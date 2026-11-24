//! Packets use virtual time. A crash discards the engine and reopens the shipped WAL.
use std::{
    collections::{BTreeMap, VecDeque},
    fs,
    io::{self, Write},
    sync::Arc,
    time::Duration,
};

use bytes::Bytes;
use journal_contract::BoxFuture;
use parking_lot::Mutex;
use tempfile::TempDir;

use super::super::{Allow, CallResult, Engine, Limits, Work};
use crate::stream::wire::*;

pub(super) const ENSEMBLE: [KeeperId; 3] = [KeeperId(1), KeeperId(2), KeeperId(3)];
pub(super) const LEARNER: KeeperId = KeeperId(4);

#[derive(Clone, Copy, Debug)]
pub(super) enum Fault {
    RequestLoss,
    ReplyLoss,
    Duplicate,
    Delay(u64),
    Partition,
    CrashBefore,
    LoseUnsynced,
    Tear,
    CrashAfterSync,
}

impl Fault {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::RequestLoss => "request loss",
            Self::ReplyLoss => "reply loss",
            Self::Duplicate => "duplication",
            Self::Delay(_) => "delay",
            Self::Partition => "partition",
            Self::CrashBefore => "crash before WAL write",
            Self::LoseUnsynced => "lost unsynced write",
            Self::Tear => "torn WAL write",
            Self::CrashAfterSync => "crash after WAL sync",
        }
    }
}

pub(super) type Coverage = BTreeMap<&'static str, usize>;

pub(super) struct Network {
    state: Mutex<State>,
    limits: Limits,
    root: TempDir,
}

struct State {
    nodes: [Option<Engine>; 4],
    isolated: Option<KeeperId>,
    lost: Option<KeeperId>,
    fault: Option<(KeeperId, Fault)>,
    random: u64,
    sent: u64,
    newest: u64,
    coverage: Coverage,
    trace: Option<Trace>,
}

/// Every keeper effect with its durable images, for Lean's reference replay.
#[derive(Default)]
struct Trace {
    rows: Vec<String>,
    identities: Vec<Identity>,
    /// The durable images of a crashed keeper, compared with its reopened images.
    durable: [Option<BTreeMap<StreamId, String>>; 4],
}

struct Client {
    network: Arc<Network>,
    identity: Identity,
}

impl Network {
    pub(super) fn new(seed: u64, limits: Limits) -> Arc<Self> {
        let mut network = Self {
            root: tempfile::tempdir().unwrap(),
            limits,
            state: Mutex::new(State {
                nodes: [None, None, None, None],
                isolated: None,
                lost: None,
                fault: None,
                random: seed,
                sent: 0,
                newest: 0,
                coverage: Coverage::new(),
                trace: None,
            }),
        };
        let [first, second, third] = ENSEMBLE.map(|keeper| Some(network.open(keeper)));
        network.state.get_mut().nodes = [first, second, third, None];
        Arc::new(network)
    }

    fn open(&self, keeper: KeeperId) -> Engine {
        Engine::open(
            &self.root.path().join(keeper.0.to_string()),
            keeper,
            self.limits,
            Arc::new(Allow),
        )
        .unwrap()
    }

    pub(super) fn client(self: &Arc<Self>, identity: &Identity) -> Arc<dyn Transport> {
        Arc::new(Client {
            network: self.clone(),
            identity: identity.clone(),
        })
    }

    pub(super) fn arm(&self, keeper: KeeperId, fault: Fault) {
        let mut state = self.state.lock();
        assert!(state.fault.replace((keeper, fault)).is_none());
        if matches!(fault, Fault::Partition) {
            assert!(state.isolated.replace(keeper).is_none());
        }
    }

    pub(super) fn isolate(&self, keeper: Option<KeeperId>) {
        self.state.lock().isolated = keeper;
    }

    pub(super) fn lose_disk(&self, keeper: KeeperId) {
        let mut state = self.state.lock();
        assert!(
            state.lost.replace(keeper).is_none(),
            "one disk loss per run"
        );
        state.nodes[slot(keeper)] = None;
        if let Some(trace) = &mut state.trace {
            trace.durable[slot(keeper)] = None;
        }
        fs::remove_dir_all(self.root.path().join(keeper.0.to_string())).unwrap();
        state.nodes[slot(LEARNER)] = Some(self.open(LEARNER));
        state.hit("disk loss");
    }

    pub(super) fn restart_survivors(&self) {
        let mut state = self.state.lock();
        for keeper in ENSEMBLE {
            if state.lost == Some(keeper) {
                continue;
            }
            let state = &mut *state;
            let running = state.nodes[slot(keeper)].take();
            let before = state.trace.as_mut().map(|trace| match &running {
                Some(running) => trace.images(running),
                None => trace.durable[slot(keeper)].take().unwrap_or_default(),
            });
            drop(running);
            let engine = self.open(keeper);
            if let (Some(trace), Some(before)) = (&mut state.trace, before) {
                let after = trace.images(&engine);
                for stream in before.keys().chain(after.keys()).collect::<std::collections::BTreeSet<_>>() {
                    let image = |images: &BTreeMap<StreamId, String>| {
                        images.get(stream).cloned().unwrap_or_else(|| trace_image(None, &mut Vec::new()))
                    };
                    let row = format!("reopen 0 {} 0 {} {}", keeper.0, image(&before), image(&after));
                    trace.rows.push(row);
                }
            }
            state.nodes[slot(keeper)] = Some(engine);
            state.hit("reopened WAL");
        }
    }

    pub(super) fn hit(&self, name: &'static str) {
        self.state.lock().hit(name);
    }

    pub(super) fn coverage(&self) -> Coverage {
        self.state.lock().coverage.clone()
    }

    pub(super) fn record_trace(&self) {
        self.state.lock().trace = Some(Trace::default());
    }

    pub(super) fn write_trace(&self, seed: u64, out: &mut impl Write) -> io::Result<()> {
        writeln!(out, "seed {seed}")?;
        for row in self.state.lock().trace.take().unwrap().rows {
            writeln!(out, "{row}")?;
        }
        Ok(())
    }

    /// Read the payload from the actual keeper state or extent, even before its
    /// commit watermark has been published. Never send these probes to a writer.
    pub(super) fn copies(
        &self,
        keepers: &[KeeperId],
        stream: StreamId,
        at: Lsn,
        payload: &Bytes,
        committed: bool,
    ) -> usize {
        let mut state = self.state.lock();
        keepers
            .iter()
            .filter(|&&keeper| {
                let Some(node) = &mut state.nodes[slot(keeper)] else {
                    return false;
                };
                let Some(stream) = node.streams.get(&stream) else {
                    return false;
                };
                if stream.deleted || at < stream.view.floor {
                    return false;
                }
                let through = if committed {
                    stream.view.head
                } else {
                    stream.view.tail
                };
                matches!(
                    stream.page(at, 1, through, &mut node.wal.reader).unwrap(),
                    Reply::Records { records, .. } if records == [(at, payload.clone())]
                )
            })
            .count()
    }

    fn deliver(&self, packet: &Packet) -> CallResult {
        let mut state = self.state.lock();
        let Packet {
            serial,
            keeper,
            identity,
            request,
            fault,
            ..
        } = packet;
        if *serial < state.newest {
            state.hit("reordering");
        }
        state.newest = state.newest.max(*serial);
        if state.isolated == Some(*keeper) || state.lost == Some(*keeper) {
            return Err(TransportError::Unreachable);
        }
        let state = &mut *state;
        let node = &mut state.nodes[slot(*keeper)];
        if matches!(fault, Some(Fault::CrashBefore)) {
            if let (Some(trace), Some(engine)) = (&mut state.trace, node.as_ref()) {
                trace.durable[slot(*keeper)] = Some(trace.images(engine));
            }
            *node = None;
            *state.coverage.entry("crashed").or_default() += 1;
            return Err(TransportError::Unreachable);
        }
        let Some(engine) = node else {
            return Err(TransportError::Unreachable);
        };
        let stream = crate::stream::codec::stream(request);
        let before = state.trace.as_mut().map(|trace| {
            let caller = trace.identity(identity);
            (caller, trace.images(engine))
        });
        engine.wal.retain_unsynced = match fault {
            Some(Fault::LoseUnsynced) => Some(0),
            Some(Fault::Tear) => Some(packet.cut),
            _ => None,
        };
        let (done, mut result) = tokio::sync::oneshot::channel();
        let work = Work {
            identity: identity.clone(),
            request: request.clone(),
            done,
            pending: None,
        };
        let rounds = engine.wal.rounds.len();
        let outcome = engine.process(VecDeque::from([work]));
        let mut record = |reply: Option<&CallResult>, engine: &Engine| {
            if let (Some(trace), Some((caller, before))) = (&mut state.trace, &before) {
                let after = trace.images(engine);
                let image = |images: &BTreeMap<StreamId, String>| {
                    images.get(&stream).cloned().unwrap_or_else(|| trace_image(None, &mut Vec::new()))
                };
                let (before, after) = (image(before), image(&after));
                let row = trace_row(packet, *caller, &before, &after, request, reply, &mut trace.identities);
                trace.rows.push(row);
            }
        };
        match outcome {
            Ok(()) if matches!(fault, Some(Fault::CrashAfterSync)) => {
                assert!(engine.wal.rounds.len() > rounds, "crash missed WAL sync");
                record(None, engine);
                if let Some(trace) = &mut state.trace {
                    trace.durable[slot(*keeper)] = Some(trace.images(engine));
                }
                state.nodes[slot(*keeper)] = None;
                *state.coverage.entry("crashed").or_default() += 1;
                Err(TransportError::Unreachable)
            }
            Ok(()) => {
                let reply = result.try_recv().expect("keeper must finish work").0;
                record(Some(&reply), engine);
                if matches!(request, Request::Append { head, .. } if head.0 != 0)
                    && matches!(reply, Ok(Reply::Appended { .. }))
                {
                    state.hit("head publication");
                }
                reply
            }
            Err(error) if is_cut(&error) => {
                assert!(
                    result.try_recv().is_err(),
                    "durability: a success reply escaped a failed WAL sync"
                );
                if let (Some(trace), Some((_, before))) = (&mut state.trace, before) {
                    trace.durable[slot(*keeper)] = Some(before);
                }
                state.nodes[slot(*keeper)] = None;
                state.hit("crashed");
                Err(TransportError::Unreachable)
            }
            Err(error) => panic!("unexpected keeper I/O error: {error}"),
        }
    }
}

fn is_cut(error: &io::Error) -> bool {
    error.to_string() == "simulated crash before WAL sync"
}

impl State {
    fn hit(&mut self, name: &'static str) {
        *self.coverage.entry(name).or_default() += 1;
    }
}

struct Packet {
    serial: u64,
    keeper: KeeperId,
    request: Request,
    identity: Identity,
    fault: Option<Fault>,
    cut: usize,
}

impl Trace {
    fn identity(&mut self, identity: &Identity) -> usize {
        match self.identities.iter().position(|known| known == identity) {
            Some(index) => index + 1,
            None => {
                self.identities.push(identity.clone());
                self.identities.len()
            }
        }
    }

    fn images(&mut self, engine: &Engine) -> BTreeMap<StreamId, String> {
        engine
            .streams
            .iter()
            .map(|(id, stream)| (*id, trace_image(Some(stream), &mut self.identities)))
            .collect()
    }
}

fn trace_runs(row: &mut String, runs: &[EpochRun]) {
    use std::fmt::Write;
    write!(row, " {}", runs.len()).unwrap();
    for run in runs {
        write!(row, " {} {} {}", run.epoch.0, run.first.0, run.last.0).unwrap();
    }
}

fn trace_view(row: &mut String, view: &StreamView, identities: &mut Vec<Identity>) {
    use std::fmt::Write;
    let (promised, owner) = view.promised.as_ref().map_or((0, 0), |(epoch, owner)| {
        let index = match identities.iter().position(|known| known == owner) {
            Some(index) => index + 1,
            None => {
                identities.push(owner.clone());
                identities.len()
            }
        };
        (u128::from(epoch.0) + 1, index)
    });
    write!(
        row,
        " {promised} {owner} {} {} {} {} {} {} {} {}",
        view.synced.map_or(0, |epoch| u128::from(epoch.0) + 1),
        view.floor.0,
        view.tail.0,
        view.head.0,
        u8::from(view.learner),
        view.ensemble[0].0,
        view.ensemble[1].0,
        view.ensemble[2].0,
    )
    .unwrap();
    trace_runs(row, &view.runs);
}

/// `exists deleted` then the view, then `0` or `1 floor from tail runs` for a staged Sync.
fn trace_image(stream: Option<&super::super::state::Stream>, identities: &mut Vec<Identity>) -> String {
    use std::fmt::Write;
    let Some(stream) = stream else {
        return "0 0 0 0 0 1 0 0 1 0 0 0 0 0".into();
    };
    let mut row = format!("1 {}", u8::from(stream.deleted));
    trace_view(&mut row, &stream.view, identities);
    match &stream.staging {
        None => row.push_str(" 0"),
        Some(staging) => {
            write!(row, " 1 {} {} {}", staging.floor.0, staging.from.0, staging.tail().0).unwrap();
            let mut runs: Vec<EpochRun> = Vec::new();
            for (index, record) in staging.records.iter().enumerate() {
                let lsn = Lsn(staging.from.0 + index as u64);
                match runs.last_mut() {
                    Some(run) if run.epoch == record.epoch => run.last = lsn,
                    _ => runs.push(EpochRun {
                        epoch: record.epoch,
                        first: lsn,
                        last: lsn,
                    }),
                }
            }
            trace_runs(&mut row, &runs);
        }
    }
    row
}

/// `verb serial keeper caller before after request-fields reply-tag reply-fields`.
fn trace_row(
    packet: &Packet,
    caller: usize,
    before: &str,
    after: &str,
    request: &Request,
    reply: Option<&CallResult>,
    identities: &mut Vec<Identity>,
) -> String {
    use std::fmt::Write;
    let ensemble = |e: &[KeeperId; 3]| format!("{} {} {}", e[0].0, e[1].0, e[2].0);
    let (verb, fields) = match request {
        Request::Create { ensemble: e, .. } => ("create", ensemble(e)),
        Request::Seal { epoch, ensemble: e, .. } => ("seal", format!("{} {}", epoch.0, ensemble(e))),
        Request::Sync { epoch, floor, from, records, runs, head, complete, .. } => {
            let mut fields = format!(
                "{} {} {} {} {} {}",
                epoch.0, floor.0, from.0, records.len(), head.0, u8::from(*complete)
            );
            trace_runs(&mut fields, runs);
            ("sync", fields)
        }
        Request::Append { epoch, at, records, head, .. } => (
            "append",
            format!("{} {} {} {}", epoch.0, at.0, records.len(), head.0),
        ),
        Request::Trim { epoch, through, .. } => ("trim", format!("{} {}", epoch.0, through.0)),
        Request::Check { epoch, .. } => ("check", format!("{}", epoch.0)),
        Request::Recover { epoch, from, max, .. } => {
            ("recover", format!("{} {} {}", epoch.0, from.0, max))
        }
        Request::Read { from, max, .. } => ("read", format!("{} {}", from.0, max)),
        Request::Delete { ensemble: e, .. } => ("delete", ensemble(e)),
        Request::Replace { epoch, from, to, .. } => (
            "replace",
            format!("{} {} {}", epoch.0, ensemble(from), ensemble(to)),
        ),
        Request::Batch(_) => unreachable!("the simulator delivers single requests"),
    };
    let mut row = format!(
        "{verb} {} {} {caller} {before} {after} {fields}",
        packet.serial, packet.keeper.0
    );
    match reply {
        None => row.push_str(" 10"),
        Some(Err(_)) => row.push_str(" 11"),
        Some(Ok(reply)) => match reply {
            Reply::Refused(_) => row.push_str(" 0"),
            Reply::Created => row.push_str(" 1"),
            Reply::Sealed(view) => {
                row.push_str(" 2");
                trace_view(&mut row, view, identities);
            }
            Reply::Synced { tail } => write!(row, " 3 {}", tail.0).unwrap(),
            Reply::Appended { tail } => write!(row, " 4 {}", tail.0).unwrap(),
            Reply::Trimmed { floor } => write!(row, " 5 {}", floor.0).unwrap(),
            Reply::Checked(view) => {
                row.push_str(" 6");
                trace_view(&mut row, view, identities);
            }
            Reply::Records { floor, records, head } => {
                write!(row, " 7 {} {} {}", floor.0, head.0, records.len()).unwrap();
                for (lsn, _) in records {
                    write!(row, " {}", lsn.0).unwrap();
                }
            }
            Reply::Deleted => row.push_str(" 8"),
            Reply::Replaced => row.push_str(" 9"),
            Reply::Batch(_) => unreachable!("the simulator delivers single requests"),
        },
    }
    row
}

impl Transport for Client {
    fn identity(&self) -> &Identity {
        &self.identity
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        Box::pin(async move {
            let network = self.network.clone();
            let (mut packet, delivery, response) = {
                let mut state = network.state.lock();
                state.sent += 1;
                let fault = if state.fault.is_some_and(|(target, _)| target == keeper)
                    && matches!(&request, Request::Append { records, .. } if !records.is_empty())
                {
                    let fault = state.fault.take().unwrap().1;
                    state.hit(fault.name());
                    Some(fault)
                } else {
                    None
                };
                let jitter = random(&mut state.random);
                (
                    Packet {
                        serial: state.sent,
                        keeper,
                        request,
                        identity: self.identity.clone(),
                        fault,
                        cut: 1 + (jitter % 120) as usize,
                    },
                    1 + jitter % 7,
                    1 + (jitter >> 8) % 7,
                )
            };
            let (done, reply) = tokio::sync::oneshot::channel();
            // A caller that drops its future cannot recall a transmitted packet.
            tokio::spawn(async move {
                let extra = match packet.fault {
                    Some(Fault::Delay(milliseconds)) => milliseconds,
                    _ => 0,
                };
                sleep(delivery + extra).await;
                if matches!(packet.fault, Some(Fault::RequestLoss)) {
                    let _ = done.send(Err(TransportError::TimedOut));
                    return;
                }
                let result = network.deliver(&packet);
                sleep(response).await;
                let reply = if matches!(packet.fault, Some(Fault::ReplyLoss)) {
                    Err(TransportError::TimedOut)
                } else {
                    result
                };
                let _ = done.send(reply);
                if matches!(packet.fault, Some(Fault::Duplicate)) {
                    sleep(9).await;
                    packet.fault = None;
                    let _ = network.deliver(&packet);
                    network.hit("duplicate delivered");
                }
            });
            reply.await.unwrap()
        })
    }
}

fn slot(keeper: KeeperId) -> usize {
    keeper.0 as usize - 1
}

pub(super) async fn sleep(ms: u64) {
    tokio::time::sleep(Duration::from_millis(ms)).await;
}

pub(super) fn random(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9e3779b97f4a7c15);
    let mut bits = *seed;
    bits = (bits ^ (bits >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    bits = (bits ^ (bits >> 27)).wrapping_mul(0x94d049bb133111eb);
    bits ^ (bits >> 31)
}
