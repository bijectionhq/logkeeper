//! Packets use virtual time. A crash discards the engine and reopens the shipped WAL.
use std::{
    collections::{BTreeMap, VecDeque},
    fs, io,
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
    Delay,
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
            Self::Delay => "delay",
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
            state.nodes[slot(keeper)] = None;
            state.nodes[slot(keeper)] = Some(self.open(keeper));
            state.hit("reopened WAL");
        }
    }

    pub(super) fn hit(&self, name: &'static str) {
        self.state.lock().hit(name);
    }

    pub(super) fn coverage(&self) -> Coverage {
        self.state.lock().coverage.clone()
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
        let node = &mut state.nodes[slot(*keeper)];
        if matches!(fault, Some(Fault::CrashBefore)) {
            *node = None;
            state.hit("crashed");
            return Err(TransportError::Unreachable);
        }
        let Some(engine) = node else {
            return Err(TransportError::Unreachable);
        };
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
        match engine.process(VecDeque::from([work])) {
            Ok(()) if matches!(fault, Some(Fault::CrashAfterSync)) => {
                assert!(engine.wal.rounds.len() > rounds, "crash missed WAL sync");
                *node = None;
                state.hit("crashed");
                Err(TransportError::Unreachable)
            }
            Ok(()) => {
                let reply = result.try_recv().expect("keeper must finish work").0;
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
                *node = None;
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
                let extra = u64::from(matches!(packet.fault, Some(Fault::Delay))) * 35;
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
