//! In-memory transport and deterministic fault gates around the real keeper reducer.

use std::{collections::BTreeMap, sync::Arc, time::Duration};

use journal_contract::{BoxFuture, Identity, StreamId};
use parking_lot::Mutex;
use tokio::sync::{Semaphore, watch};

use crate::stream::{
    keeper::{Limits, memory::Memory},
    wire::{KeeperId, Reply, Request, StreamView, Transport, TransportError},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Kind {
    Create,
    Seal,
    Sync,
    Recover,
    Replace,
    Append,
    Publish,
    Trim,
    Check,
    Poll,
    Read,
    Delete,
}

impl Kind {
    fn of(request: &Request) -> Self {
        match request {
            Request::Create { .. } => Self::Create,
            Request::Seal { .. } => Self::Seal,
            Request::Sync { .. } => Self::Sync,
            Request::Recover { .. } => Self::Recover,
            Request::Replace { .. } => Self::Replace,
            Request::Append { records, .. } if records.is_empty() => Self::Publish,
            Request::Append { .. } => Self::Append,
            Request::Trim { .. } => Self::Trim,
            Request::Check { .. } => Self::Check,
            Request::Read { wait_ms, .. } if *wait_ms > 0 => Self::Poll,
            Request::Read { .. } => Self::Read,
            Request::Delete { .. } => Self::Delete,
            Request::Batch(_) => unreachable!("the writer issues single requests"),
        }
    }
}

pub(super) const KEEPERS: [KeeperId; 4] = [KeeperId(1), KeeperId(2), KeeperId(3), KeeperId(4)];

#[derive(Clone)]
pub(super) enum Fault {
    LoseReply,
    DelayRequest(Arc<Gate>),
    HoldReply(Arc<Gate>),
}

pub(super) struct Gate {
    reached: Semaphore,
    released: Semaphore,
}

impl Gate {
    pub(super) fn new() -> Arc<Self> {
        Arc::new(Self {
            reached: Semaphore::new(0),
            released: Semaphore::new(0),
        })
    }

    pub(super) async fn reached(&self) {
        self.reached.acquire().await.unwrap().forget();
    }

    pub(super) fn release(&self) {
        self.released.add_permits(1);
    }
}

pub(super) struct Network {
    state: Mutex<State>,
    change: watch::Sender<()>,
    limits: Limits,
}

struct State {
    keepers: Vec<Memory>,
    down: [bool; 4],
    faults: BTreeMap<(KeeperId, Kind), Fault>,
    calls: Vec<(KeeperId, Kind)>,
}

pub(super) struct Client {
    network: Arc<Network>,
    identity: Identity,
}

impl Default for Network {
    fn default() -> Self {
        Self::new(4, 64, 192)
    }
}

impl Network {
    pub(super) fn new(keepers: usize, max_record_bytes: u32, stream_quota_bytes: u64) -> Self {
        Self {
            state: Mutex::new(State {
                keepers: (0..keepers).map(|_| Memory::default()).collect(),
                down: [false; 4],
                faults: BTreeMap::new(),
                calls: Vec::new(),
            }),
            change: watch::channel(()).0,
            limits: Limits {
                max_record_bytes,
                stream_quota_bytes,
                ..Limits::default()
            },
        }
    }

    pub(super) fn client(self: &Arc<Self>, id: u128) -> Arc<Client> {
        self.connect(Identity::from(format!("urn:logkeeper:client:{id}")))
    }

    pub(super) fn connect(self: &Arc<Self>, identity: Identity) -> Arc<Client> {
        Arc::new(Client {
            network: self.clone(),
            identity,
        })
    }

    pub(super) fn down(&self, keeper: KeeperId, down: bool) {
        self.state.lock().down[slot(keeper)] = down;
    }

    pub(super) fn fault(&self, keeper: KeeperId, kind: Kind, fault: Fault) {
        self.state.lock().faults.insert((keeper, kind), fault);
    }

    pub(super) fn calls(&self, kind: Kind) -> Vec<KeeperId> {
        self.state
            .lock()
            .calls
            .iter()
            .filter_map(|&(keeper, seen)| (kind == seen).then_some(keeper))
            .collect()
    }

    pub(super) fn view(&self, keeper: KeeperId, stream: StreamId) -> Option<StreamView> {
        self.state.lock().keepers[slot(keeper)]
            .view(stream)
            .cloned()
    }

    pub(super) async fn until(&self, predicate: impl Fn() -> bool) {
        let mut change = self.change.subscribe();
        tokio::time::timeout(Duration::from_secs(1), async {
            while !predicate() {
                change.changed().await.unwrap();
            }
        })
        .await
        .expect("keeper witness was unreachable");
    }
}

impl Transport for Client {
    fn identity(&self) -> &Identity {
        &self.identity
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, Result<Reply, TransportError>> {
        Box::pin(async move {
            let network = &self.network;
            let kind = Kind::of(&request);
            let mut change = network.change.subscribe();
            let apply = |state: &mut State| {
                state.keepers[slot(keeper)].call(
                    keeper,
                    &self.identity,
                    request.clone(),
                    &network.limits,
                )
            };
            let (mut reply, fault) = {
                let mut state = network.state.lock();
                state.calls.push((keeper, kind));
                if state.down[slot(keeper)] {
                    return Err(TransportError::Unreachable);
                }
                let fault = state.faults.remove(&(keeper, kind));
                if let Some(Fault::DelayRequest(gate)) = fault {
                    let network = Arc::clone(network);
                    let identity = self.identity.clone();
                    tokio::spawn(async move {
                        gate.reached.add_permits(1);
                        gate.released.acquire().await.unwrap().forget();
                        let mut state = network.state.lock();
                        state.keepers[slot(keeper)].call(
                            keeper,
                            &identity,
                            request,
                            &network.limits,
                        );
                        network.change.send_replace(());
                    });
                    return Err(TransportError::TimedOut);
                }
                (apply(&mut state), fault)
            };
            if let Request::Read {
                from, wait_ms, max, ..
            } = request
            {
                if wait_ms > 0 && max != 0 {
                    let deadline =
                        tokio::time::Instant::now() + Duration::from_millis(wait_ms.into());
                    while matches!(reply, Reply::Records { head, .. } if head < from) {
                        let woke = tokio::time::timeout_at(deadline, change.changed())
                            .await
                            .is_ok();
                        reply = apply(&mut network.state.lock());
                        if !woke {
                            break;
                        }
                    }
                }
            } else if !matches!(kind, Kind::Check | Kind::Recover) {
                network.change.send_replace(());
            }
            match fault {
                Some(Fault::LoseReply) => Err(TransportError::TimedOut),
                Some(Fault::DelayRequest(_)) => unreachable!("delayed before delivery"),
                Some(Fault::HoldReply(gate)) => {
                    gate.reached.add_permits(1);
                    gate.released.acquire().await.unwrap().forget();
                    Ok(reply)
                }
                None => Ok(reply),
            }
        })
    }
}

fn slot(keeper: KeeperId) -> usize {
    usize::try_from(keeper.0).unwrap() - 1
}
