mod reading;

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::Arc,
    time::Duration,
};

use bytes::Bytes;
use futures::stream::{FuturesUnordered, StreamExt};
use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};
use parking_lot::Mutex;
use tokio::time::{Instant, sleep};

use super::{
    ALPN, Configuration, Credentials, Fence, Genesis, KeeperStatus, Keepers, MAX_RECORD, Sealed,
    invalid,
    network::{Frame, Lane, Reply, Request, Rpc},
    state::Outcome,
};

const ATTEMPT: Duration = Duration::from_millis(1200);
const ROUTE_FANOUT: usize = 16;

/// A journal client with authenticated, cached routes. An ordinary append and
/// head use the stream leader directly after discovery.
#[derive(Clone)]
pub struct Client {
    rpc: Rpc,
    catalog: uuid::Uuid,
    deadline: Duration,
    routes: Arc<Mutex<BTreeMap<StreamId, Route>>>,
}

#[derive(Clone)]
struct Route {
    genesis: Option<Genesis>,
    preferred: Option<(Configuration, uuid::Uuid)>,
    contacts: Vec<uuid::Uuid>,
    leader: Option<uuid::Uuid>,
}

impl Client {
    pub fn new(
        credentials: &Credentials,
        keepers: Keepers,
        catalog: uuid::Uuid,
        deadline: Duration,
    ) -> io::Result<Self> {
        if !keepers.contains_key(&catalog) || deadline.is_zero() {
            return Err(invalid("invalid catalog address or client deadline"));
        }
        let (tls, _) = credentials.client_protocol(ALPN)?;
        Ok(Self {
            rpc: Rpc::new(tls, keepers, Lane::Application),
            catalog,
            deadline,
            routes: Arc::default(),
        })
    }

    /// Assigns and initializes a stream's unique genesis. Use the same ID, voter
    /// set, and quota when retrying an uncertain create.
    pub async fn create(
        &self,
        stream: StreamId,
        mut voters: [uuid::Uuid; 3],
        quota_bytes: u64,
    ) -> Result<()> {
        voters.sort_unstable();
        let genesis = Genesis {
            stream,
            voters,
            quota_bytes,
        };
        if !genesis.valid(self.rpc.keepers()) {
            return Err(JournalError::Unavailable);
        }
        let end = Instant::now() + self.deadline;
        let reply: Reply = self
            .rpc
            .call(
                self.catalog,
                Frame::Client(Request::Claim(genesis)),
                self.deadline,
            )
            .await
            .map_err(|_| JournalError::Unavailable)?;
        self.install_route(stream, reply)?;
        let bootstrap = async {
            let mut calls =
                FuturesUnordered::from_iter(voters.into_iter().map(|keeper| async move {
                    while !remaining(end).is_zero() {
                        if matches!(
                            self.rpc
                                .call::<Reply>(
                                    keeper,
                                    Frame::Client(Request::Bootstrap(stream)),
                                    remaining(end).min(ATTEMPT),
                                )
                                .await,
                            Ok(Reply::Decision(Outcome::Unit))
                        ) {
                            break;
                        }
                        sleep(Duration::from_millis(25).min(remaining(end))).await;
                    }
                }));
            while calls.next().await.is_some() {}
            std::future::pending::<Result<Outcome>>().await
        };
        let outcome = tokio::select! {
            result = self.decide(Request::Create(stream), end, ATTEMPT) => result?,
            result = bootstrap => result?,
        };
        unit(outcome)
    }

    pub async fn seal(
        &self,
        stream: StreamId,
        expected: Epoch,
        writer: uuid::Uuid,
    ) -> Result<Sealed> {
        if writer.is_nil() {
            return Err(JournalError::Unavailable);
        }
        match self
            .operation(Request::Seal {
                stream,
                expected,
                writer,
            })
            .await?
        {
            Outcome::Sealed(sealed) => Ok(sealed),
            _ => Err(JournalError::Unavailable),
        }
    }

    pub async fn append(
        &self,
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payload: Bytes,
    ) -> Result<Lsn> {
        if payload.len() > MAX_RECORD {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        position(
            self.operation(Request::Append {
                stream,
                fence,
                at,
                payload,
            })
            .await?,
        )
    }

    /// Appends a contiguous group from `at` in one committed entry and
    /// returns its last LSN. The keeper applies the whole group or none of
    /// it. Use at most 256 records and 4 MiB of payload per call.
    pub async fn append_batch(
        &self,
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payloads: Vec<Bytes>,
    ) -> Result<Lsn> {
        if !super::state::valid_batch(&payloads) {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        position(
            self.operation(Request::AppendBatch {
                stream,
                fence,
                at,
                payloads,
            })
            .await?,
        )
    }

    pub async fn head(&self, stream: StreamId) -> Result<Lsn> {
        position(self.operation(Request::Head(stream)).await?)
    }

    pub async fn trim(&self, stream: StreamId, fence: Fence, through: Lsn) -> Result<()> {
        unit(
            self.operation(Request::Trim {
                stream,
                fence,
                through,
            })
            .await?,
        )
    }

    pub async fn delete(&self, stream: StreamId) -> Result<()> {
        unit(self.operation(Request::Delete(stream)).await?)
    }

    /// Stages a timed original on one signing voter and returns its signed
    /// sync sample. Stage on the first two voters of the sorted roster.
    pub(super) async fn stage_original(
        &self,
        keeper: uuid::Uuid,
        stream: StreamId,
        revision: u64,
        original: crate::stream::timed::TimedOriginal,
        payload: Bytes,
    ) -> Result<crate::stream::timed::TimedSample> {
        let request = Request::StageOriginal {
            stream,
            revision,
            original: original.encode().to_vec(),
            payload,
        };
        match self.keeper_operation(keeper, request).await? {
            Reply::Decision(outcome) => match decision(outcome)? {
                Outcome::OriginalSample(sample) => {
                    crate::stream::timed::TimedSample::decode(&sample)
                        .ok_or(JournalError::Unavailable)
                }
                _ => Err(JournalError::Unavailable),
            },
            _ => Err(JournalError::Unavailable),
        }
    }

    /// Appends a timed original with the evidence of its two signing voters.
    pub(super) async fn append_original(
        &self,
        stream: StreamId,
        fence: Fence,
        evidence: &crate::stream::timed::TimedEvidence,
        payload: Bytes,
    ) -> Result<Lsn> {
        position(
            self.operation(Request::AppendOriginal {
                stream,
                fence,
                evidence: evidence.encode().to_vec(),
                payload,
            })
            .await?,
        )
    }

    /// The retained evidence of the timed record at `at`.
    pub(super) async fn prove_original(
        &self,
        stream: StreamId,
        at: Lsn,
    ) -> Result<crate::stream::timed::TimedEvidence> {
        match self
            .operation(Request::ProveOriginal { stream, at })
            .await?
        {
            Outcome::OriginalEvidence(evidence) => {
                crate::stream::timed::TimedEvidence::decode(&evidence)
                    .ok_or(JournalError::Unavailable)
            }
            _ => Err(JournalError::Unavailable),
        }
    }

    /// Reads the local generation to use in a conditional retirement.
    pub async fn replica_generation(&self, stream: StreamId, keeper: uuid::Uuid) -> Result<u64> {
        match self
            .keeper_operation(keeper, Request::LocalCopy(stream))
            .await?
        {
            Reply::Generation(generation) => Ok(generation),
            Reply::Decision(Outcome::Refused(error)) => Err(error),
            _ => Err(JournalError::Unavailable),
        }
    }

    /// Retires one exact local copy after its keeper verifies fresh exclusion
    /// with the current placement authority.
    pub async fn retire_copy(
        &self,
        stream: StreamId,
        keeper: uuid::Uuid,
        authority: uuid::Uuid,
        revision: u64,
        generation: u64,
    ) -> Result<()> {
        match self
            .keeper_operation(
                keeper,
                Request::RetireCopy {
                    stream,
                    authority,
                    revision,
                    generation,
                },
            )
            .await?
        {
            Reply::Decision(outcome) => unit(decision(outcome)?),
            _ => Err(JournalError::Unavailable),
        }
    }

    /// The status `keeper` reports about itself and its replica of `stream`.
    pub async fn keeper_status(
        &self,
        keeper: uuid::Uuid,
        stream: StreamId,
    ) -> Result<KeeperStatus> {
        match self
            .keeper_operation(keeper, Request::KeeperStatus(stream))
            .await?
        {
            Reply::Status(status) if status.keeper == keeper => Ok(status),
            _ => Err(JournalError::Unavailable),
        }
    }

    /// The voters the catalog assigned to `stream`, or `None` when the
    /// catalog has none.
    pub(super) async fn claimed_voters(&self, stream: StreamId) -> Result<Option<[uuid::Uuid; 3]>> {
        let end = Instant::now() + self.deadline;
        match self.refresh(stream, end).await {
            Ok(route) => Ok(route.genesis.map(|genesis| genesis.voters)),
            Err(JournalError::NotFound) => Ok(None),
            Err(error) => Err(error),
        }
    }

    async fn keeper_operation(&self, keeper: uuid::Uuid, request: Request) -> Result<Reply> {
        let deadline = Instant::now() + self.deadline;
        // Drop any old pooled channels before opening a fresh one after a restart.
        for _ in 0..5 {
            let budget = remaining(deadline).min(ATTEMPT);
            if budget.is_zero() {
                break;
            }
            if let Ok(reply) = self
                .rpc
                .call(keeper, Frame::Client(request.clone()), budget)
                .await
            {
                return Ok(reply);
            }
        }
        Err(JournalError::Unavailable)
    }

    /// Reads the finalized configuration through the stream's leader.
    pub async fn configuration(&self, stream: StreamId) -> Result<Configuration> {
        configuration(self.operation(Request::Configuration(stream)).await?)
    }

    /// Replaces the voters at the expected finalized revision. Retry with the
    /// same revision and target after uncertainty. Once a later replacement
    /// finalizes, an older revision conflicts.
    pub async fn replace(
        &self,
        stream: StreamId,
        expected: u64,
        mut voters: [uuid::Uuid; 3],
    ) -> Result<Configuration> {
        voters.sort_unstable();
        configuration(
            self.operation(Request::Replace {
                stream,
                expected,
                voters,
            })
            .await?,
        )
    }

    async fn operation(&self, request: Request) -> Result<Outcome> {
        self.decide(request, Instant::now() + self.deadline, ATTEMPT)
            .await
    }

    async fn decide(&self, request: Request, end: Instant, attempt: Duration) -> Result<Outcome> {
        let stream = request.stream();
        let mut route = self.route(stream, end).await?;
        while !remaining(end).is_zero() {
            let mut visited = BTreeSet::new();
            let mut contacts = route.contacts.iter().copied();
            let mut preferred = route.leader;
            let call = |keeper| {
                let request = request.clone();
                async move {
                    let reply = self
                        .rpc
                        .call::<Reply>(keeper, Frame::Client(request), remaining(end).min(attempt))
                        .await;
                    (keeper, reply)
                }
            };
            while !remaining(end).is_zero() {
                let mut calls = FuturesUnordered::new();
                if let Some(leader) = preferred.take()
                    && visited.insert(leader)
                {
                    calls.push(call(leader));
                } else {
                    for keeper in contacts
                        .by_ref()
                        .filter(|id| visited.insert(*id))
                        .take(ROUTE_FANOUT)
                    {
                        calls.push(call(keeper));
                    }
                }
                if calls.is_empty() {
                    break;
                }
                while let Some((keeper, reply)) = calls.next().await {
                    match reply {
                        Ok(Reply::Leader(Some(leader)))
                            if self.rpc.keepers().contains_key(&leader)
                                && visited.insert(leader) =>
                        {
                            calls.push(call(leader));
                        }
                        Ok(Reply::Decision(Outcome::Refused(JournalError::Unavailable))) => (),
                        Ok(Reply::Decision(outcome)) => {
                            self.routes
                                .lock()
                                .entry(stream)
                                .or_insert_with(|| route.clone())
                                .leader = Some(keeper);
                            return decision(outcome);
                        }
                        _ => (),
                    }
                }
            }
            sleep(Duration::from_millis(25).min(remaining(end))).await;
            route = self.resolve(stream, end).await?;
            route.leader = None;
        }
        Err(JournalError::Unavailable)
    }

    async fn route(&self, stream: StreamId, end: Instant) -> Result<Route> {
        let cached = self.routes.lock().get(&stream).cloned();
        match cached {
            Some(route) => Ok(route),
            None => self.resolve(stream, end).await,
        }
    }

    async fn resolve(&self, stream: StreamId, end: Instant) -> Result<Route> {
        match self.refresh(stream, end).await {
            Err(JournalError::Unavailable) => Ok(Route {
                genesis: None,
                preferred: None,
                contacts: self.rpc.keepers().keys().copied().collect(),
                leader: None,
            }),
            result => result,
        }
    }

    async fn refresh(&self, stream: StreamId, end: Instant) -> Result<Route> {
        let reply = self
            .rpc
            .call(
                self.catalog,
                Frame::Client(Request::Locate(stream)),
                (remaining(end) / 4).min(ATTEMPT),
            )
            .await
            .map_err(|_| JournalError::Unavailable)?;
        self.install_route(stream, reply)
    }

    fn install_route(&self, stream: StreamId, reply: Reply) -> Result<Route> {
        match reply {
            Reply::Catalog(genesis, contacts)
                if genesis.stream == stream && genesis.valid(self.rpc.keepers()) =>
            {
                let mut routes = self.routes.lock();
                let route = routes.entry(stream).or_insert_with(|| Route {
                    genesis: Some(genesis.clone()),
                    contacts: Vec::new(),
                    leader: None,
                    preferred: None,
                });
                if route
                    .genesis
                    .as_ref()
                    .is_some_and(|known| known != &genesis)
                {
                    return Err(JournalError::Unavailable);
                }
                route.genesis = Some(genesis);
                route.contacts = contacts;
                Ok(route.clone())
            }
            Reply::Decision(Outcome::Refused(error)) => Err(error),
            _ => Err(JournalError::Unavailable),
        }
    }
}

fn remaining(end: Instant) -> Duration {
    end.saturating_duration_since(Instant::now())
}

fn decision(outcome: Outcome) -> Result<Outcome> {
    match outcome {
        Outcome::Refused(error) => Err(error),
        success => Ok(success),
    }
}

fn unit(outcome: Outcome) -> Result<()> {
    match outcome {
        Outcome::Unit => Ok(()),
        _ => Err(JournalError::Unavailable),
    }
}

fn configuration(outcome: Outcome) -> Result<Configuration> {
    match outcome {
        Outcome::Configuration(configuration) => Ok(configuration),
        _ => Err(JournalError::Unavailable),
    }
}

fn position(outcome: Outcome) -> Result<Lsn> {
    match outcome {
        Outcome::At(position) => Ok(position),
        _ => Err(JournalError::Unavailable),
    }
}
