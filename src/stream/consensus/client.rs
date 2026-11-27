mod reading;

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use bytes::Bytes;
use futures::stream::{FuturesUnordered, StreamExt};
use journal_contract::{Epoch, JournalError, Lsn, RecoveryFence, Result, StreamId};
use parking_lot::Mutex;
use tokio::time::{Instant, sleep};

use super::{
    Configuration, Credentials, Fence, Genesis, KeeperStatus, Keepers, MAX_RECORD, Sealed, invalid,
    network::{Lane, Reply, Request, Rpc},
    state::Outcome,
};

const ATTEMPT: Duration = Duration::from_millis(1200);
const ROUTE_FANOUT: usize = 16;
/// The longest one replicated catalog voter may take with a claim.
const CATALOG_WRITE_ATTEMPT: Duration = Duration::from_secs(3);

/// A journal client with authenticated, cached routes. An ordinary append and
/// head use the stream leader directly after discovery.
#[derive(Clone)]
pub struct Client {
    rpc: Rpc,
    catalog: uuid::Uuid,
    /// The replicated catalog's voters, which replace `catalog` when set.
    catalog_voters: Option<[uuid::Uuid; 3]>,
    /// The replicated catalog voter that last answered a claim.
    catalog_leader: Arc<Mutex<Option<uuid::Uuid>>>,
    deadline: Duration,
    routes: Arc<Mutex<BTreeMap<StreamId, Route>>>,
    /// Keepers in this client's failure domain, tried first for reads.
    local: Arc<BTreeSet<uuid::Uuid>>,
    /// Retired keeper identities that may still appear in historical stream
    /// genesis or pre-repair configurations.
    retired: Arc<BTreeSet<uuid::Uuid>>,
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
        let (tls, _) = credentials.client_protocols(Lane::Application.alpns())?;
        Ok(Self {
            rpc: Rpc::new(tls, keepers, Lane::Application),
            catalog,
            catalog_voters: None,
            catalog_leader: Arc::default(),
            deadline,
            routes: Arc::default(),
            local: Arc::default(),
            retired: Arc::default(),
        })
    }

    /// Uses the replicated catalog on `voters` instead of the single catalog
    /// keeper. Claims and lookups try them in order and follow leader hints.
    pub fn with_catalog_voters(mut self, voters: [uuid::Uuid; 3]) -> Self {
        self.catalog_voters = Some(voters);
        self
    }

    /// Reads go first to a voter among `keepers`, those in the client's own
    /// failure domain.
    pub fn with_local_keepers(mut self, keepers: BTreeSet<uuid::Uuid>) -> Self {
        self.local = Arc::new(keepers);
        self
    }

    #[cfg(test)]
    pub(super) fn set_transport_filter(
        &self,
        source: uuid::Uuid,
        filter: Option<super::network::TransportFilter>,
    ) {
        self.rpc.set_filter(source, filter);
    }

    /// Recognizes `retired` keeper identities in historical stream genesis and
    /// placement proofs without sending new traffic to retired keepers absent
    /// from `keepers`.
    pub fn with_retired(mut self, retired: BTreeSet<uuid::Uuid>) -> Self {
        self.retired = Arc::new(retired);
        self
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
        if !genesis.valid(self.rpc.keepers()) || voters.iter().any(|id| self.retired.contains(id)) {
            return Err(JournalError::Unavailable);
        }
        let end = Instant::now() + self.deadline;
        let attempt = match self.catalog_voters {
            Some(_) => CATALOG_WRITE_ATTEMPT,
            None => self.deadline,
        };
        let reply = self
            .ask_catalog(Request::Claim(genesis), end, attempt)
            .await?;
        self.install_route(stream, reply)?;
        let bootstrap = async {
            let mut calls =
                FuturesUnordered::from_iter(voters.into_iter().map(|keeper| async move {
                    while !remaining(end).is_zero() {
                        if matches!(
                            self.rpc
                                .call_application(
                                    keeper,
                                    Request::Bootstrap(stream),
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
        let uncertain = AtomicBool::default();
        let outcome = tokio::select! {
            result = self.decide(Request::Create(stream), end, ATTEMPT, &uncertain) => result?,
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
        self.append_after(stream, fence, at, payload, false).await
    }

    /// Appends like `append`; `retried` says that an earlier call of the
    /// same append returned `Unavailable`, so it may have taken effect.
    pub(super) async fn append_after(
        &self,
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payload: Bytes,
        retried: bool,
    ) -> Result<Lsn> {
        if payload.len() > MAX_RECORD {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        let request = Request::Append {
            stream,
            fence,
            at,
            payload: payload.clone(),
        };
        self.write_records(request, stream, fence, at, vec![payload], retried)
            .await
    }

    /// Sends an append or a batch. An attempt that went unanswered may have
    /// committed the records before a competing seal or a trim, and then a
    /// retry is refused `Fenced` or `Trimmed` although the records are in
    /// the stream: such a refusal is not definite. The keeper then says
    /// whether records of this writer's epoch hold exactly these payloads.
    /// When none do, or another epoch's records do, no attempt committed and
    /// none can, so the refusal stands. When they do, the outcome is unknown,
    /// not a success: an earlier, identical call may have written them, and
    /// a call that began after the fencing seal cannot have taken effect.
    async fn write_records(
        &self,
        request: Request,
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payloads: Vec<Bytes>,
        retried: bool,
    ) -> Result<Lsn> {
        let uncertain = AtomicBool::new(retried);
        let end = Instant::now() + self.deadline;
        let refusal = match self
            .decide(request, end, ATTEMPT, &uncertain)
            .await
            .and_then(position)
        {
            Err(refusal @ (JournalError::Fenced { .. } | JournalError::Trimmed { .. }))
                if uncertain.load(Ordering::Relaxed) =>
            {
                refusal
            }
            result => return result,
        };
        let written = Request::Written {
            stream,
            fence,
            at,
            payloads,
        };
        let check = Instant::now() + self.deadline;
        match self
            .decide(written, check, ATTEMPT, &AtomicBool::default())
            .await
            .and_then(position)
        {
            Err(JournalError::Conflict { .. }) => Err(refusal),
            Ok(_) | Err(_) => Err(JournalError::Unavailable),
        }
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
        self.append_batch_after(stream, fence, at, payloads, false)
            .await
    }

    /// Appends like `append_batch`; `retried` says that an earlier call of
    /// the same batch returned `Unavailable`.
    pub(super) async fn append_batch_after(
        &self,
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payloads: Vec<Bytes>,
        retried: bool,
    ) -> Result<Lsn> {
        if !super::state::valid_batch(&payloads) {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        let request = Request::AppendBatch {
            stream,
            fence,
            at,
            payloads: payloads.clone(),
        };
        self.write_records(request, stream, fence, at, payloads, retried)
            .await
    }

    pub async fn head(&self, stream: StreamId) -> Result<Lsn> {
        position(self.operation(Request::Head(stream)).await?)
    }

    /// Discards records through `through`. A trim whose attempt went
    /// unanswered may have taken effect before a competing seal, so a
    /// `Fenced` refusal of its retry leaves the outcome unknown.
    pub async fn trim(&self, stream: StreamId, fence: Fence, through: Lsn) -> Result<()> {
        let uncertain = AtomicBool::default();
        let request = Request::Trim {
            stream,
            fence,
            through,
        };
        match self
            .decide(request, Instant::now() + self.deadline, ATTEMPT, &uncertain)
            .await
            .and_then(unit)
        {
            Err(JournalError::Fenced { .. }) if uncertain.load(Ordering::Relaxed) => {
                Err(JournalError::Unavailable)
            }
            result => result,
        }
    }

    pub async fn delete(&self, stream: StreamId) -> Result<()> {
        unit(self.operation(Request::Delete(stream)).await?)
    }

    /// Clears the recovery fence an operator recovery left on `stream`, so
    /// writers can seal again, and returns the head. Administrators only.
    /// Idempotent: without a recovery fence it only returns the head.
    pub async fn acknowledge_recovery(&self, stream: StreamId) -> Result<Lsn> {
        position(self.operation(Request::AcknowledgeRecovery(stream)).await?)
    }

    pub async fn recovery_fence(&self, stream: StreamId) -> Result<Option<RecoveryFence>> {
        match self.operation(Request::RecoveryFence(stream)).await? {
            Outcome::RecoveryFence(fence) => Ok(fence),
            _ => Err(JournalError::Unavailable),
        }
    }

    pub async fn acknowledge_recovery_with_marker(
        &self,
        stream: StreamId,
        fence: RecoveryFence,
        payload: Bytes,
    ) -> Result<Lsn> {
        position(
            self.operation(Request::AcknowledgeRecoveryWithMarker { stream, fence, payload })
                .await?,
        )
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

    /// Asks the stream's leader to hand leadership to `keeper`. The leader
    /// does so when `keeper` has matched its log and no hand-off happened in
    /// the last minute; either way the call succeeds.
    pub async fn prefer_leader(&self, stream: StreamId, keeper: uuid::Uuid) -> Result<()> {
        unit(decision(
            self.operation(Request::PreferLeader { stream, keeper })
                .await?,
        )?)
    }

    /// Reads the finalized cluster feature level from the catalog.
    pub async fn cluster_version(&self) -> Result<u32> {
        let end = Instant::now() + self.deadline;
        match self
            .ask_catalog(Request::ClusterVersion, end, ATTEMPT)
            .await?
        {
            Reply::ClusterVersion(version) => Ok(version),
            Reply::Decision(Outcome::Refused(error)) => Err(error),
            Reply::Unsupported(_) => Err(JournalError::Unsupported),
            _ => Err(JournalError::Unavailable),
        }
    }

    /// Advances the finalized cluster feature level to `version`.
    /// Administrators only. `Unsupported` when a keeper in the inventory
    /// lacks `version`; `Unavailable`, worth retrying, when one did not
    /// answer.
    pub async fn finalize_version(&self, version: u32) -> Result<u32> {
        let end = Instant::now() + self.deadline;
        let attempt = match self.catalog_voters {
            Some(_) => CATALOG_WRITE_ATTEMPT,
            None => self.deadline,
        };
        match self
            .ask_catalog(Request::FinalizeVersion(version), end, attempt)
            .await?
        {
            Reply::ClusterVersion(finalized) => Ok(finalized),
            Reply::Decision(Outcome::Refused(error)) => Err(error),
            Reply::Unsupported(_) => Err(JournalError::Unsupported),
            _ => Err(JournalError::Unavailable),
        }
    }

    /// Clears a durable corruption quarantine marker for `stream` on `keeper`.
    /// Administrators only.
    pub async fn clear_quarantine(&self, keeper: uuid::Uuid, stream: StreamId) -> Result<()> {
        match self
            .keeper_operation(keeper, Request::ClearQuarantine(stream))
            .await?
        {
            Reply::Decision(outcome) => unit(decision(outcome)?),
            Reply::Unsupported(_) => Err(JournalError::Unsupported),
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

    /// The keeper that last decided a request on `stream`, which was its
    /// leader then.
    pub fn leader(&self, stream: StreamId) -> Option<uuid::Uuid> {
        self.routes
            .lock()
            .get(&stream)
            .and_then(|route| route.leader)
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
            match self
                .rpc
                .call_application(keeper, request.clone(), budget)
                .await
            {
                Ok(Reply::Unsupported(_)) => return Err(JournalError::Unsupported),
                Ok(reply) => return Ok(reply),
                Err(error) if error.kind() == io::ErrorKind::Unsupported => {
                    return Err(JournalError::Unsupported);
                }
                Err(_) => (),
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
        self.decide(
            request,
            Instant::now() + self.deadline,
            ATTEMPT,
            &AtomicBool::default(),
        )
        .await
    }

    /// Sends `request` until a keeper decides it. Sets `uncertain` when an
    /// attempt went unanswered or was answered `Unavailable`, so it may
    /// have taken effect before the deciding one.
    async fn decide(
        &self,
        request: Request,
        end: Instant,
        attempt: Duration,
        uncertain: &AtomicBool,
    ) -> Result<Outcome> {
        let stream = request.stream();
        let mut route = self.route(stream, end).await?;
        let mut saw_corrupted = false;
        let mut saw_unavailable = false;
        while !remaining(end).is_zero() {
            let mut visited = BTreeSet::new();
            let mut contacts = route.contacts.iter().copied();
            let mut preferred = route.leader;
            let call = |keeper| {
                let request = request.clone();
                async move {
                    let reply = self
                        .rpc
                        .call_application(keeper, request, remaining(end).min(attempt))
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
                            saw_unavailable = true;
                            calls.push(call(leader));
                        }
                        Ok(Reply::Decision(Outcome::Refused(JournalError::Corrupted))) => {
                            saw_corrupted = true;
                        }
                        Ok(Reply::Unsupported(_)) => return Err(JournalError::Unsupported),
                        Err(ref error) if error.kind() == io::ErrorKind::Unsupported => {
                            return Err(JournalError::Unsupported);
                        }
                        Ok(Reply::Decision(Outcome::Refused(JournalError::Unavailable)))
                        | Err(_) => {
                            saw_unavailable = true;
                            uncertain.store(true, Ordering::Relaxed);
                        }
                        Ok(Reply::Decision(outcome)) => {
                            self.routes
                                .lock()
                                .entry(stream)
                                .or_insert_with(|| route.clone())
                                .leader = Some(keeper);
                            return decision(outcome);
                        }
                        _ => saw_unavailable = true,
                    }
                }
            }
            sleep(Duration::from_millis(25).min(remaining(end))).await;
            route = self.resolve(stream, end).await?;
            route.leader = None;
        }
        if saw_corrupted && !saw_unavailable {
            Err(JournalError::Corrupted)
        } else {
            Err(JournalError::Unavailable)
        }
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
            .ask_catalog(
                Request::Locate(stream),
                Instant::now() + remaining(end) / 4,
                ATTEMPT,
            )
            .await?;
        self.install_route(stream, reply)
    }

    /// Asks the catalog keeper, or the replicated catalog's voters until one
    /// answers, giving each call at most `attempt`. Repair may have replaced
    /// every configured voter, so the other keepers follow them.
    async fn ask_catalog(
        &self,
        request: Request,
        end: Instant,
        attempt: Duration,
    ) -> Result<Reply> {
        let Some(voters) = self.catalog_voters else {
            for _ in 0..3 {
                let budget = remaining(end).min(attempt);
                if budget.is_zero() {
                    break;
                }
                match self
                    .rpc
                    .call_application(self.catalog, request.clone(), budget)
                    .await
                {
                    Ok(Reply::Unsupported(_)) => return Err(JournalError::Unsupported),
                    Ok(reply) => return Ok(reply),
                    Err(error) if error.kind() == io::ErrorKind::Unsupported => {
                        return Err(JournalError::Unsupported);
                    }
                    Err(_) => sleep(Duration::from_millis(25).min(remaining(end))).await,
                }
            }
            return Err(JournalError::Unavailable);
        };
        let order = self
            .catalog_leader
            .lock()
            .iter()
            .copied()
            .chain(voters)
            .chain(self.rpc.keepers().keys().copied())
            .collect::<Vec<_>>();
        let claim = matches!(request, Request::Claim(_));
        let (keeper, reply) = super::catalog::ask(&order, end, |keeper| {
            let request = request.clone();
            async move {
                self.rpc
                    .call_application(keeper, request, remaining(end).min(attempt))
                    .await
            }
        })
        .await
        .ok_or(JournalError::Unavailable)?;
        if matches!(reply, Reply::Unsupported(_)) {
            return Err(JournalError::Unsupported);
        }
        // A keeper found past the configured voters is remembered for every
        // request, since they no longer host the catalog.
        if claim || !voters.contains(&keeper) {
            *self.catalog_leader.lock() = Some(keeper);
        }
        Ok(reply)
    }

    fn install_route(&self, stream: StreamId, reply: Reply) -> Result<Route> {
        match reply {
            Reply::Catalog(genesis, contacts)
                if genesis.stream == stream
                    && genesis.valid_with_retired(self.rpc.keepers(), &self.retired) =>
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
                route.contacts = contacts
                    .into_iter()
                    .filter(|id| self.rpc.keepers().contains_key(id))
                    .collect();
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
