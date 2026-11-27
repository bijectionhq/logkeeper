//! The replicated catalog: a consensus stream of its own, hosted on the three
//! `catalog_voters` in distinct failure domains.
//!
//! Its genesis comes from configuration, so it needs no catalog to exist.
//! Only its leader appends, as a fixed internal writer, each record at exactly
//! head + 1, so a lost race is a conflict and the next attempt re-reads. Each
//! replica folds the applied records into the entries the single-keeper
//! catalog keeps, with the same rules.
//!
//! - Any replica answers a lookup that its fold finds. Its fold may lag the
//!   leader, but a genesis never changes and contacts are only hints. Only
//!   the leader, after a read barrier, answers that a stream is unknown.
//! - Claims and stages go to the leader, which takes a read barrier and
//!   catches its fold up first. A follower answers with its leader.
//! - The configured `catalog` keeper seeds the stream once, as its leader:
//!   a checkpoint of its single-keeper catalog, which may be empty, then a
//!   `Seeded` marker. Until then the catalog refuses claims, stages and
//!   negative lookups. Another leader hands leadership to the seeder.
//! - When more than `COMPACT_AFTER` records follow the last checkpoint, the
//!   leader appends a checkpoint of every entry and trims what precedes it.
//!   A replica whose next record was trimmed folds again from the floor,
//!   which is always the first record of a complete checkpoint.
//! - The stream is never parked or deleted. Repair replaces its voters like
//!   any stream's, and its own entry records the staged move.

use std::{
    collections::BTreeMap,
    io,
    sync::atomic::{AtomicBool, Ordering},
    time::Duration,
};

use journal_contract::{Epoch, JournalError, Lsn, StreamId};
use openraft::{
    ServerState,
    async_runtime::WatchReceiver,
    errors::{InitializeError, RaftError},
};
use serde::{Deserialize, Serialize};
use tokio::{
    sync::{Mutex, MutexGuard},
    time::Instant,
};
use uuid::Uuid;

use super::{Engine, Group, REQUEST_TIMEOUT, Reply, Request, failure, invalid};
use crate::stream::consensus::Voters;
use crate::stream::consensus::{
    Fence, Genesis, MAX_RECORD, MAX_RECORDS_PER_PAGE, Stage, authority, catalog, decisions, decode,
    encode,
    state::{Command, Outcome},
    storage::CatalogEntry,
};

/// The catalog stream's reserved ID.
pub(in crate::stream::consensus) const STREAM: StreamId = StreamId(u128::MAX);
const FENCE: Fence = Fence {
    epoch: Epoch(1),
    writer: Uuid::from_u128(0x6361_7461_6c6f_672d_7772_6974_6572_0001),
};
const OWNER: &str = "urn:logkeeper:internal:catalog";
const QUOTA_BYTES: u64 = 1 << 30;
const PART_BYTES: usize = 1 << 20;
/// Records after the last checkpoint that trigger compaction.
#[cfg(not(test))]
const COMPACT_AFTER: u64 = 1024;
#[cfg(test)]
pub(super) const COMPACT_AFTER: u64 = 16;
#[cfg(not(test))]
const TEND_INTERVAL: Duration = Duration::from_secs(1);
#[cfg(test)]
const TEND_INTERVAL: Duration = Duration::from_millis(100);
const ATTEMPT: Duration = Duration::from_secs(2);
/// Keeper records per checkpoint record.
const KEEPERS_PER_RECORD: usize = 64;

#[derive(Serialize, Deserialize)]
enum CatalogRecord {
    Claim(Genesis),
    Stage(Stage),
    Contacts(StreamId, Vec<Uuid>),
    /// Entries as they stood when the checkpoint was taken. A checkpoint
    /// may span several records, each of which replaces the entries it holds.
    Checkpoint(Vec<CatalogEntry>),
    /// The seed checkpoint is complete.
    Seeded,
    /// Advances the finalized cluster feature level monotonically. Only
    /// appended once finalized past V1, so N-1 binaries can read the catalog
    /// stream before finalize.
    ClusterVersion(u32),
    /// A change to the configuration authority's keeper records. Only
    /// appended once `CLUSTER_VERSION_LEASES` is finalized.
    Authority(authority::Change),
    /// Keeper records as they stood when a checkpoint was taken; each
    /// replaces the records it holds. Only appended with leases finalized.
    Keepers(Vec<(Uuid, authority::KeeperRecord)>),
    /// The latest recovery of each stream, as a checkpoint held them.
    Recoveries(Vec<authority::RecoveryRecord>),
}

struct Fold {
    entries: BTreeMap<StreamId, CatalogEntry>,
    next: Lsn,
    /// Records applied since the last checkpoint record.
    tail: u64,
    seeded: bool,
    cluster_version: u32,
    authority: authority::Records,
}

impl Fold {
    fn new(genesis: &Genesis, next: Lsn) -> Self {
        let own = CatalogEntry {
            genesis: genesis.clone(),
            contacts: genesis.voters.into_iter().collect(),
            staged: None,
        };
        Self {
            entries: BTreeMap::from([(STREAM, own)]),
            next,
            tail: 0,
            // Only compaction trims, and it follows the seed.
            seeded: next > Lsn(1),
            cluster_version: crate::stream::consensus::CLUSTER_VERSION_V1,
            authority: authority::Records::default(),
        }
    }

    fn enforced(&self) -> bool {
        self.cluster_version >= crate::stream::consensus::CLUSTER_VERSION_LEASES
    }

    /// Applies one record by the single-keeper catalog's rules: the first
    /// claim wins, and a stage or contacts need an entry.
    fn apply(&mut self, record: CatalogRecord) {
        self.tail += 1;
        match record {
            CatalogRecord::Claim(genesis) => {
                self.entries
                    .entry(genesis.stream)
                    .or_insert_with(|| CatalogEntry {
                        contacts: genesis.voters.into_iter().collect(),
                        genesis,
                        staged: None,
                    });
            }
            CatalogRecord::Stage(stage) => {
                if let Some(entry) = self.entries.get_mut(&stage.stream) {
                    entry.staged = Some(stage);
                    entry.contacts = entry.ordered_contacts().into_iter().collect();
                }
            }
            CatalogRecord::Contacts(stream, contacts) => {
                if let Some(entry) = self.entries.get_mut(&stream) {
                    entry.contacts.extend(contacts);
                    entry.contacts = entry.ordered_contacts().into_iter().collect();
                }
            }
            CatalogRecord::Checkpoint(entries) => {
                self.tail = 0;
                for entry in entries {
                    self.entries.insert(entry.genesis.stream, entry);
                }
            }
            CatalogRecord::Seeded => self.seeded = true,
            CatalogRecord::ClusterVersion(version) => {
                self.cluster_version = self.cluster_version.max(version);
            }
            CatalogRecord::Authority(change) => {
                // A recovery installs its membership with its fence.
                if let authority::Change::Recover { stage, .. } = &change
                    && let Some(entry) = self.entries.get_mut(&stage.stream)
                {
                    entry.staged = Some(stage.clone());
                    entry.contacts = entry.ordered_contacts().into_iter().collect();
                }
                self.authority.apply(&change);
            }
            CatalogRecord::Keepers(records) => {
                self.authority.keepers.extend(records);
            }
            CatalogRecord::Recoveries(records) => {
                self.authority
                    .recoveries
                    .extend(records.into_iter().map(|record| (record.stream, record)));
            }
        }
    }
}

pub(super) struct CatalogStream {
    genesis: Genesis,
    /// The single-keeper catalog, which seeds this stream.
    seeder: Uuid,
    fold: Mutex<Fold>,
    /// Serializes this keeper's appends.
    writing: Mutex<()>,
    sealed: AtomicBool,
    /// The keeper that last answered a write, tried first.
    leader: parking_lot::Mutex<Option<Uuid>>,
}

impl CatalogStream {
    pub fn matches(&self, genesis: &Genesis) -> bool {
        self.genesis == *genesis
    }

    pub fn new(voters: Voters, seeder: Uuid) -> Self {
        let genesis = Genesis {
            stream: STREAM,
            voters,
            quota_bytes: QUOTA_BYTES,
            immutable: false,
        };
        Self {
            fold: Mutex::new(Fold::new(&genesis, Lsn(1))),
            genesis,
            seeder,
            writing: Mutex::default(),
            sealed: AtomicBool::new(false),
            leader: parking_lot::Mutex::default(),
        }
    }
}

impl CatalogStream {
    /// The configured voters of the catalog stream.
    pub fn voters(&self) -> Voters {
        self.genesis.voters
    }
}

fn found(entry: &CatalogEntry) -> Reply {
    Reply::Catalog(entry.genesis.clone(), entry.ordered_contacts())
}

fn conflict() -> Reply {
    failure(JournalError::Conflict { head: Lsn(0) })
}

fn is_conflict(reply: &Reply) -> bool {
    matches!(
        reply,
        Reply::Decision(Outcome::Refused(JournalError::Conflict { .. }))
    )
}

fn describe(reply: &Reply) -> String {
    match reply {
        Reply::Decision(Outcome::Refused(error)) => format!("{error:?}"),
        Reply::Leader(_) => "leadership moved".into(),
        _ => "unexpected reply".into(),
    }
}

/// Splits entries into checkpoint records of about `PART_BYTES`.
fn parts(entries: Vec<CatalogEntry>) -> io::Result<Vec<Vec<CatalogEntry>>> {
    let mut parts = vec![Vec::new()];
    let mut bytes = 0;
    for entry in entries {
        let size = encode(&entry)?.len();
        if bytes + size > PART_BYTES && !parts.last().unwrap().is_empty() {
            parts.push(Vec::new());
            bytes = 0;
        }
        bytes += size;
        parts.last_mut().unwrap().push(entry);
    }
    Ok(parts)
}

impl Engine {
    fn catalog_stream(&self) -> io::Result<&CatalogStream> {
        self.catalog_stream
            .as_ref()
            .ok_or_else(|| invalid("keeper has no replicated catalog"))
    }

    async fn catalog_group(&self) -> Option<std::sync::Arc<Group>> {
        self.groups.lock().await.get(&STREAM).cloned()
    }

    /// Answers a catalog request from this keeper's replica.
    pub(super) async fn serve_catalog_stream(&self, request: Request) -> io::Result<Reply> {
        self.require_media()?;
        let catalog = self.catalog_stream()?;
        let Some(group) = self.catalog_group().await else {
            return Ok(Reply::Leader(None));
        };
        match request {
            Request::Claim(genesis) => self.claim_replicated(catalog, &group, genesis).await,
            Request::Locate(stream) => self.locate_replicated(catalog, &group, stream).await,
            Request::Stage(stage) => self.stage_replicated(catalog, &group, stage).await,
            Request::Staging(stream) => self.staged_replicated(catalog, &group, stream).await,
            Request::ClusterVersion => self.cluster_version_replicated(catalog, &group).await,
            Request::FinalizeVersion(target) => {
                self.finalize_version_replicated(catalog, &group, target)
                    .await
            }
            Request::RenewLease { .. } => {
                self.renew_replicated(catalog, &group, request, true).await
            }
            Request::FenceKeeper(keeper) => {
                self.authority_write(catalog, &group, authority::Change::Fence { keeper })
                    .await
            }
            Request::NamedStreams(keeper) => {
                let (fold, _) = match self.leading(catalog, &group, false).await {
                    Ok(view) => view,
                    Err(reply) => return Ok(reply),
                };
                if !fold.seeded {
                    return Ok(failure(JournalError::Unavailable));
                }
                Ok(Reply::Named(crate::stream::consensus::catalog::named(
                    fold.entries.values(),
                    keeper,
                )))
            }
            Request::RecoverStream {
                stage,
                dead,
                record,
            } => {
                self.recover_replicated(catalog, &group, stage, dead, record)
                    .await
            }
            _ => Err(invalid("invalid catalog request")),
        }
    }

    /// Answers a lease renewal from this keeper's catalog replica.
    pub(super) async fn serve_renewal(&self, request: Request, forward: bool) -> io::Result<Reply> {
        self.require_media()?;
        let catalog = self.catalog_stream()?;
        let Some(group) = self.catalog_group().await else {
            return Ok(Reply::Leader(None));
        };
        self.renew_replicated(catalog, &group, request, forward)
            .await
    }

    /// Asks the replicated catalog, starting with this keeper when it holds
    /// a replica, then the last writer and the configured voters, then the
    /// other keepers, since repair may have replaced every configured voter.
    pub(super) async fn ask_catalog_stream(&self, request: Request) -> io::Result<Reply> {
        let catalog = self.catalog_stream()?;
        let mut order = Vec::new();
        if self.catalog_group().await.is_some() {
            order.push(self.id);
        }
        order.extend(*catalog.leader.lock());
        order.extend(catalog.genesis.voters);
        order.extend(self.placement.domains().keys().copied());
        let end = Instant::now() + REQUEST_TIMEOUT;
        let write = !matches!(
            request,
            Request::Locate(_) | Request::Staging(_) | Request::ClusterVersion
        );
        let answer = super::super::catalog::ask(&order, end, |keeper| {
            let request = request.clone();
            async move {
                if keeper == self.id {
                    self.serve_catalog_stream(request).await
                } else {
                    let budget = end.saturating_duration_since(Instant::now()).min(ATTEMPT);
                    self.rpc.call_application(keeper, request, budget).await
                }
            }
        })
        .await;
        Ok(match answer {
            Some((keeper, reply)) => {
                if write || !catalog.genesis.voters.contains(&keeper) {
                    *catalog.leader.lock() = Some(keeper);
                }
                reply
            }
            None => failure(JournalError::Unavailable),
        })
    }

    /// The fold, caught up with this replica's applied records, and the
    /// applied head.
    async fn caught_up<'a>(
        &self,
        catalog: &'a CatalogStream,
        group: &Group,
    ) -> Result<(MutexGuard<'a, Fold>, Lsn), JournalError> {
        let mut fold = catalog.fold.lock().await;
        loop {
            let head = match group.state.head() {
                Ok(head) => head,
                Err(JournalError::NotFound) => Lsn(0),
                Err(error) => return Err(error),
            };
            if fold.next > head {
                return Ok((fold, head));
            }
            match group.state.page(fold.next, MAX_RECORDS_PER_PAGE).await {
                Ok(page) if page.records.is_empty() => return Ok((fold, page.head)),
                Ok(page) => {
                    for (at, bytes) in page.records {
                        let Ok(record) = decode::<CatalogRecord>(&bytes) else {
                            // Only keepers write the catalog, and its records
                            // are checksummed, so a committed record that does
                            // not decode is a keeper bug or a version skew.
                            crate::stream::consensus::logging::critical!(
                                "keeper {} cannot read catalog record {} of stream {}",
                                self.id,
                                at.0,
                                crate::stream::consensus::logging::stream_uuid(STREAM)
                            );
                            return Err(JournalError::Unavailable);
                        };
                        fold.apply(record);
                        fold.next = Lsn(at.0 + 1);
                    }
                }
                Err(JournalError::Trimmed { floor }) => *fold = Fold::new(&catalog.genesis, floor),
                Err(error) => return Err(error),
            }
        }
    }

    /// The fold as of a read barrier on the leader. A writer first creates
    /// the stream and seals its internal fence, once per keeper process.
    async fn leading<'a>(
        &self,
        catalog: &'a CatalogStream,
        group: &Group,
        write: bool,
    ) -> Result<(MutexGuard<'a, Fold>, Lsn), Reply> {
        group.barrier(Instant::now() + REQUEST_TIMEOUT).await?;
        if write && !catalog.sealed.load(Ordering::Acquire) {
            let seal = Command::Seal {
                expected: Epoch(0),
                writer: FENCE.writer,
                owner: OWNER.into(),
            };
            for command in [Command::Create, seal] {
                match group.write(command).await {
                    Reply::Decision(Outcome::Unit | Outcome::Sealed(_)) => (),
                    reply => return Err(reply),
                }
            }
            catalog.sealed.store(true, Ordering::Release);
        }
        self.caught_up(catalog, group).await.map_err(failure)
    }

    async fn append_catalog(
        &self,
        group: &Group,
        head: Lsn,
        record: &CatalogRecord,
    ) -> Result<Lsn, Reply> {
        let payload = encode(record).map_err(|_| failure(JournalError::Unavailable))?;
        if payload.len() > MAX_RECORD {
            return Err(failure(JournalError::TooLarge { max: MAX_RECORD }));
        }
        match group
            .write(Command::Append {
                fence: FENCE,
                owner: OWNER.into(),
                at: Lsn(head.0 + 1),
                payload: payload.into(),
            })
            .await
        {
            Reply::Decision(Outcome::At(at)) => Ok(at),
            reply => Err(reply),
        }
    }

    /// Appends a checkpoint of `entries` after `head` and returns the
    /// position of its first record and the new head.
    async fn checkpoint(
        &self,
        group: &Group,
        head: Lsn,
        entries: Vec<CatalogEntry>,
    ) -> Result<(Lsn, Lsn), Reply> {
        let parts = parts(entries).map_err(|_| failure(JournalError::Unavailable))?;
        let mut at = head;
        for part in parts {
            at = self
                .append_catalog(group, at, &CatalogRecord::Checkpoint(part))
                .await?;
        }
        Ok((Lsn(head.0 + 1), at))
    }

    async fn claim_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        genesis: Genesis,
    ) -> io::Result<Reply> {
        if genesis.stream == STREAM || !self.placement.genesis(&genesis) {
            return Ok(conflict());
        }
        let _writing = catalog.writing.lock().await;
        for _ in 0..3 {
            let (fold, head) = match self.leading(catalog, group, true).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            // Five voters need every keeper to read their roster.
            if !crate::stream::consensus::decisions::creates_replication(
                genesis.voters.len(),
                fold.cluster_version,
                crate::stream::consensus::CLUSTER_VERSION_REPLICATION,
            ) {
                return Ok(failure(JournalError::Unsupported));
            }
            if let Some(existing) = fold.entries.get(&genesis.stream) {
                return Ok(if existing.genesis == genesis {
                    found(existing)
                } else {
                    conflict()
                });
            }
            drop(fold);
            match self
                .append_catalog(group, head, &CatalogRecord::Claim(genesis.clone()))
                .await
            {
                Ok(_) => {
                    let (fold, _) = self
                        .caught_up(catalog, group)
                        .await
                        .map_err(|_| invalid("claimed catalog entry is not readable"))?;
                    return Ok(fold
                        .entries
                        .get(&genesis.stream)
                        .map_or_else(|| failure(JournalError::Unavailable), found));
                }
                Err(reply) if is_conflict(&reply) => continue,
                Err(reply) => return Ok(reply),
            }
        }
        Ok(failure(JournalError::Unavailable))
    }

    async fn stage_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        stage: Stage,
    ) -> io::Result<Reply> {
        if !self.placement.stage(&stage) {
            return Err(invalid("invalid staged placement"));
        }
        let _writing = catalog.writing.lock().await;
        for _ in 0..3 {
            let (fold, head) = match self.leading(catalog, group, true).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            let entry = fold
                .entries
                .get(&stage.stream)
                .ok_or_else(|| invalid("missing catalog entry"))?;
            if !catalog::admits_stage(entry, &stage) {
                return Ok(catalog::stage_conflict());
            }
            if entry.staged.as_ref() == Some(&stage) {
                return Ok(Reply::Staged(stage));
            }
            drop(fold);
            match self
                .append_catalog(group, head, &CatalogRecord::Stage(stage.clone()))
                .await
            {
                Ok(_) => return Ok(Reply::Staged(stage)),
                Err(reply) if is_conflict(&reply) => continue,
                Err(reply) => return Ok(reply),
            }
        }
        Ok(failure(JournalError::Unavailable))
    }

    async fn cluster_version_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
    ) -> io::Result<Reply> {
        let (fold, _) = match self.leading(catalog, group, false).await {
            Ok(view) => view,
            Err(reply) => return Ok(reply),
        };
        if !fold.seeded {
            return Ok(failure(JournalError::Unavailable));
        }
        let version = fold.cluster_version;
        self.disk.set_write_version(version);
        Ok(Reply::ClusterVersion(version))
    }

    async fn finalize_version_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        target: u32,
    ) -> io::Result<Reply> {
        if target < crate::stream::consensus::CLUSTER_VERSION_V1
            || target > crate::stream::consensus::CLUSTER_VERSION_CURRENT
        {
            return Ok(failure(JournalError::Unsupported));
        }
        let _writing = catalog.writing.lock().await;
        for _ in 0..3 {
            let (fold, head) = match self.leading(catalog, group, true).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            if target < fold.cluster_version {
                return Ok(conflict());
            }
            if target == fold.cluster_version {
                self.disk.set_write_version(target);
                return Ok(Reply::ClusterVersion(target));
            }
            drop(fold);
            match self
                .append_catalog(group, head, &CatalogRecord::ClusterVersion(target))
                .await
            {
                Ok(_) => {
                    let _ = self.caught_up(catalog, group).await;
                    self.disk.set_write_version(target);
                    return Ok(Reply::ClusterVersion(target));
                }
                Err(reply) if is_conflict(&reply) => continue,
                Err(reply) => return Ok(reply),
            }
        }
        Ok(failure(JournalError::Unavailable))
    }

    async fn locate_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        stream: StreamId,
    ) -> io::Result<Reply> {
        if let Ok((fold, _)) = self.caught_up(catalog, group).await
            && let Some(entry) = fold.entries.get(&stream)
        {
            return Ok(found(entry));
        }
        let (fold, _) = match self.leading(catalog, group, false).await {
            Ok(view) => view,
            Err(reply) => return Ok(reply),
        };
        Ok(match fold.entries.get(&stream) {
            Some(entry) => found(entry),
            None if !fold.seeded => failure(JournalError::Unavailable),
            None => failure(JournalError::NotFound),
        })
    }

    /// The latest move staged for `stream`, read on the leader: a copy that
    /// a lagging replica certified could miss the recovery that fenced it.
    async fn staged_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        stream: StreamId,
    ) -> io::Result<Reply> {
        let (fold, _) = match self.leading(catalog, group, false).await {
            Ok(view) => view,
            Err(reply) => return Ok(reply),
        };
        Ok(match fold.entries.get(&stream) {
            Some(entry) => entry
                .staged
                .clone()
                .map_or(Reply::Decision(Outcome::Unit), Reply::Staged),
            None if !fold.seeded => failure(JournalError::Unavailable),
            None => failure(JournalError::NotFound),
        })
    }

    /// Answers a lease renewal on the leader after a read barrier, so a
    /// renewal answered after a recovery or a fence committed sees it. The
    /// first enforced renewal of a keeper or media incarnation enrolls it.
    /// A follower forwards the renewal to its leader once.
    pub(super) async fn renew_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        request: Request,
        forward: bool,
    ) -> io::Result<Reply> {
        let Request::RenewLease {
            keeper,
            incarnation,
            epoch,
        } = request.clone()
        else {
            return Err(invalid("invalid lease renewal"));
        };
        let metrics = group.raft.metrics().borrow_watched().clone();
        if metrics.state != ServerState::Leader {
            let leader = metrics.current_leader.map(Uuid::from_u128);
            return Ok(match leader {
                Some(leader) if forward && leader != self.id => self
                    .rpc
                    .call_application(leader, request, ATTEMPT)
                    .await
                    .unwrap_or_else(|_| Reply::Leader(Some(leader))),
                leader => Reply::Leader(leader),
            });
        }
        let lease = (
            self.lease.duration().as_millis() as u64,
            self.lease.margin().as_millis() as u64,
        );
        let enrollment = {
            let (fold, _) = match self.leading(catalog, group, false).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            let enforced = fold.enforced();
            match fold
                .authority
                .pending(keeper, incarnation, lease.0, lease.1)
            {
                Some(change) if enforced => change,
                _ => {
                    return Ok(Reply::Lease(fold.authority.grant(
                        keeper,
                        incarnation,
                        epoch,
                        enforced,
                        lease.0,
                        lease.1,
                    )));
                }
            }
        };
        let mut change = Some(enrollment);
        // An enrollment may be followed by a record of this lease.
        while let Some(pending) = change.take() {
            match self.authority_write(catalog, group, pending).await? {
                Reply::Decision(Outcome::Unit) => (),
                reply => return Ok(reply),
            }
            let (fold, _) = self
                .caught_up(catalog, group)
                .await
                .map_err(|_| invalid("enrolled keeper record is not readable"))?;
            change = fold
                .authority
                .pending(keeper, incarnation, lease.0, lease.1)
                .filter(|next| matches!(next, authority::Change::Lease { .. }));
        }
        let (fold, _) = self
            .caught_up(catalog, group)
            .await
            .map_err(|_| invalid("enrolled keeper record is not readable"))?;
        Ok(Reply::Lease(fold.authority.grant(
            keeper,
            incarnation,
            epoch,
            fold.enforced(),
            lease.0,
            lease.1,
        )))
    }

    /// Appends one change to the authority's records on the leader. Refused
    /// as unsupported until leases are finalized.
    async fn authority_write(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        change: authority::Change,
    ) -> io::Result<Reply> {
        let _writing = catalog.writing.lock().await;
        let record = CatalogRecord::Authority(change);
        for _ in 0..3 {
            let (fold, head) = match self.leading(catalog, group, true).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            if !fold.enforced() {
                return Ok(failure(JournalError::Unsupported));
            }
            // A recovery checks its source against the committed move at the
            // head it appends after, as a stage does.
            if let CatalogRecord::Authority(authority::Change::Recover { stage, .. }) = &record
                && !fold
                    .entries
                    .get(&stage.stream)
                    .is_some_and(|entry| catalog::admits_stage(entry, stage))
            {
                return Ok(catalog::stage_conflict());
            }
            drop(fold);
            match self.append_catalog(group, head, &record).await {
                Ok(_) => return Ok(Reply::Decision(Outcome::Unit)),
                Err(reply) if is_conflict(&reply) => continue,
                Err(reply) => return Ok(reply),
            }
        }
        Ok(failure(JournalError::Unavailable))
    }

    /// An operator recovery's catalog transaction, in one record: the
    /// recovered membership, the fence of every voter it leaves, and the
    /// epoch bumps of the keepers the operator declared dead.
    async fn recover_replicated(
        &self,
        catalog: &CatalogStream,
        group: &Group,
        stage: Stage,
        dead: Vec<Uuid>,
        record: authority::RecoveryRecord,
    ) -> io::Result<Reply> {
        let fenced = authority::fenced_by(&stage);
        if stage.stream == STREAM
            || !authority::describes(&record, &stage)
            || !stage.recovery()
            || !self.placement.stage(&stage)
            || dead.iter().any(|keeper| !fenced.contains(keeper))
        {
            return Err(invalid("invalid recovery stage"));
        }
        let wait_ms = decisions::recovery_wait(
            self.lease.duration().as_millis() as u64,
            self.lease.margin().as_millis() as u64,
        )
        .ok_or_else(|| invalid("lease duration overflows"))?;
        let done = {
            let (fold, _) = match self.leading(catalog, group, false).await {
                Ok(view) => view,
                Err(reply) => return Ok(reply),
            };
            if !fold.seeded {
                return Ok(failure(JournalError::Unavailable));
            }
            let entry = fold
                .entries
                .get(&stage.stream)
                .ok_or_else(|| invalid("missing catalog entry"))?;
            if !catalog::admits_stage(entry, &stage) {
                return Ok(catalog::stage_conflict());
            }
            entry.staged.as_ref() == Some(&stage) && fold.authority.recovered(&stage)
        };
        if !done {
            match self
                .authority_write(
                    catalog,
                    group,
                    authority::Change::Recover {
                        stage: stage.clone(),
                        dead,
                        record,
                    },
                )
                .await?
            {
                Reply::Decision(Outcome::Unit) => (),
                reply => return Ok(reply),
            }
        }
        let (fold, _) = self
            .caught_up(catalog, group)
            .await
            .map_err(|_| invalid("recovered catalog entry is not readable"))?;
        let wait_ms = fold.authority.recovery_wait(&fenced, wait_ms);
        Ok(Reply::Recovered(authority::Recovered {
            record: fold
                .authority
                .recoveries
                .get(&stage.stream)
                .copied()
                .unwrap_or(record),
            unleased: fold.authority.unleased(&fenced),
            fenced,
            wait_ms,
            written: !done,
        }))
    }

    /// Registers and initializes this keeper's catalog replica, then seeds
    /// and compacts the catalog while this keeper leads it.
    pub(super) async fn tend_catalog_stream(&self) {
        let Ok(catalog) = self.catalog_stream() else {
            return;
        };
        let mut bootstrapped = !catalog.genesis.voters.contains(&self.id);
        let mut schedule = tokio::time::interval(TEND_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => (),
            }
            if !bootstrapped {
                match self.bootstrap_catalog_stream(catalog).await {
                    Ok(()) => bootstrapped = true,
                    Err(error) => {
                        if let Some(dropped) = crate::stream::consensus::logging::rate_limit(
                            "catalog.bootstrap_deferred",
                            Some(STREAM),
                        ) {
                            tracing::warn!(
                                keeper = %self.id,
                                stream = %crate::stream::consensus::logging::stream_uuid(STREAM),
                                error = %error,
                                dropped = dropped,
                                "catalog bootstrap deferred"
                            );
                        }
                    }
                }
            }
            self.tend(catalog).await;
        }
    }

    /// Initializing is idempotent, so every configured voter initializes.
    /// A copy this keeper retired stays retired.
    async fn bootstrap_catalog_stream(&self, catalog: &CatalogStream) -> io::Result<()> {
        if self.disk.genesis(STREAM).is_some()
            && self
                .disk
                .ownership(STREAM)
                .is_some_and(|book| book.generation().is_none())
        {
            return Ok(());
        }
        if self.disk.genesis(STREAM).is_none() {
            self.check_identity().await;
        }
        let group = self.group(catalog.genesis.clone()).await?;
        match group
            .raft
            .initialize(self.nodes(catalog.genesis.voters))
            .await
        {
            Ok(()) | Err(RaftError::APIError(InitializeError::NotAllowed(_))) => Ok(()),
            Err(error) => Err(io::Error::other(error)),
        }
    }

    async fn tend(&self, catalog: &CatalogStream) {
        let Some(group) = self.catalog_group().await else {
            return;
        };
        if group.raft.metrics().borrow_watched().state != ServerState::Leader {
            return;
        }
        if let Ok((fold, _)) = self.caught_up(catalog, &group).await
            && fold.seeded
            && fold.tail <= COMPACT_AFTER
        {
            return;
        }
        let Ok(_writing) = catalog.writing.try_lock() else {
            return;
        };
        let Ok((fold, head)) = self.leading(catalog, &group, true).await else {
            return;
        };
        if !fold.seeded {
            drop(fold);
            if self.id == catalog.seeder {
                self.seed(&group, head).await;
            } else {
                hand_to_seeder(&group, catalog.seeder).await;
            }
        } else if fold.tail > COMPACT_AFTER {
            let entries = fold.entries.values().cloned().collect();
            let cluster_version = fold.cluster_version;
            let keepers = fold
                .authority
                .keepers
                .iter()
                .map(|(keeper, record)| (*keeper, record.clone()))
                .collect::<Vec<_>>();
            let recoveries = fold.authority.recoveries.values().copied().collect();
            drop(fold);
            self.compact(&group, head, entries, keepers, recoveries, cluster_version)
                .await;
        }
    }

    /// Imports the single-keeper catalog's entries, once.
    async fn seed(&self, group: &Group, head: Lsn) {
        let entries = self
            .disk
            .catalog_entries()
            .into_iter()
            .filter(|entry| entry.genesis.stream != STREAM)
            .collect::<Vec<_>>();
        let cluster_version = self.disk.cluster_version();
        let count = entries.len();
        let seeded = async {
            let (_, mut head) = self.checkpoint(group, head, entries).await?;
            if cluster_version > crate::stream::consensus::CLUSTER_VERSION_V1 {
                head = self
                    .append_catalog(group, head, &CatalogRecord::ClusterVersion(cluster_version))
                    .await?;
            }
            self.append_catalog(group, head, &CatalogRecord::Seeded)
                .await
        }
        .await;
        match seeded {
            Ok(_) => tracing::info!(
                keeper = %self.id,
                stream = %crate::stream::consensus::logging::stream_uuid(STREAM),
                entries = count,
                "seeded replicated catalog"
            ),
            Err(reply) => {
                if let Some(dropped) = crate::stream::consensus::logging::rate_limit(
                    "catalog.seed_deferred",
                    Some(STREAM),
                ) {
                    tracing::warn!(
                        keeper = %self.id,
                        stream = %crate::stream::consensus::logging::stream_uuid(STREAM),
                        reason = %describe(&reply),
                        dropped = dropped,
                        "catalog seed deferred"
                    );
                }
            }
        }
    }

    async fn compact(
        &self,
        group: &Group,
        head: Lsn,
        entries: Vec<CatalogEntry>,
        keepers: Vec<(Uuid, authority::KeeperRecord)>,
        recoveries: Vec<authority::RecoveryRecord>,
        cluster_version: u32,
    ) {
        let compacted = async {
            let (first, mut last) = self.checkpoint(group, head, entries).await?;
            // Keeper records exist only once leases are finalized.
            for part in keepers.chunks(KEEPERS_PER_RECORD) {
                last = self
                    .append_catalog(group, last, &CatalogRecord::Keepers(part.to_vec()))
                    .await?;
            }
            for part in recoveries.chunks(KEEPERS_PER_RECORD) {
                last = self
                    .append_catalog(group, last, &CatalogRecord::Recoveries(part.to_vec()))
                    .await?;
            }
            if cluster_version > crate::stream::consensus::CLUSTER_VERSION_V1 {
                self.append_catalog(group, last, &CatalogRecord::ClusterVersion(cluster_version))
                    .await?;
            }
            match group
                .write(Command::Trim {
                    fence: FENCE,
                    owner: OWNER.into(),
                    through: Lsn(first.0 - 1),
                })
                .await
            {
                Reply::Decision(Outcome::Unit) => Ok(()),
                reply => Err(reply),
            }
        }
        .await;
        if let Err(reply) = compacted {
            if let Some(dropped) = crate::stream::consensus::logging::rate_limit(
                "catalog.compaction_deferred",
                Some(STREAM),
            ) {
                tracing::warn!(
                    keeper = %self.id,
                    stream = %crate::stream::consensus::logging::stream_uuid(STREAM),
                    reason = %describe(&reply),
                    dropped = dropped,
                    "catalog compaction deferred"
                );
            }
        }
    }
}

/// Hands leadership of the unseeded catalog to its seeder once the seeder
/// has matched the log.
async fn hand_to_seeder(group: &Group, seeder: Uuid) {
    let metrics = group.raft.metrics().borrow_watched().clone();
    let matched = metrics
        .replication
        .as_ref()
        .and_then(|progress| progress.get(&seeder.as_u128()).copied().flatten())
        .map(|log| log.index);
    if matched.is_some() && matched == metrics.last_log_index {
        let _ = group.raft.trigger().transfer_leader(seeder.as_u128()).await;
    }
}

/// Requests a client may not send to the catalog stream, which only its
/// leader writes.
pub(super) fn internal(request: &Request) -> bool {
    request.stream() == STREAM
        && matches!(
            request,
            Request::Bootstrap(_)
                | Request::Create(_)
                | Request::Seal { .. }
                | Request::Append { .. }
                | Request::AppendBatch { .. }
                | Request::StageOriginal { .. }
                | Request::AppendOriginal { .. }
                | Request::Trim { .. }
                | Request::TrimCheckpoint { .. }
                | Request::Delete(_)
                | Request::AcknowledgeRecovery(_)
                | Request::Written { .. }
                | Request::OffloadStatus { .. }
                | Request::Restore { .. }
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_fold_keeps_the_first_claim_and_restarts_from_a_checkpoint() {
        let ids = [1, 2, 3, 4].map(Uuid::from_u128);
        let own = Genesis {
            stream: STREAM,
            voters: Voters::from([ids[0], ids[1], ids[2]]),
            quota_bytes: QUOTA_BYTES,
            immutable: false,
        };
        let genesis = |voters| Genesis {
            stream: StreamId(7),
            voters,
            quota_bytes: 4096,
            immutable: false,
        };
        let first = genesis(Voters::from([ids[0], ids[1], ids[2]]));
        let stage = Stage {
            stream: StreamId(7),
            source: 1,
            old: first.voters,
            target: Voters::from([ids[0], ids[1], ids[3]]),
        };
        let mut fold = Fold::new(&own, Lsn(1));
        for record in [
            CatalogRecord::Checkpoint(Vec::new()),
            CatalogRecord::Seeded,
            CatalogRecord::Claim(first.clone()),
            CatalogRecord::Claim(genesis(Voters::from([ids[0], ids[1], ids[3]]))),
            CatalogRecord::Stage(stage.clone()),
            CatalogRecord::Contacts(StreamId(8), vec![ids[3]]),
        ] {
            fold.apply(decode(&encode(&record).unwrap()).unwrap());
        }
        assert!(fold.seeded);
        // Every record after the checkpoint counts toward compaction.
        assert_eq!(fold.tail, 5);
        let entry = &fold.entries[&StreamId(7)];
        assert_eq!(entry.genesis, first);
        assert_eq!(entry.staged.as_ref(), Some(&stage));
        assert_eq!(entry.ordered_contacts(), [ids[0], ids[1], ids[3], ids[2]]);
        assert!(!fold.entries.contains_key(&StreamId(8)));

        let checkpoint = fold.entries.values().cloned().collect();
        let mut restarted = Fold::new(&own, Lsn(9));
        assert!(restarted.seeded);
        restarted.apply(CatalogRecord::Checkpoint(checkpoint));
        assert_eq!(restarted.tail, 0);
        assert_eq!(
            restarted.entries[&StreamId(7)].ordered_contacts(),
            entry.ordered_contacts()
        );
        assert_eq!(restarted.entries[&STREAM].genesis, own);
    }
}
