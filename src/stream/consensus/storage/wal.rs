//! One writer serializes durable mutations across all stream groups.

use crate::stream::consensus::decisions;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{self, BufReader, Read},
    path::PathBuf,
    sync::{
        Arc, Weak,
        atomic::{AtomicBool, AtomicU32, Ordering},
    },
};

use journal_contract::StreamId;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};

use tokio::sync::{mpsc, oneshot};
use uuid::Uuid;

mod legacy;
pub(super) mod segmented;
pub use segmented::SalvageReport;
use segmented::{Segmented, Tuning};

#[cfg(test)]
mod tests;

use super::{
    Entry, Genesis, Log, LogId, Vote,
    media::{Boundary, Enrollment, Media, Opened, QuarantineStore},
    objects::{Location, Objects},
    snapshot::Selected,
    space::{Admission, Reservation, Space, WAL_METADATA_BYTES},
};
use crate::stream::{
    consensus::{
        Stage, decode, invalid,
        network::{Lane, has_application_entries},
        ownership::{self, Change, Ownership},
        placement::Placement,
        state::Command,
    },
    keeper::durability::{sync_directory, sync_file},
};

const MAX_ROUND_BYTES: usize = 32 * 1024 * 1024;
const MAX_WORK_BYTES: u64 = 68 * 1024 * 1024;
const MAX_APPEND_ENTRIES: usize = 64;
const MAX_ENTRY_OVERHEAD: u64 = 16 * 1024;
const MAX_ROUND_RECORDS: usize = 128;
const MAINTENANCE_QUEUE: usize = 16;
const REPLICATION_QUEUE: usize = 16;
const FOLLOWER_SUFFIX_LIMIT: usize = segmented::MAX_SUFFIX - 16;
const MAX_CONTACTS: usize = 128;
/// How long a noted commit index waits for a round that runs anyway before
/// an idle keeper writes it in a round of its own.
pub(in crate::stream::consensus) const COMMITTED_FLUSH: std::time::Duration =
    std::time::Duration::from_millis(500);

/// Commit indexes OpenRaft reported that the WAL does not hold yet, with the
/// replica generation that reported each.
type Noted = parking_lot::Mutex<BTreeMap<StreamId, (u64, LogId)>>;

#[derive(Serialize, Deserialize)]
pub(in crate::stream::consensus) enum Record {
    Register(Genesis),
    Claim(Genesis),
    Stage(Stage),
    Vote(StreamId, Vote),
    Append(StreamId, Vec<Entry>),
    Truncate(StreamId, u64),
    Purge(StreamId, LogId),
    Snapshot(StreamId, Selected),
    Contacts(StreamId, BTreeSet<Uuid>),
    Ownership(StreamId, Change),
    Owned(u64, Box<Record>),
    /// An operator recovery's vote and entries, made durable in one round.
    /// The entries end the frame body like an `Append`'s. Added after
    /// `Owned`, so an older keeper refuses a WAL that holds it instead of
    /// misreading it; checkpoints keep their format.
    Recover(StreamId, Vote, Vec<Entry>),
    /// A copy of the live slice at the location, written by segment
    /// compaction so the slice's old segment can go. The bytes end the
    /// frame body. Local to this keeper and outside Raft; replay ignores
    /// it, since whatever a restart reads still names the old copy or a
    /// checkpoint taken after the move. Added after `Recover`, so an older
    /// keeper refuses a WAL whose unpublished suffix holds it.
    Relocate(Location, Vec<u8>),
    /// Advances the single-keeper catalog's finalized cluster feature level.
    /// Only written once an operator finalizes past V1, so N-1 binaries can
    /// still open the WAL before finalize.
    ClusterVersion(u32),
    /// The highest log ID of the stream this replica knows committed. Written
    /// lazily in rounds that run anyway, and only once the cluster finalized
    /// `CLUSTER_VERSION_LEASES`, so N-1 binaries can still open the WAL
    /// before finalize. Added after `ClusterVersion`. An operator recovery
    /// keeps the survivor's log only through it (`keeper/recovery.rs`).
    Committed(StreamId, LogId),
}

#[derive(Clone, Serialize, Deserialize)]
pub(in crate::stream::consensus) struct CatalogEntry {
    pub genesis: Genesis,
    pub contacts: BTreeSet<uuid::Uuid>,
    pub staged: Option<Stage>,
}

impl CatalogEntry {
    pub fn ordered_contacts(&self) -> Vec<Uuid> {
        let mut seen = BTreeSet::new();
        self.staged
            .iter()
            .flat_map(|stage| stage.target.into_iter().chain(stage.old))
            .chain(self.genesis.voters)
            .chain(self.contacts.iter().copied())
            .filter(|id| seen.insert(*id))
            .take(MAX_CONTACTS)
            .collect()
    }

    fn bound_contacts(&mut self) {
        self.contacts = self.ordered_contacts().into_iter().collect();
    }
}

#[derive(Clone)]
pub(super) struct State {
    pub(super) genesis: BTreeMap<StreamId, Genesis>,
    pub(super) catalog: BTreeMap<StreamId, CatalogEntry>,
    pub(super) logs: BTreeMap<StreamId, Log>,
    pub(super) cluster_version: u32,
}

impl Default for State {
    fn default() -> Self {
        Self {
            genesis: BTreeMap::new(),
            catalog: BTreeMap::new(),
            logs: BTreeMap::new(),
            cluster_version: crate::stream::consensus::CLUSTER_VERSION_V1,
        }
    }
}

impl State {
    fn apply(&mut self, record: Record) -> io::Result<()> {
        match record {
            Record::Register(genesis) => {
                if let Some(current) = self.genesis.get(&genesis.stream) {
                    if current != &genesis {
                        return Err(invalid("stream genesis changed"));
                    }
                } else {
                    let stream = genesis.stream;
                    self.genesis.insert(stream, genesis);
                    self.logs.insert(stream, Log::default());
                }
            }
            Record::Claim(genesis) => {
                if let Some(current) = self.catalog.get(&genesis.stream) {
                    if current.genesis != genesis {
                        return Err(invalid("conflicting catalog claim"));
                    }
                } else {
                    let contacts = genesis.voters.into_iter().collect();
                    self.catalog.insert(
                        genesis.stream,
                        CatalogEntry {
                            genesis,
                            contacts,
                            staged: None,
                        },
                    );
                }
            }
            Record::Stage(stage) => {
                let entry = self
                    .catalog
                    .get_mut(&stage.stream)
                    .ok_or_else(|| invalid("missing catalog entry"))?;
                entry.staged = Some(stage);
                entry.bound_contacts();
            }
            Record::Contacts(stream, contacts) => {
                let entry = self
                    .catalog
                    .get_mut(&stream)
                    .ok_or_else(|| invalid("missing catalog entry"))?;
                entry.contacts.extend(contacts);
                entry.bound_contacts();
            }
            Record::Vote(stream, vote) => {
                let log = self.log_mut(stream)?;
                if log.vote.is_some_and(|old| !(old <= vote)) {
                    return Err(invalid("persisted vote regressed"));
                }
                log.vote = Some(vote);
            }
            Record::Append(stream, entries) => {
                let log = self.log_mut(stream)?;
                if let Some(first) = entries.first() {
                    let first = first.log_id.index;
                    if log.purged.is_some_and(|purged| first <= purged.index)
                        || first
                            > log
                                .entries
                                .last_key_value()
                                .map(|(&index, _)| index.saturating_add(1))
                                .or_else(|| log.purged.map(|id| id.index.saturating_add(1)))
                                .unwrap_or(0)
                        || !entries.windows(2).all(|pair| {
                            pair[0].log_id.index.checked_add(1) == Some(pair[1].log_id.index)
                        })
                    {
                        return Err(invalid("non-contiguous Raft append"));
                    }
                    log.entries.split_off(&first);
                    log.segments.split_off(&first);
                    log.entries
                        .extend(entries.into_iter().map(|entry| (entry.log_id.index, entry)));
                    if log.committed.is_some_and(|known| {
                        known.index >= first
                            && log
                                .entries
                                .get(&known.index)
                                .is_none_or(|entry| entry.log_id != known)
                    }) {
                        log.committed = None;
                    }
                }
            }
            Record::Recover(stream, vote, entries) => {
                if self
                    .genesis
                    .get(&stream)
                    .is_some_and(|genesis| genesis.immutable)
                {
                    return Err(invalid("recovery would rewrite an immutable history"));
                }
                self.apply(Record::Vote(stream, vote))?;
                self.apply(Record::Append(stream, entries))?;
            }
            Record::Relocate(..) => (),
            Record::Committed(stream, committed) => {
                let log = self.log_mut(stream)?;
                if log
                    .committed
                    .is_none_or(|known| known.index < committed.index)
                {
                    log.committed = Some(committed);
                }
            }
            Record::Truncate(stream, since) => {
                let log = self.log_mut(stream)?;
                if log.purged.is_some_and(|id| id.index >= since) {
                    return Err(invalid("truncation overlaps purged log"));
                }
                log.entries.split_off(&since);
                log.segments.split_off(&since);
                // Raft never truncates a committed entry. A frame that names
                // one anyway no longer describes this log.
                if log.committed.is_some_and(|known| known.index >= since) {
                    log.committed = None;
                }
            }
            Record::Purge(stream, through) => {
                let log = self.log_mut(stream)?;
                if log.purged.is_some_and(|id| id.index > through.index) {
                    return Err(invalid("purged index regressed"));
                }
                log.entries.retain(|&index, _| index > through.index);
                log.segments.retain(|&index, _| index > through.index);
                log.purged = Some(through);
            }
            Record::Owned(generation, record) => {
                if self.log_mut(record.stream())?.ownership.generation() != Some(generation) {
                    return Err(ownership::stale());
                }
                self.apply(*record)?;
            }
            Record::Ownership(stream, change) => {
                if matches!(&change, Change::Recover(_))
                    && self
                        .genesis
                        .get(&stream)
                        .is_some_and(|genesis| genesis.immutable)
                {
                    return Err(invalid(
                        "recovery staging would rewrite an immutable history",
                    ));
                }
                let log = self.log_mut(stream)?;
                let has_cut = |cut: LogId| {
                    log.purged == Some(cut)
                        || log.snapshot.is_some_and(|snapshot| snapshot.log_id == cut)
                        || log
                            .entries
                            .get(&cut.index)
                            .is_some_and(|entry| entry.log_id == cut)
                };
                if log.ownership.apply(change, has_cut)? {
                    log.snapshot = None;
                    log.purged = None;
                    log.committed = None;
                    log.entries.clear();
                    log.segments.clear();
                }
            }
            Record::Snapshot(stream, snapshot) => {
                let log = self.log_mut(stream)?;
                if log.snapshot.is_some_and(|previous| {
                    previous.log_id.index > snapshot.log_id.index
                        || (previous.log_id.index == snapshot.log_id.index
                            && previous.log_id != snapshot.log_id)
                }) {
                    return Err(invalid("selected snapshot regressed"));
                }
                log.snapshot = Some(snapshot);
            }
            Record::ClusterVersion(version) => {
                if version < self.cluster_version
                    || version > crate::stream::consensus::CLUSTER_VERSION_CURRENT
                {
                    return Err(invalid("cluster feature level regressed or unsupported"));
                }
                self.cluster_version = version;
            }
        }
        Ok(())
    }

    fn check_hard_state(&self) -> io::Result<()> {
        for log in self.logs.values() {
            let last = log
                .entries
                .last_key_value()
                .map(|(_, entry)| entry.log_id)
                .max(log.purged)
                .max(log.snapshot.map(|snapshot| snapshot.log_id));
            if last.is_some_and(|id| {
                id.leader_id.term > log.vote.map_or(0, |vote| vote.leader_id().term)
            }) {
                return Err(invalid("WAL lacks durable term or vote for its log"));
            }
        }
        Ok(())
    }

    fn log_mut(&mut self, stream: StreamId) -> io::Result<&mut Log> {
        self.logs
            .get_mut(&stream)
            .ok_or_else(|| invalid("missing registered stream"))
    }

    fn scopes(&self, scopes: &BTreeSet<StreamId>) -> Self {
        Self {
            genesis: scopes
                .iter()
                .filter_map(|id| self.genesis.get(id).map(|genesis| (*id, genesis.clone())))
                .collect(),
            catalog: scopes
                .iter()
                .filter_map(|id| self.catalog.get(id).map(|catalog| (*id, catalog.clone())))
                .collect(),
            logs: scopes
                .iter()
                .filter_map(|id| self.logs.get(id).map(|log| (*id, log.clone())))
                .collect(),
            cluster_version: self.cluster_version,
        }
    }

    fn scope_ids(&self) -> BTreeSet<StreamId> {
        self.genesis
            .keys()
            .chain(self.catalog.keys())
            .copied()
            .collect()
    }

    /// Applies `record` and stages its frame. Returns the move of a
    /// relocated slice, which takes effect once the round is durable.
    fn apply_indexed(
        &mut self,
        record: Record,
        wal: &mut Segmented,
        objects: &Objects,
    ) -> io::Result<Option<(Location, Location)>> {
        if let Record::Owned(generation, scoped) = &record
            && self.log_mut(scoped.stream())?.ownership.generation() != Some(*generation)
        {
            return Err(ownership::stale());
        }
        let payload = match &record {
            Record::Owned(_, scoped) => scoped.as_ref(),
            _ => &record,
        };
        if let Record::Purge(stream, through) = payload {
            let log = self.log_mut(*stream)?;
            if !log.snapshot.is_some_and(|selected| {
                selected.log_id == *through || selected.log_id.index > through.index
            }) || log
                .purged
                .is_some_and(|previous| previous.index == through.index && previous != *through)
            {
                return Err(invalid("purge lacks an exact covered WAL cut"));
            }
        }
        if let Record::Append(stream, entries) | Record::Recover(stream, _, entries) = payload
            && let Some(first) = entries.first()
        {
            let log = self.log_mut(*stream)?;
            let prefix = log.entries.range(..first.log_id.index).count();
            if prefix.saturating_add(entries.len()) > segmented::MAX_SUFFIX {
                return Err(invalid("WAL append exceeds its accepted suffix geometry"));
            }
        }
        let mut staged = wal.stage(&record, objects)?;
        let slices = staged.slices.take();
        let moved = staged.moved.take();
        if let Err(error) = self.apply(record) {
            wal.discard(staged);
            return Err(error);
        }
        if let Some((stream, slices)) = slices {
            self.log_mut(stream)?.segments.extend(slices);
        }
        Ok(moved)
    }
}

impl Record {
    fn entries(&self) -> Option<&[Entry]> {
        match self {
            Self::Append(_, entries) | Self::Recover(_, _, entries) => Some(entries),
            Self::Owned(_, inner) => inner.entries(),
            _ => None,
        }
    }

    fn append_count(&self) -> usize {
        match self {
            Self::Owned(_, inner) => inner.append_count(),
            Self::Append(_, entries) | Self::Recover(_, _, entries) => entries.len(),
            _ => 0,
        }
    }

    fn tickets(&self, tickets: &mut Vec<(StreamId, Uuid)>) {
        match self {
            Self::Owned(_, record) => record.tickets(tickets),
            Self::Append(scope, entries) => {
                tickets.extend(entries.iter().filter_map(|entry| match &entry.payload {
                    openraft::EntryPayload::Normal(Command::Admitted(ticket, _)) => {
                        Some((*scope, *ticket))
                    }
                    _ => None,
                }));
            }
            _ => (),
        }
    }

    fn stream(&self) -> StreamId {
        match self {
            Self::Register(genesis) | Self::Claim(genesis) => genesis.stream,
            Self::Stage(stage) => stage.stream,
            Self::ClusterVersion(_) => StreamId(0),
            Self::Owned(_, record) => record.stream(),
            Self::Vote(stream, _)
            | Self::Append(stream, _)
            | Self::Truncate(stream, _)
            | Self::Purge(stream, _)
            | Self::Snapshot(stream, _)
            | Self::Contacts(stream, _)
            | Self::Recover(stream, ..)
            | Self::Committed(stream, _)
            | Self::Ownership(stream, _) => *stream,
            Self::Relocate(from, _) => from.scope,
        }
    }
}

fn allocation(record: &Record) -> io::Result<u64> {
    let bytes = bincode::serialized_size(record).map_err(io::Error::other)?;
    let entries = record.append_count();
    if bytes > MAX_WORK_BYTES || entries > MAX_APPEND_ENTRIES {
        return Err(invalid("WAL work exceeds its batch geometry"));
    }
    Ok(bytes.saturating_add(WAL_METADATA_BYTES + entries as u64 * MAX_ENTRY_OVERHEAD))
}

fn append_allocation(entries: &[Entry]) -> io::Result<u64> {
    let bytes = bincode::serialized_size(entries).map_err(io::Error::other)?;
    // Record/ownership variants, stream and framing fit in the extra block.
    Ok(bytes.saturating_add(WAL_METADATA_BYTES + MAX_ENTRY_OVERHEAD * (entries.len() as u64 + 1)))
}

struct Work {
    record: Record,
    done: oneshot::Sender<io::Result<()>>,
    _space: Option<Reservation>,
    follower: bool,
    /// A leader's own application append, whose queue wait and WAL time
    /// feed the commit stage timers.
    application: bool,
    queued: std::time::Instant,
}

enum Message {
    Write(Work),
    /// Writes the noted commit indexes if no round carried them lately, or
    /// at once with a reply.
    Flush(Option<oneshot::Sender<io::Result<()>>>),
    #[cfg(test)]
    Checkpoint(oneshot::Sender<io::Result<()>>),
    Shutdown,
}

#[derive(Clone)]
pub(in crate::stream::consensus) struct Disk {
    state: Arc<RwLock<State>>,
    work: mpsc::Sender<Message>,
    maintenance: mpsc::Sender<Message>,
    covered: mpsc::Sender<Message>,
    control: mpsc::Sender<Message>,
    replication: mpsc::Sender<Message>,
    healthy: Arc<AtomicBool>,
    watchdog: Arc<super::watchdog::Watchdog>,
    inflight: Arc<parking_lot::Mutex<BTreeMap<StreamId, Arc<super::inflight::Inflight>>>>,
    /// Finalized cluster feature level gating new on-disk formats and commands.
    write_version: Arc<AtomicU32>,
    noted: Arc<Noted>,
    stopped: Arc<tokio::sync::Mutex<Option<oneshot::Receiver<io::Result<()>>>>>,
    media_lock: Weak<File>,
    pub path: Arc<PathBuf>,
    #[cfg(test)]
    pub(in crate::stream::consensus) trace: Option<crate::stream::consensus::trace::Node>,
    /// The incarnation of the installed media, new at each installation.
    pub incarnation: Uuid,
    pub space: Space,
    pub(super) objects: Objects,
    pub(in crate::stream::consensus) metrics: Arc<crate::stream::consensus::metrics::Metrics>,
    pub quarantine: QuarantineStore,
    #[cfg(test)]
    replica_fault: Arc<parking_lot::Mutex<Option<(StreamId, ReplicaFault)>>>,
    #[cfg(test)]
    wal_delay_ms: Arc<std::sync::atomic::AtomicU64>,
}

#[cfg(test)]
pub(in crate::stream::consensus) enum ReplicaFault {
    PartialSegment,
    FailedSync,
    BeforeSelection,
    AfterSelection,
    BeforeSettlement {
        entered: oneshot::Sender<()>,
        resume: std::sync::mpsc::Receiver<()>,
    },
    /// Fails the next round that holds a local write of the scope, at the
    /// given WAL cut.
    Interrupt(u8),
    /// Holds the next round that holds a local write of the scope before its
    /// data write until `resume` answers: true finishes the round, false fails
    /// it before its boundary, as a crash before the sync returned would.
    Hold {
        entered: oneshot::Sender<()>,
        resume: std::sync::mpsc::Receiver<bool>,
    },
}

impl Disk {
    pub fn open(enrollment: Enrollment) -> io::Result<Self> {
        Self::open_tuned(enrollment, Tuning::default())
    }

    /// Offline salvage on a stopped keeper: walks past damaged WAL spans,
    /// durably quarantines affected streams, and publishes a clean boundary.
    pub fn salvage(enrollment: Enrollment) -> io::Result<SalvageReport> {
        let quarantine = enrollment.quarantine_store()?;
        let (media, _lock, opened) = enrollment.open()?;
        let path = media.data().to_path_buf();
        let space = Space::new(path.clone())?;
        let objects = Objects::open(&path)?;
        if let Opened::Legacy(_) = opened {
            return Err(invalid(
                "salvage requires the segmented WAL format; migrate before salvaging",
            ));
        }
        Segmented::salvage(&media, &objects, &space, &quarantine)
    }

    fn open_tuned(enrollment: Enrollment, tuning: Tuning) -> io::Result<Self> {
        let quarantine = enrollment.quarantine_store()?;
        let (media, lock, opened) = enrollment.open()?;
        let keeper_id = media.keeper();
        let path = media.data().to_path_buf();
        let space = Space::new(path.clone())?;
        let objects = Objects::open(&path)?;
        for stream in quarantine.streams().keys() {
            objects.protect(*stream);
        }
        if let Opened::Legacy(boundary) = opened {
            Segmented::migrate(&media, boundary, &objects, &space)?;
        }
        let (wal, state) = Segmented::open(&media, &objects, tuning)?;
        let incarnation = media.incarnation();
        #[cfg(test)]
        let trace = crate::stream::consensus::trace::Node::open(&path, keeper_id, incarnation);
        #[cfg(test)]
        let writer_trace = trace.clone();
        drop(media);
        let initial_version = state.cluster_version;
        let state = Arc::new(RwLock::new(state));
        let (work, incoming) = mpsc::channel(MAX_ROUND_RECORDS);
        let (maintenance, housekeeping) = mpsc::channel(MAINTENANCE_QUEUE);
        let (covered, reclaim) = mpsc::channel(8);
        let (control, peer) = mpsc::channel(64);
        let (replication, follower) = mpsc::channel(REPLICATION_QUEUE);
        let healthy = Arc::new(AtomicBool::new(true));
        let write_version = Arc::new(AtomicU32::new(initial_version));
        let writer_healthy = healthy.clone();
        let writer_version = write_version.clone();
        let noted = Arc::new(Noted::default());
        let writer_noted = noted.clone();
        let watchdog = super::watchdog::Watchdog::new();
        watchdog.spawn(
            healthy.clone(),
            super::watchdog::MAX_ROUND_DURATION,
            super::watchdog::exit_on_stall,
        )?;
        let (finished, stopped) = oneshot::channel();
        let writer_watchdog = watchdog.clone();
        let writer_state = state.clone();
        let writer_objects = objects.clone();
        let writer_space = space.clone();
        let metrics = Arc::new(crate::stream::consensus::metrics::Metrics::new());
        let writer_metrics = metrics.clone();
        #[cfg(test)]
        let replica_fault = Arc::new(parking_lot::Mutex::new(None));
        #[cfg(test)]
        let writer_fault = replica_fault.clone();
        #[cfg(test)]
        let wal_delay_ms = Arc::new(std::sync::atomic::AtomicU64::new(0));
        #[cfg(test)]
        let writer_delay = wal_delay_ms.clone();
        let lock = Arc::new(lock);
        let media_lock = Arc::downgrade(&lock);
        std::thread::Builder::new()
            .name("logkeeper-raft-wal".into())
            .spawn(move || {
                let result = run(
                    wal,
                    &writer_state,
                    Queues {
                        peer,
                        housekeeping,
                        reclaim,
                        follower,
                        incoming,
                        next: 0,
                    },
                    &writer_objects,
                    &writer_space,
                    &writer_healthy,
                    &writer_version,
                    &writer_noted,
                    &writer_watchdog,
                    &writer_metrics,
                    #[cfg(test)]
                    &writer_fault,
                    #[cfg(test)]
                    &writer_delay,
                    #[cfg(test)]
                    writer_trace.as_ref(),
                );
                drop(lock);
                if let Err(error) = &result {
                    tracing::error!(
                        keeper = %keeper_id,
                        error = %error,
                        "consensus WAL stopped"
                    );
                }
                let _ = finished.send(result);
            })?;
        spawn_committed_flush(
            maintenance.downgrade(),
            Arc::downgrade(&noted),
            Arc::downgrade(&write_version),
        )?;
        Ok(Self {
            state,
            work,
            maintenance,
            covered,
            control,
            replication,
            healthy,
            watchdog,
            inflight: Arc::default(),
            write_version,
            noted,
            stopped: Arc::new(tokio::sync::Mutex::new(Some(stopped))),
            media_lock,
            path: Arc::new(path),
            #[cfg(test)]
            trace,
            incarnation,
            space,
            objects,
            metrics,
            quarantine,
            #[cfg(test)]
            replica_fault,
            #[cfg(test)]
            wal_delay_ms,
        })
    }

    pub fn healthy(&self) -> bool {
        self.healthy.load(Ordering::Acquire)
    }

    /// Keeps this media exclusively open until the service has stopped its
    /// listeners and Raft groups, even if the WAL writer fails first.
    pub fn hold_media_lock(&self) -> io::Result<Arc<File>> {
        self.media_lock
            .upgrade()
            .ok_or_else(|| super::super::invalid("keeper media lock was released"))
    }

    /// Whether the media is healthy and keeps up with its WAL rounds.
    pub fn responsive(&self) -> bool {
        self.healthy() && self.watchdog.responsive()
    }

    /// Whether the media is near its slow-round gate, when background work
    /// should wait.
    pub fn near_slow(&self) -> bool {
        self.watchdog.near_slow()
    }

    /// Resolves once a WAL round runs past the slow-round limit.
    pub async fn slowed(&self) {
        self.watchdog.slowed().await;
    }

    /// Marks the media slow for `hold`, as a slow WAL round would.
    #[cfg(test)]
    pub fn mark_slow(&self, hold: std::time::Duration) {
        self.watchdog.mark_slow(hold);
    }

    /// Durably quarantines `stream` in the enrollment registry and protects
    /// its objects and segments from reaping until cleared.
    pub fn quarantine_stream(&self, stream: StreamId, reason: &str) {
        self.objects.protect(stream);
        if let Err(error) = self.quarantine.mark(stream, reason) {
            tracing::error!(
                stream = %crate::stream::consensus::logging::stream_uuid(stream),
                error = %error,
                "could not persist a quarantine marker"
            );
        }
    }

    /// Clears a durable quarantine marker for `stream`.
    pub fn clear_quarantine(&self, stream: StreamId) -> io::Result<bool> {
        // Objects stay protected until the copy opens again and pins them.
        self.quarantine.clear(stream)
    }

    pub fn is_quarantined(&self, stream: StreamId) -> bool {
        self.quarantine.contains(stream)
    }

    pub fn quarantined_streams(&self) -> BTreeMap<StreamId, String> {
        self.quarantine.streams()
    }

    /// Finalized cluster feature level gating new on-disk formats and commands.
    pub fn cluster_version(&self) -> u32 {
        self.write_version
            .load(Ordering::Acquire)
            .max(self.state.read().cluster_version)
    }

    /// Advances the keeper's observed finalized cluster feature level monotonically.
    pub fn set_write_version(&self, version: u32) {
        let clamped = version.min(crate::stream::consensus::CLUSTER_VERSION_CURRENT);
        let _ = self.write_version.fetch_max(clamped, Ordering::AcqRel);
    }

    /// Whether the finalized cluster feature level allows writing a format or
    /// command requiring `required`.
    pub fn write_version_allows(&self, required: u32) -> bool {
        decisions::write_version_allows(self.cluster_version(), required)
    }

    /// Notes that `stream`'s replica of `generation` knows it committed
    /// through `committed`. The WAL writes it lazily (`Record::Committed`).
    pub fn note_committed(&self, stream: StreamId, generation: u64, committed: LogId) {
        let mut noted = self.noted.lock();
        let slot = noted.entry(stream).or_insert((generation, committed));
        if slot.0 != generation || slot.1.index < committed.index {
            *slot = (generation, committed);
        }
    }

    /// Writes the noted commit indexes now, in a round of their own if no
    /// other write is queued. Only once leases are finalized.
    #[cfg(test)]
    pub async fn flush_committed(&self) -> io::Result<()> {
        let (done, reply) = oneshot::channel();
        self.maintenance
            .send(Message::Flush(Some(done)))
            .await
            .map_err(io::Error::other)?;
        reply.await.map_err(io::Error::other)?
    }

    #[cfg(test)]
    pub async fn checkpoint_now(&self) -> io::Result<()> {
        let (done, reply) = oneshot::channel();
        self.work
            .send(Message::Checkpoint(done))
            .await
            .map_err(io::Error::other)?;
        reply.await.map_err(io::Error::other)?
    }

    #[cfg(test)]
    pub fn set_wal_delay(&self, delay: std::time::Duration) {
        self.wal_delay_ms
            .store(delay.as_millis() as u64, Ordering::Relaxed);
    }

    #[cfg(test)]
    pub fn fail_replication_at(&self, scope: StreamId, fault: ReplicaFault) {
        *self.replica_fault.lock() = Some((scope, fault));
    }

    /// Fails the next local write of `scope` at WAL cut `cut`.
    #[cfg(test)]
    pub fn interrupt_next(&self, scope: StreamId, cut: u8) {
        *self.replica_fault.lock() = Some((scope, ReplicaFault::Interrupt(cut)));
    }

    pub async fn write(&self, record: Record) -> io::Result<()> {
        let space = self.space.reserve(allocation(&record)?)?;
        self.enqueue(&self.work, record, Some(space), false).await
    }

    pub async fn protocol(&self, record: Record) -> io::Result<()> {
        if record.entries().is_some_and(|entries| {
            has_application_entries(entries)
                || bincode::serialized_size(entries)
                    .map_or(true, |size| size > Lane::Control.frame_limit())
        }) {
            return Err(invalid(
                "application entries or oversized metadata on the protocol WAL lane",
            ));
        }
        let bytes = allocation(&record)?;
        let reserve = self.space.protocol(bytes)?;
        self.enqueue(&self.control, record, Some(reserve), false)
            .await
    }

    pub async fn application(&self, record: Record) -> io::Result<()> {
        allocation(&record)?;
        self.submit_work(&self.work, record, None, false, true)
            .await?
            .await
            .map_err(io::Error::other)?
    }

    /// Queues an application write and returns at once; the receiver
    /// resolves once it is durable. Writes queued here land in order.
    pub async fn submit_application(
        &self,
        record: Record,
    ) -> io::Result<oneshot::Receiver<io::Result<()>>> {
        allocation(&record)?;
        self.submit_work(&self.work, record, None, false, true)
            .await
    }

    /// The leader appends of `stream` still in flight.
    pub fn inflight(&self, stream: StreamId) -> Arc<super::inflight::Inflight> {
        self.inflight.lock().entry(stream).or_default().clone()
    }

    pub async fn maintenance(&self, record: Record) -> io::Result<()> {
        let bytes = allocation(&record)?;
        let reserve = self.space.maintenance(bytes)?;
        self.enqueue(&self.maintenance, record, Some(reserve), false)
            .await
    }

    pub async fn covered(&self, record: Record) -> io::Result<()> {
        let reserve = self.space.covered(allocation(&record)?)?;
        self.enqueue(&self.covered, record, Some(reserve), false)
            .await
    }

    pub(super) fn reserve_replication(
        &self,
        scope: StreamId,
        id: Uuid,
        entries: &[Entry],
    ) -> Result<Reservation, Admission> {
        let bytes = append_allocation(entries).map_err(|_| Admission::Space)?;
        self.space
            .ordinary_slots(scope, id, FOLLOWER_SUFFIX_LIMIT, bytes, || {
                self.log(scope, |log| {
                    let tip = log
                        .entries
                        .last_key_value()
                        .map(|(&index, _)| index)
                        .or_else(|| log.purged.map(|cut| cut.index));
                    let added = entries
                        .iter()
                        .filter(|entry| tip.is_none_or(|index| entry.log_id.index > index))
                        .count();
                    (log.entries.len(), added)
                })
            })
    }

    pub(super) async fn replicate(&self, record: Record, reserve: Reservation) -> io::Result<()> {
        if reserve
            .ticket()
            .is_none_or(|(scope, _)| scope != record.stream())
        {
            return Err(invalid("replication ticket is outside its WAL scope"));
        }
        self.enqueue(&self.replication, record, Some(reserve), true)
            .await
    }

    async fn enqueue(
        &self,
        queue: &mpsc::Sender<Message>,
        record: Record,
        space: Option<Reservation>,
        follower: bool,
    ) -> io::Result<()> {
        self.submit(queue, record, space, follower)
            .await?
            .await
            .map_err(io::Error::other)?
    }

    async fn submit(
        &self,
        queue: &mpsc::Sender<Message>,
        record: Record,
        space: Option<Reservation>,
        follower: bool,
    ) -> io::Result<oneshot::Receiver<io::Result<()>>> {
        self.submit_work(queue, record, space, follower, false)
            .await
    }

    /// `application` marks a leader's own application append, which the
    /// commit stage timers follow through its WAL round.
    async fn submit_work(
        &self,
        queue: &mpsc::Sender<Message>,
        record: Record,
        space: Option<Reservation>,
        follower: bool,
        application: bool,
    ) -> io::Result<oneshot::Receiver<io::Result<()>>> {
        let (done, reply) = oneshot::channel();
        queue
            .send(Message::Write(Work {
                record,
                done,
                _space: space,
                follower,
                application,
                queued: std::time::Instant::now(),
            }))
            .await
            .map_err(io::Error::other)?;
        Ok(reply)
    }

    pub fn protect_objects(&self, stream: StreamId) {
        self.objects.protect(stream);
    }

    pub fn unprotect_objects(&self, stream: StreamId) {
        self.objects.unprotect(stream);
    }

    /// Sealed segments before the published checkpoint, other than the
    /// newest, whose live slices hold under `share` percent of their bytes
    /// and that only those slices hold, least live first.
    pub fn cold_segments(&self, share: u64) -> Vec<u64> {
        self.objects.cold_segments(1, share)
    }

    /// The streams whose WAL suffix still holds entries in segment `id`;
    /// a snapshot and purge would free them without copying.
    pub fn suffix_owners(&self, id: u64) -> BTreeSet<StreamId> {
        let state = self.state.read();
        state
            .logs
            .iter()
            .filter(|(_, log)| {
                log.segments.values().any(|slice| {
                    matches!(slice.reference(), super::objects::Reference::Segment(at) if at.segment == id)
                })
            })
            .map(|(stream, _)| *stream)
            .collect()
    }

    /// Copies the live slices of segment `id` to the active segment, grouped
    /// by stream, up to `budget` bytes, through the maintenance lane. Every
    /// holder reads the copies once their round is durable. Suspended, with
    /// nothing copied, unless ordinary writes keep room for twice the
    /// batch. Returns the bytes copied.
    pub async fn relocate_segment(&self, id: u64, budget: u64) -> io::Result<u64> {
        let mut slices = self
            .objects
            .slices_in(id)
            .into_iter()
            // A slice only checkpoints hold dies at the next one.
            .filter(|slice| slice.needed(1))
            .filter_map(|slice| match slice.reference() {
                super::objects::Reference::Segment(at) => Some((at, slice)),
                super::objects::Reference::Object(_) => None,
            })
            .collect::<Vec<_>>();
        slices.sort_by_key(|(at, _)| (at.scope, at.offset));
        let mut total = 0u64;
        slices.retain(|(at, _)| {
            let keep = total == 0 || total + at.len <= budget;
            if keep {
                total += at.len;
            }
            keep
        });
        if slices.is_empty() {
            return Ok(0);
        }
        let room = total.saturating_mul(2) + WAL_METADATA_BYTES;
        if !self.space.clear_of_ordinary(room) {
            return Ok(0);
        }
        let _space = self.space.maintenance(total + WAL_METADATA_BYTES)?;
        let records = tokio::task::spawn_blocking(move || {
            slices
                .into_iter()
                .map(|(at, slice)| Ok(Record::Relocate(at, slice.read()?)))
                .collect::<io::Result<Vec<_>>>()
        })
        .await??;
        let writes = records
            .into_iter()
            .map(|record| self.enqueue(&self.maintenance, record, None, false));
        for result in futures::future::join_all(writes).await {
            result?;
        }
        Ok(total)
    }

    /// Releases segments held for streams this keeper no longer holds.
    pub fn release_moved_of_detached(&self) {
        for scope in self.objects.moved_scopes() {
            if !self.installed(scope) {
                self.objects.release_moved(scope, u64::MAX);
            }
        }
    }

    /// Streams whose selected snapshot may still name segments their slices
    /// left; a rebuilt snapshot releases them.
    pub fn moved_scopes(&self) -> Vec<StreamId> {
        self.objects.moved_scopes()
    }

    /// How much of each segment before the published checkpoint is live.
    pub fn segment_usage(&self) -> super::objects::Usage {
        self.objects.usage()
    }

    pub fn enable_reaping(&self) {
        self.objects.enable_reaping();
    }

    pub fn disable_reaping(&self) {
        self.objects.disable_reaping();
    }

    pub async fn reap_objects(&self) -> io::Result<()> {
        let objects = self.objects.clone();
        tokio::task::spawn_blocking(move || objects.reap()).await?
    }

    pub async fn shutdown(&self) -> io::Result<()> {
        self.disable_reaping();
        if let Some(stopped) = self.stopped.lock().await.take() {
            let _ = self.work.send(Message::Shutdown).await;
            stopped.await.map_err(io::Error::other)??;
        }
        Ok(())
    }

    pub fn ownership(&self, scope: StreamId) -> Option<Ownership> {
        self.state
            .read()
            .logs
            .get(&scope)
            .map(|log| log.ownership.clone())
    }

    pub fn current_generation(&self, scope: StreamId) -> Option<u64> {
        self.state
            .read()
            .logs
            .get(&scope)
            .and_then(|log| log.ownership.generation())
    }

    pub fn installed(&self, scope: StreamId) -> bool {
        self.state
            .read()
            .logs
            .get(&scope)
            .is_some_and(|log| log.ownership.installed())
    }

    pub fn detached(&self, from: Option<StreamId>) -> Vec<(StreamId, Option<u64>)> {
        use std::ops::Bound::{Excluded, Unbounded};
        let state = self.state.read();
        state
            .logs
            .range((from.map_or(Unbounded, Excluded), Unbounded))
            .take(32)
            .map(|(&scope, log)| (scope, log.ownership.detached().first().copied()))
            .collect()
    }

    pub fn genesis(&self, stream: StreamId) -> Option<Genesis> {
        self.state.read().genesis.get(&stream).cloned()
    }

    pub fn streams(&self) -> Vec<Genesis> {
        self.state.read().genesis.values().cloned().collect()
    }

    pub(super) fn next_log_scope(&self, after: Option<StreamId>) -> Option<StreamId> {
        use std::ops::Bound::{Excluded, Unbounded};

        self.state
            .read()
            .logs
            .range((after.map_or(Unbounded, Excluded), Unbounded))
            .next()
            .map(|(&scope, _)| scope)
    }

    pub fn suffix_len(&self, stream: StreamId) -> usize {
        self.state
            .read()
            .logs
            .get(&stream)
            .map_or(0, |log| log.entries.len())
    }

    pub fn check_placement(&self, stream: StreamId, placement: &Placement) -> io::Result<()> {
        let state = self.state.read();
        if !placement.structural_genesis(&state.genesis[&stream])
            || state.logs[&stream]
                .entries
                .values()
                .any(|entry| match &entry.payload {
                    openraft::EntryPayload::Membership(membership) => {
                        !placement.structural_membership(stream, membership)
                    }
                    openraft::EntryPayload::Normal(command) => match command.body() {
                        Command::Stage(stage) | Command::StageOwned(stage) => {
                            !placement.structural_stage(stage) || stage.stream != stream
                        }
                        Command::Recover(stage) | Command::RecoverRecorded { stage, .. } => {
                            !placement.structural_stage(stage)
                                || stage.stream != stream
                                || !stage.recovery()
                        }
                        Command::Admitted(..) => true,
                        _ => false,
                    },
                    _ => false,
                })
        {
            return Err(invalid("persisted stream placement is invalid"));
        }
        Ok(())
    }

    pub fn catalog(&self, stream: StreamId) -> Option<CatalogEntry> {
        self.state.read().catalog.get(&stream).cloned()
    }

    /// Every entry of the single-keeper catalog, which a replicated catalog
    /// imports once.
    pub fn catalog_entries(&self) -> Vec<CatalogEntry> {
        self.state.read().catalog.values().cloned().collect()
    }

    /// What an operator recovery needs from this keeper's log of `stream`.
    pub fn recovery_point(&self, stream: StreamId) -> RecoveryPoint {
        let noted = self.noted.lock().get(&stream).copied();
        self.log(stream, |log| {
            // A running keeper also knows what it noted and has not written.
            let noted = noted
                .filter(|(generation, id)| {
                    log.ownership.generation() == Some(*generation)
                        && log
                            .entries
                            .get(&id.index)
                            .is_some_and(|entry| entry.log_id == *id)
                })
                .map(|(_, id)| id);
            let committed = [log.durable_committed(), noted]
                .into_iter()
                .flatten()
                .max_by_key(|id| id.index);
            let vote_term = log.vote.map_or(0, |vote| vote.leader_id().term);
            let last = log.entries.last_key_value().map(|(_, entry)| entry.log_id);
            let tip = last.or(log.purged);
            let snapshot = log.snapshot.map(|selected| selected.log_id);
            let log_term = [last, log.purged, snapshot]
                .into_iter()
                .flatten()
                .map(|id| id.leader_id.term)
                .max()
                .unwrap_or(0);
            // An earlier run wrote the recovery when the log ends with its
            // entry and membership, alone in the survivor's vote term.
            let mut tail = log.entries.values().rev();
            let written = match (tail.next(), tail.next(), tail.next()) {
                (Some(membership), Some(recover), before)
                    if recover.log_id.leader_id.term == vote_term
                        && membership.log_id.leader_id.term == vote_term
                        && before.is_none_or(|entry| entry.log_id.leader_id.term < vote_term)
                        && matches!(membership.payload, openraft::EntryPayload::Membership(_)) =>
                {
                    match &recover.payload {
                        openraft::EntryPayload::Normal(
                            Command::Recover(stage) | Command::RecoverRecorded { stage, .. },
                        ) => Some(stage.clone()),
                        _ => None,
                    }
                }
                _ => None,
            };
            RecoveryPoint {
                vote_term,
                log_term,
                tip,
                committed,
                snapshot_ahead: snapshot
                    .is_some_and(|snapshot| tip.is_none_or(|tip| snapshot.index > tip.index)),
                written,
            }
        })
    }

    pub(super) fn log<T>(&self, stream: StreamId, read: impl FnOnce(&Log) -> T) -> T {
        read(&self.state.read().logs[&stream])
    }

    pub(super) fn maybe_log<T>(&self, stream: StreamId, read: impl FnOnce(&Log) -> T) -> Option<T> {
        self.state.read().logs.get(&stream).map(read)
    }
}

/// The survivor's log as an operator recovery sees it.
pub(in crate::stream::consensus) struct RecoveryPoint {
    pub vote_term: u64,
    /// The highest term of the last entry, purge cut or selected snapshot.
    pub log_term: u64,
    pub tip: Option<LogId>,
    /// The highest log ID this keeper knows committed: durably, from its
    /// `Record::Committed` frames, snapshot and purge cut, and, while it
    /// runs, what it noted since. Never past `tip`.
    pub committed: Option<LogId>,
    /// The selected snapshot covers entries past the log's tip.
    pub snapshot_ahead: bool,
    /// The stage of a recovery an earlier run already wrote.
    pub written: Option<Stage>,
}

struct Queues {
    peer: mpsc::Receiver<Message>,
    housekeeping: mpsc::Receiver<Message>,
    reclaim: mpsc::Receiver<Message>,
    follower: mpsc::Receiver<Message>,
    incoming: mpsc::Receiver<Message>,
    next: usize,
}

impl Queues {
    fn recv(&mut self) -> Option<Message> {
        if let Some(message) = self.try_recv() {
            return Some(message);
        }
        let (lane, message) = futures::executor::block_on(async {
            tokio::select! {
                biased;
                Some(message) = self.peer.recv() => Some((0, message)),
                Some(message) = self.reclaim.recv() => Some((1, message)),
                Some(message) = self.follower.recv() => Some((2, message)),
                Some(message) = self.incoming.recv() => Some((3, message)),
                Some(message) = self.housekeeping.recv() => Some((4, message)),
                else => None,
            }
        })?;
        self.next = decisions::after(lane);
        Some(message)
    }

    fn try_recv(&mut self) -> Option<Message> {
        let lanes = [
            &mut self.peer,
            &mut self.reclaim,
            &mut self.follower,
            &mut self.incoming,
            &mut self.housekeeping,
        ];
        for step in 0..decisions::LANES {
            let lane = decisions::probe(self.next, step);
            if let Ok(message) = lanes[lane].try_recv() {
                self.next = decisions::after(lane);
                return Some(message);
            }
        }
        None
    }
}

#[allow(clippy::too_many_arguments)]
fn run(
    mut wal: Segmented,
    state: &RwLock<State>,
    mut queues: Queues,
    objects: &Objects,
    space: &Space,
    health: &AtomicBool,
    write_version: &AtomicU32,
    noted: &Noted,
    watchdog: &super::watchdog::Watchdog,
    metrics: &crate::stream::consensus::metrics::Metrics,
    #[cfg(test)] replica_fault: &parking_lot::Mutex<Option<(StreamId, ReplicaFault)>>,
    #[cfg(test)] wal_delay_ms: &std::sync::atomic::AtomicU64,
    #[cfg(test)] trace: Option<&crate::stream::consensus::trace::Node>,
) -> io::Result<()> {
    let _gate = CloseGate(health);
    let result = rounds(
        &mut wal,
        state,
        &mut queues,
        objects,
        space,
        write_version,
        noted,
        watchdog,
        metrics,
        #[cfg(test)]
        replica_fault,
        #[cfg(test)]
        wal_delay_ms,
        #[cfg(test)]
        trace,
    );
    wal.finish();
    result
}

#[allow(clippy::too_many_arguments)]
fn rounds(
    wal: &mut Segmented,
    state: &RwLock<State>,
    queues: &mut Queues,
    objects: &Objects,
    space: &Space,
    write_version: &AtomicU32,
    noted: &Noted,
    watchdog: &super::watchdog::Watchdog,
    metrics: &crate::stream::consensus::metrics::Metrics,
    #[cfg(test)] replica_fault: &parking_lot::Mutex<Option<(StreamId, ReplicaFault)>>,
    #[cfg(test)] wal_delay_ms: &std::sync::atomic::AtomicU64,
    #[cfg(test)] trace: Option<&crate::stream::consensus::trace::Node>,
) -> io::Result<()> {
    let mut finish = false;
    // When the last round with frames committed.
    let mut last_round = std::time::Instant::now();
    while let Some(message) = queues.recv() {
        let mut round = Vec::new();
        let mut flushed = Vec::new();
        match message {
            Message::Write(first) => round.push(first),
            // A round ran lately and the next one carries the noted indexes.
            Message::Flush(None) if last_round.elapsed() < COMMITTED_FLUSH / 2 => continue,
            Message::Flush(done) => flushed.extend(done),
            #[cfg(test)]
            Message::Checkpoint(done) => {
                let version = write_version.load(Ordering::Acquire);
                let result = wal.checkpoint_now_versioned(&state.read(), objects, space, version);
                let _ = done.send(result);
                continue;
            }
            // The last round carries what was noted since the one before.
            Message::Shutdown => finish = true,
        }
        let round_start = std::time::Instant::now();
        let _round = watchdog.begin();
        let mut bytes = 0;
        if let Some(first) = round.first() {
            bytes += bincode::serialized_size(&first.record).map_err(io::Error::other)?;
        }
        #[cfg(test)]
        let mut checkpoint_waiters = Vec::new();
        while !finish && round.len() < MAX_ROUND_RECORDS && bytes < MAX_ROUND_BYTES as u64 {
            match queues.try_recv() {
                Some(Message::Write(work)) => {
                    bytes += bincode::serialized_size(&work.record).map_err(io::Error::other)?;
                    round.push(work);
                }
                // This round carries the noted indexes anyway.
                Some(Message::Flush(done)) => flushed.extend(done),
                #[cfg(test)]
                Some(Message::Checkpoint(done)) => checkpoint_waiters.push(done),
                Some(Message::Shutdown) => {
                    finish = true;
                    break;
                }
                None => break,
            }
        }
        let scopes = round
            .iter()
            .map(|work| work.record.stream())
            .collect::<BTreeSet<_>>();
        let mut working = state.read().scopes(&scopes);
        let mut replies = Vec::with_capacity(round.len());
        let mut changed = BTreeSet::new();
        let mut added = 0;
        let mut tickets = Vec::new();
        let mut moves = Vec::new();
        let mut applications = 0u64;
        #[cfg(test)]
        let mut before_settlement = None;
        #[cfg(test)]
        let mut held = None;
        #[cfg(test)]
        let mut events = Vec::new();
        for mut work in round {
            if work.application {
                applications += 1;
                metrics
                    .commit_stage_queue
                    .observe(round_start.saturating_duration_since(work.queued));
            }
            let scope = work.record.stream();
            let new = !wal.contains_scope(scope) && !changed.contains(&scope);
            if new && wal.scope_count() + added >= segmented::MAX_SCOPES {
                let _ = work.done.send(Err(io::Error::new(
                    io::ErrorKind::StorageFull,
                    "keeper WAL scope limit reached",
                )));
                continue;
            }
            let saved = tickets.len();
            if work.follower {
                let reservation = work._space.as_mut().expect("admitted follower append");
                tickets.push(reservation.ticket().expect("follower slot ticket"));
                // A failed or uncertain write disables this WAL. Keep its
                // ticket until reopen can verify the boundary and allocations.
                reservation.hold_until_reconciled(true);
                #[cfg(test)]
                if let Some((_, fault)) = replica_fault.lock().take_if(|(id, fault)| {
                    *id == scope
                        && !matches!(
                            fault,
                            ReplicaFault::Interrupt(_) | ReplicaFault::Hold { .. }
                        )
                }) {
                    match fault {
                        ReplicaFault::PartialSegment => wal.interrupt(6),
                        ReplicaFault::FailedSync => wal.interrupt(5),
                        ReplicaFault::BeforeSelection => wal.interrupt(2),
                        ReplicaFault::AfterSelection => wal.interrupt(3),
                        gate @ ReplicaFault::BeforeSettlement { .. } => {
                            before_settlement = Some(gate)
                        }
                        ReplicaFault::Interrupt(_) | ReplicaFault::Hold { .. } => {
                            unreachable!("local write fault")
                        }
                    }
                }
            } else {
                work.record.tickets(&mut tickets);
                #[cfg(test)]
                match replica_fault.lock().take_if(|(id, fault)| {
                    *id == scope
                        && matches!(
                            fault,
                            ReplicaFault::Interrupt(_) | ReplicaFault::Hold { .. }
                        )
                }) {
                    Some((_, ReplicaFault::Interrupt(cut))) => wal.interrupt(cut),
                    Some((_, ReplicaFault::Hold { entered, resume })) => {
                        held = Some((entered, resume))
                    }
                    _ => (),
                }
            }
            #[cfg(test)]
            let observed = trace.and_then(|_| crate::stream::consensus::trace::wal(&work.record));
            #[cfg(test)]
            let generation = trace.and_then(|_| {
                working
                    .logs
                    .get(&scope)
                    .and_then(|log| log.ownership.generation())
            });
            match working.apply_indexed(work.record, wal, objects) {
                Ok(moved) => {
                    #[cfg(test)]
                    if trace.is_some() {
                        events.extend(observed);
                        if working.logs.get(&scope).is_some_and(|log| {
                            generation != log.ownership.generation()
                                && log.entries.is_empty()
                                && log.snapshot.is_none()
                                && log.purged.is_none()
                        }) {
                            events.push(crate::stream::consensus::trace::event(
                                "ResetCopy",
                                scope,
                                serde_json::json!({}),
                            ));
                        }
                    }
                    moves.extend(moved);
                    changed.insert(scope);
                    added += usize::from(new);
                    replies.push((work.done, work._space));
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    tickets.truncate(saved);
                    if let Some(reservation) = work._space.as_mut() {
                        reservation.hold_until_reconciled(false);
                    }
                    let _ = work.done.send(Err(error));
                }
                Err(error) => return Err(error),
            }
        }
        let committed = if decisions::write_version_allows(
            write_version
                .load(Ordering::Acquire)
                .max(working.cluster_version),
            crate::stream::consensus::CLUSTER_VERSION_LEASES,
        ) {
            stage_committed(noted, &state.read(), &working, wal, objects)?
        } else {
            Vec::new()
        };
        #[cfg(test)]
        if let Some((entered, resume)) = held {
            let _ = entered.send(());
            if !resume
                .recv_timeout(std::time::Duration::from_secs(30))
                .unwrap_or(true)
            {
                wal.interrupt(2);
            }
        }
        if !changed.is_empty() || !committed.is_empty() {
            #[cfg(test)]
            {
                let delay = wal_delay_ms.load(Ordering::Relaxed);
                if delay > 0 {
                    std::thread::sleep(std::time::Duration::from_millis(delay));
                }
            }
            let round_records = replies.len() as u64;
            let round_bytes = wal.commit(
                objects,
                &changed,
                metrics,
                #[cfg(test)]
                || {
                    if let Some(trace) = trace {
                        events.extend(committed.iter().filter_map(|&(stream, _, id)| {
                            crate::stream::consensus::trace::wal(&Record::Committed(stream, id))
                        }));
                        trace.batch(events);
                    }
                },
            )?;
            last_round = std::time::Instant::now();
            metrics.wal_round_records.observe(round_records);
            metrics.wal_round_bytes.observe(round_bytes);
            let round_duration = round_start.elapsed();
            metrics.wal_round_duration.observe(round_duration);
            metrics
                .commit_stage_wal
                .observe_n(round_duration, applications);
            // The copies are durable: every holder reads them from now on.
            // Their old segments stay for the checkpoint and the selected
            // snapshots that may still name them.
            for (from, to) in moves {
                match objects.relocate(from, to) {
                    Ok(Some(left)) => {
                        // Only a selected snapshot can still name the old
                        // copy once the checkpoint moves on.
                        if working
                            .logs
                            .get(&from.scope)
                            .is_some_and(|log| log.snapshot.is_some())
                        {
                            objects.hold_moved(from.scope, left.clone());
                        }
                        wal.retire(left);
                    }
                    Ok(None) => (),
                    // The copy stays unused; the old one is still read.
                    Err(error) => tracing::warn!(error = %error, "kept a WAL slice in place"),
                }
            }
            #[cfg(test)]
            if let Some(ReplicaFault::BeforeSettlement { entered, resume }) = before_settlement {
                let _ = entered.send(());
                let _ = resume.recv_timeout(std::time::Duration::from_secs(10));
            }
            space.settle(&tickets, || {
                let mut installed = state.write();
                installed.genesis.extend(working.genesis);
                installed.catalog.extend(working.catalog);
                installed.logs.extend(working.logs);
                installed.cluster_version = installed.cluster_version.max(working.cluster_version);
                for (stream, generation, id) in &committed {
                    if let Some(log) = installed.logs.get_mut(stream)
                        && log.ownership.generation() == Some(*generation)
                        && log.committed.is_none_or(|known| known.index < id.index)
                    {
                        log.committed = Some(*id);
                    }
                }
            });
            let mut pending = noted.lock();
            for (stream, generation, id) in committed {
                if pending.get(&stream) == Some(&(generation, id)) {
                    pending.remove(&stream);
                }
            }
            drop(pending);
            let _ = write_version.fetch_max(working.cluster_version, Ordering::AcqRel);
            wal.maybe_checkpoint(
                &state.read(),
                objects,
                space,
                write_version.load(Ordering::Acquire),
            );
        }
        for (reply, _reservation) in replies {
            let _ = reply.send(Ok(()));
        }
        for done in flushed {
            let _ = done.send(Ok(()));
        }
        #[cfg(test)]
        for done in checkpoint_waiters {
            let version = write_version.load(Ordering::Acquire);
            let _ = done.send(wal.checkpoint_now_versioned(&state.read(), objects, space, version));
        }
        if finish {
            break;
        }
    }
    Ok(())
}

/// Stages a `Record::Committed` frame for each noted commit index the WAL
/// does not hold yet, once the log holds the entry it names. Forgets notes
/// that no longer apply: a stream gone or moved to another generation, an
/// index already durable, or an entry the log holds otherwise.
fn stage_committed(
    noted: &Noted,
    installed: &State,
    working: &State,
    wal: &mut Segmented,
    objects: &Objects,
) -> io::Result<Vec<(StreamId, u64, LogId)>> {
    let mut pending = noted.lock();
    let mut staged = Vec::new();
    let mut stale = Vec::new();
    for (&stream, &(generation, id)) in pending.iter() {
        let Some(log) = working
            .logs
            .get(&stream)
            .or_else(|| installed.logs.get(&stream))
        else {
            stale.push(stream);
            continue;
        };
        if log.ownership.generation() != Some(generation)
            || log.committed.is_some_and(|known| known.index >= id.index)
        {
            stale.push(stream);
            continue;
        }
        let holds = log
            .entries
            .get(&id.index)
            .is_some_and(|entry| entry.log_id == id)
            || log.purged.is_some_and(|purged| purged.index >= id.index)
            || log
                .snapshot
                .is_some_and(|snapshot| snapshot.log_id.index >= id.index);
        if !holds {
            // A leader can learn an entry committed before its own write of
            // it lands; it is noted again once it does if it is not now.
            if log
                .entries
                .last_key_value()
                .is_some_and(|(&last, _)| last >= id.index)
            {
                stale.push(stream);
            }
            continue;
        }
        let record = Record::Owned(generation, Box::new(Record::Committed(stream, id)));
        wal.stage(&record, objects)?;
        staged.push((stream, generation, id));
    }
    for stream in stale {
        pending.remove(&stream);
    }
    Ok(staged)
}

/// Asks the WAL writer every `COMMITTED_FLUSH`, while commit indexes wait
/// and leases are finalized, to write them if no round did meanwhile. Stops
/// once the WAL does.
fn spawn_committed_flush(
    lane: mpsc::WeakSender<Message>,
    noted: Weak<Noted>,
    version: Weak<AtomicU32>,
) -> io::Result<()> {
    std::thread::Builder::new()
        .name("logkeeper-raft-commit".into())
        .spawn(move || {
            loop {
                std::thread::sleep(COMMITTED_FLUSH);
                let (Some(noted), Some(version), Some(lane)) =
                    (noted.upgrade(), version.upgrade(), lane.upgrade())
                else {
                    return;
                };
                if noted.lock().is_empty()
                    || !decisions::write_version_allows(
                        version.load(Ordering::Acquire),
                        crate::stream::consensus::CLUSTER_VERSION_LEASES,
                    )
                {
                    continue;
                }
                if let Err(mpsc::error::TrySendError::Closed(_)) =
                    lane.try_send(Message::Flush(None))
                {
                    return;
                }
            }
        })?;
    Ok(())
}

struct CloseGate<'a>(&'a AtomicBool);

impl Drop for CloseGate<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

#[cfg(test)]
fn write_record(file: &mut impl std::io::Write, record: &Record) -> io::Result<u64> {
    let body = super::super::encode(record)?;
    file.write_all(&(body.len() as u32).to_be_bytes())?;
    file.write_all(&crc32fast::hash(&body).to_be_bytes())?;
    file.write_all(&body)?;
    Ok((8 + body.len()) as u64)
}

fn recover(file: impl Read) -> io::Result<(State, u64)> {
    let mut file = BufReader::new(file);
    let mut state = State::default();
    let mut offset = 0;
    loop {
        let mut header = [0; 8];
        match file.read_exact(&mut header) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => break,
            Err(error) => return Err(error),
        }
        let size = u32::from_be_bytes(header[..4].try_into().unwrap());
        let checksum = u32::from_be_bytes(header[4..].try_into().unwrap());
        if size == 0 || u64::from(size) > super::super::MAX_MESSAGE {
            return Err(invalid("invalid Raft WAL frame length"));
        }
        let mut body = vec![0; size as usize];
        match file.read_exact(&mut body) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => break,
            Err(error) => return Err(error),
        }
        if crc32fast::hash(&body) != checksum {
            return Err(invalid("Raft WAL checksum changed"));
        }
        state.apply(decode(&body)?)?;
        offset += 8 + u64::from(size);
    }
    Ok((state, offset))
}
