//! One writer serializes durable mutations across all stream groups.

use crate::stream::consensus::decisions;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, BufReader, Read},
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use journal_contract::StreamId;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};

use tokio::sync::{mpsc, oneshot};
use uuid::Uuid;

mod indexed;
use indexed::{Indexed, store_entry};
#[cfg(test)]
mod tests;

use super::{
    Entry, Genesis, Log, LogId, Vote,
    media::{Boundary, Enrollment, Media},
    objects::Objects,
    snapshot::Selected,
    space::{Admission, Reservation, Space, WAL_METADATA_BYTES},
};
use crate::stream::{
    consensus::{
        Stage, decode, encode, invalid,
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
const FOLLOWER_SUFFIX_LIMIT: usize = indexed::MAX_SUFFIX - 16;
const MAX_CONTACTS: usize = 128;

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

#[derive(Clone, Default)]
struct State {
    genesis: BTreeMap<StreamId, Genesis>,
    catalog: BTreeMap<StreamId, CatalogEntry>,
    logs: BTreeMap<StreamId, Log>,
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
                }
            }
            Record::Truncate(stream, since) => {
                let log = self.log_mut(stream)?;
                if log.purged.is_some_and(|id| id.index >= since) {
                    return Err(invalid("truncation overlaps purged log"));
                }
                log.entries.split_off(&since);
                log.segments.split_off(&since);
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
        }
    }

    fn apply_indexed(&mut self, record: Record, objects: &Objects) -> io::Result<()> {
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
        let segments = if let Record::Append(stream, entries) = payload {
            if let Some(first) = entries.first() {
                let log = self.log_mut(*stream)?;
                let prefix = log.entries.range(..first.log_id.index).count();
                if prefix.saturating_add(entries.len()) > indexed::MAX_SUFFIX {
                    return Err(invalid("WAL append exceeds its accepted suffix geometry"));
                }
            }
            let segments = entries
                .iter()
                .map(|entry| Ok((entry.log_id.index, store_entry(objects, *stream, entry)?)))
                .collect::<io::Result<Vec<_>>>()?;
            Some((*stream, segments))
        } else {
            None
        };
        self.apply(record)?;
        if let Some((stream, segments)) = segments {
            self.log_mut(stream)?.segments.extend(segments);
        }
        Ok(())
    }
}

impl Record {
    fn entries(&self) -> Option<&[Entry]> {
        match self {
            Self::Append(_, entries) => Some(entries),
            Self::Owned(_, inner) => inner.entries(),
            _ => None,
        }
    }

    fn append_count(&self) -> usize {
        match self {
            Self::Owned(_, inner) => inner.append_count(),
            Self::Append(_, entries) => entries.len(),
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
            Self::Owned(_, record) => record.stream(),
            Self::Vote(stream, _)
            | Self::Append(stream, _)
            | Self::Truncate(stream, _)
            | Self::Purge(stream, _)
            | Self::Snapshot(stream, _)
            | Self::Contacts(stream, _)
            | Self::Ownership(stream, _) => *stream,
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
}

enum Message {
    Write(Work),
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
    stopped: Arc<tokio::sync::Mutex<Option<oneshot::Receiver<io::Result<()>>>>>,
    pub path: Arc<PathBuf>,
    pub space: Space,
    pub(super) objects: Objects,
    #[cfg(test)]
    replica_fault: Arc<parking_lot::Mutex<Option<(StreamId, ReplicaFault)>>>,
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
}

impl Disk {
    pub fn open(enrollment: Enrollment) -> io::Result<Self> {
        let (media, lock, boundary) = enrollment.open()?;
        let path = media.data().to_path_buf();
        let space = Space::new(path.clone())?;
        let objects = Objects::open(&path)?;
        let (indexed, state) = Indexed::open(&media, boundary, &objects, &space)?;
        let selected = media.wal(indexed.generation());
        for item in fs::read_dir(&path)? {
            let item = item?;
            if item.path() != selected
                && item
                    .file_name()
                    .to_str()
                    .is_some_and(|name| name.starts_with("raft-") && name.ends_with(".wal"))
            {
                fs::remove_file(item.path())?;
            }
        }
        let state = Arc::new(RwLock::new(state));
        let (work, incoming) = mpsc::channel(MAX_ROUND_RECORDS);
        let (maintenance, housekeeping) = mpsc::channel(MAINTENANCE_QUEUE);
        let (covered, reclaim) = mpsc::channel(8);
        let (control, peer) = mpsc::channel(64);
        let (replication, follower) = mpsc::channel(REPLICATION_QUEUE);
        let healthy = Arc::new(AtomicBool::new(true));
        let writer_healthy = healthy.clone();
        let (finished, stopped) = oneshot::channel();
        let writer_state = state.clone();
        let writer_objects = objects.clone();
        let writer_space = space.clone();
        #[cfg(test)]
        let replica_fault = Arc::new(parking_lot::Mutex::new(None));
        #[cfg(test)]
        let writer_fault = replica_fault.clone();
        std::thread::Builder::new()
            .name("logkeeper-raft-wal".into())
            .spawn(move || {
                let result = run(
                    indexed,
                    &media,
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
                    #[cfg(test)]
                    &writer_fault,
                );
                drop(lock);
                if let Err(error) = &result {
                    eprintln!("logkeeper consensus WAL stopped: {error}");
                }
                let _ = finished.send(result);
            })?;
        Ok(Self {
            state,
            work,
            maintenance,
            covered,
            control,
            replication,
            healthy,
            stopped: Arc::new(tokio::sync::Mutex::new(Some(stopped))),
            path: Arc::new(path),
            space,
            objects,
            #[cfg(test)]
            replica_fault,
        })
    }

    pub fn healthy(&self) -> bool {
        self.healthy.load(Ordering::Acquire)
    }

    #[cfg(test)]
    pub fn fail_replication_at(&self, scope: StreamId, fault: ReplicaFault) {
        *self.replica_fault.lock() = Some((scope, fault));
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
        self.enqueue(&self.work, record, None, false).await
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
        let (done, reply) = oneshot::channel();
        queue
            .send(Message::Write(Work {
                record,
                done,
                _space: space,
                follower,
            }))
            .await
            .map_err(io::Error::other)?;
        reply.await.map_err(io::Error::other)?
    }

    pub fn protect_objects(&self, stream: StreamId) {
        self.objects.protect(stream);
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

    pub fn check_placement(&self, stream: StreamId, placement: &Placement) -> io::Result<()> {
        let state = self.state.read();
        if !placement.genesis(&state.genesis[&stream])
            || state.logs[&stream]
                .entries
                .values()
                .any(|entry| match &entry.payload {
                    openraft::EntryPayload::Membership(membership) => {
                        !placement.membership(membership)
                    }
                    openraft::EntryPayload::Normal(command) => match command.body() {
                        Command::Stage(stage) | Command::StageOwned(stage) => {
                            !placement.stage(stage) || stage.stream != stream
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

    pub(super) fn log<T>(&self, stream: StreamId, read: impl FnOnce(&Log) -> T) -> T {
        read(&self.state.read().logs[&stream])
    }
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

fn run(
    mut wal: Indexed,
    media: &Media,
    state: &RwLock<State>,
    mut queues: Queues,
    objects: &Objects,
    space: &Space,
    health: &AtomicBool,
    #[cfg(test)] replica_fault: &parking_lot::Mutex<Option<(StreamId, ReplicaFault)>>,
) -> io::Result<()> {
    let _gate = CloseGate(health);
    let mut finish = false;
    while let Some(Message::Write(first)) = queues.recv() {
        let mut round = vec![first];
        let mut bytes = 0;
        while round.len() < 16 {
            bytes += bincode::serialized_size(&round.last().unwrap().record)
                .map_err(io::Error::other)?;
            if bytes >= MAX_ROUND_BYTES as u64 {
                break;
            }
            match queues.try_recv() {
                Some(Message::Write(work)) => round.push(work),
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
        #[cfg(test)]
        let mut before_settlement = None;
        for mut work in round {
            let scope = work.record.stream();
            let new = !wal.contains_scope(scope) && !changed.contains(&scope);
            if new && wal.scope_count() + added >= indexed::MAX_SCOPES {
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
                if let Some((_, fault)) = replica_fault.lock().take_if(|(id, _)| *id == scope) {
                    match fault {
                        ReplicaFault::PartialSegment => objects.interrupt_next_put(scope),
                        ReplicaFault::FailedSync => wal.interrupt(5),
                        ReplicaFault::BeforeSelection => wal.interrupt(2),
                        ReplicaFault::AfterSelection => wal.interrupt(3),
                        gate @ ReplicaFault::BeforeSettlement { .. } => {
                            before_settlement = Some(gate)
                        }
                    }
                }
            } else {
                work.record.tickets(&mut tickets);
            }
            match working.apply_indexed(work.record, objects) {
                Ok(()) => {
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
        if !changed.is_empty() {
            wal.commit(media, objects, &working, &changed)?;
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
            });
        }
        for (reply, _reservation) in replies {
            let _ = reply.send(Ok(()));
        }
        if finish {
            break;
        }
    }
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
    let body = encode(record)?;
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
