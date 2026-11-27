mod file;
pub(super) mod index;

use std::{
    collections::{BTreeMap, VecDeque},
    fs::{self, File, OpenOptions},
    io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::{
        Arc, Weak,
        atomic::{AtomicBool, Ordering},
    },
};

use bincode::Options;
use futures::TryStreamExt;
use journal_contract::{Epoch, JournalError, Lsn, Page, StreamId};
use openraft::{
    EntryPayload, OptionalSend, RaftSnapshotBuilder,
    storage::{EntryResponder, RaftStateMachine},
};
use parking_lot::{Mutex, RwLock};
use serde::{Deserialize, Serialize};
use tokio::sync::watch;

pub(in crate::stream::consensus) use file::SnapshotFile;
use file::{Open as WireFile, Temporary};

use super::{
    Disk, Record,
    media::{hex, sha256},
};
use crate::stream::timed::EVIDENCE_BYTES;
use crate::stream::{
    consensus::{
        Configuration, Entry, Genesis, LogId, MAX_MESSAGE, MAX_RECORD, Membership, RaftTypes,
        SnapshotMeta, Stage, invalid, options, ownership,
        placement::Placement,
        state::{Command, MAX_RETAINED_RECORDS, Outcome, Payload, State, TIMED_RECORD},
    },
    keeper::durability::{sync_directory, sync_file},
};

/// The applied state a timed original stage depends on.
pub(in crate::stream::consensus) struct TimedView {
    pub head: Lsn,
    pub floor: Lsn,
    pub writer: Option<(super::super::Fence, String)>,
    pub configuration: Configuration,
    pub changing: bool,
    pub fits: bool,
}

#[derive(Clone, Default, Serialize, Deserialize)]
struct Image {
    applied: Option<LogId>,
    membership: Membership,
    configuration: Option<Configuration>,
    previous_revision: Option<u64>,
    stage: Option<Stage>,
    #[serde(skip)]
    stage_intent: bool,
    state: State,
}

impl Image {
    fn stage(
        &mut self,
        stage: Stage,
        genesis: &Genesis,
        placement: &Placement,
        explicit: bool,
    ) -> Outcome {
        let head = match self.state.head() {
            Ok(head) => head,
            Err(error) => return Outcome::Refused(error),
        };
        if self.configuration
            == Some(Configuration {
                revision: stage.source,
                voters: stage.old,
            })
            && self.membership.membership().get_joint_config().len() == 1
            && stage.stream == genesis.stream
            && placement.structural_stage(&stage)
        {
            self.stage = Some(stage);
            self.stage_intent = explicit;
            Outcome::Unit
        } else {
            Outcome::Refused(JournalError::Conflict { head })
        }
    }

    /// Applies an operator recovery: stages the move from the current
    /// configuration to the recovery target and fences the stream under the
    /// recovery writer. The recovered membership entry that follows it is
    /// accepted only while both hold.
    fn recover(&mut self, stage: Stage, genesis: &Genesis, placement: &Placement) -> Outcome {
        let head = match self.state.head() {
            Ok(head) => head,
            Err(error) => return Outcome::Refused(error),
        };
        if self.configuration
            != Some(Configuration {
                revision: stage.source,
                voters: stage.old,
            })
            || self.membership.membership().get_joint_config().len() != 1
            || stage.stream != genesis.stream
            || !placement.structural_stage(&stage)
            || !stage.recovery()
        {
            return Outcome::Refused(JournalError::Conflict { head });
        }
        match self.state.recover() {
            Ok(outcome) => {
                self.stage = Some(stage);
                self.stage_intent = true;
                outcome
            }
            Err(error) => Outcome::Refused(error),
        }
    }

    /// Whether `stable` may change to `target` in one step: only after an
    /// applied operator recovery staged exactly this move.
    fn recovers(
        &self,
        genesis: &Genesis,
        stable: &std::collections::BTreeSet<u128>,
        target: &std::collections::BTreeSet<u128>,
    ) -> bool {
        self.state.recovering()
            && self.stage_intent
            && self.has_stage(genesis, target)
            && self.stage.as_ref().is_some_and(|stage| {
                stage.recovery() && stable.iter().copied().eq(stage.old.map(|id| id.as_u128()))
            })
    }

    fn verify_placement(&self, placement: &Placement, genesis: &Genesis) -> io::Result<()> {
        let membership = self.membership.membership();
        let current = self
            .configuration
            .ok_or_else(|| invalid("snapshot lacks finalized placement"))?;
        let configs = membership.get_joint_config();
        if placement.structural_membership(membership)
            && placement.structural_roster(&current.voters)
            && configs.first().is_some_and(|old| {
                old.iter()
                    .copied()
                    .eq(current.voters.map(|id| id.as_u128()))
            })
            && match configs.as_slice() {
                [_] => self.stage.as_ref().is_none_or(|stage| {
                    stage.stream == genesis.stream
                        && stage.source == current.revision
                        && stage.old == current.voters
                        && placement.structural_stage(stage)
                }),
                [_, target] => self.has_stage(genesis, target),
                _ => false,
            }
        {
            Ok(())
        } else {
            Err(invalid("snapshot placement is invalid"))
        }
    }

    fn has_stage(&self, genesis: &Genesis, target: &std::collections::BTreeSet<u128>) -> bool {
        self.stage.as_ref().is_some_and(|stage| {
            stage.stream == genesis.stream
                && self.configuration
                    == Some(Configuration {
                        revision: stage.source,
                        voters: stage.old,
                    })
                && target
                    .iter()
                    .copied()
                    .eq(stage.target.map(|id| id.as_u128()))
        })
    }

    fn verify_transition(
        &self,
        membership: &openraft::Membership<u128, openraft::BasicNode>,
        placement: &Placement,
        genesis: &Genesis,
    ) -> io::Result<()> {
        let before = self.membership.membership().get_joint_config();
        let after = membership.get_joint_config();
        if placement.structural_membership(membership)
            && match (before.as_slice(), after.as_slice()) {
                ([], [new]) => new
                    .iter()
                    .copied()
                    .eq(genesis.voters.map(|id| id.as_u128())),
                ([stable], [unchanged]) => {
                    stable == unchanged || self.recovers(genesis, stable, unchanged)
                }
                ([stable], [old, new]) => stable == old && self.has_stage(genesis, new),
                ([_, target], [finalized]) => target == finalized,
                _ => false,
            }
        {
            Ok(())
        } else {
            Err(invalid("invalid committed placement transition"))
        }
    }
}

type Snapshot = openraft::type_config::alias::SnapshotOf<RaftTypes, Box<SnapshotFile>>;

#[derive(Clone)]
pub(in crate::stream::consensus) struct StateMachine {
    inner: Arc<Inner>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Selected {
    pub log_id: LogId,
    pub(super) digest: [u8; 32],
}

pub(super) fn verify_selected_file(
    file: File,
    directory: &Path,
    genesis: &Genesis,
    selected: Selected,
    objects: &super::objects::Objects,
) -> io::Result<()> {
    read_selected(file, directory, genesis, selected, objects)?;
    Ok(())
}

impl Selected {
    pub(super) fn path(self, directory: &Path) -> PathBuf {
        directory.join(format!("snapshot-{}", hex(&self.digest)))
    }
}

struct Inner {
    genesis: Genesis,
    generation: u64,
    lifetime: Arc<()>,
    placement: Placement,
    disk: Disk,
    directory: PathBuf,
    applied: RwLock<Image>,
    snapshot: Mutex<Option<ActiveSnapshot>>,
    wire: Mutex<BTreeMap<String, Weak<[u8; 32]>>>,
    publishing: tokio::sync::Mutex<()>,
    healthy: AtomicBool,
    stopped: AtomicBool,
    published: watch::Sender<Option<LogId>>,
    changed: watch::Sender<()>,
    /// The last index and time of this leader's recent durable application
    /// appends, oldest first, which time the replication commit stage.
    durable: Mutex<VecDeque<(u64, std::time::Instant)>>,
    #[cfg(test)]
    snapshot_paused: watch::Sender<bool>,
}

/// Durable appends remembered for the replication stage timer. Older ones
/// are forgotten, so a stream that never applies holds a bounded queue.
const TIMED_APPENDS: usize = 256;

#[derive(Clone)]
struct ActiveSnapshot {
    meta: SnapshotMeta,
    selected: Selected,
    image: Image,
    dependencies: index::Dependencies,
}

/// What a closed replica keeps instead of its state machine: the segments
/// its selected snapshot and applied records lie in, a hold on its
/// standalone objects (index pages, entries from before segments), its
/// lifetime and its finalized configuration. Reopening loads the image
/// again from the selected snapshot and the WAL suffix, which pins itself.
pub(in crate::stream::consensus) struct Pin {
    pub selected: Option<Selected>,
    pub finalized: Option<Configuration>,
    pub generation: u64,
    _segments: Vec<Arc<super::objects::Segment>>,
    _files: super::objects::Hold,
    _lifetime: Arc<()>,
}

impl Pin {
    pub fn lifetime(&self) -> Weak<()> {
        Arc::downgrade(&self._lifetime)
    }

    /// The segments the pin keeps.
    pub fn segments(&self) -> impl Iterator<Item = u64> + '_ {
        self._segments.iter().map(|segment| segment.id())
    }

    /// Makes the pin durable in the replica's directory, so a restart keeps
    /// the copy parked without loading its image. The mark is an N format:
    /// before the cluster version is finalized none is written, so an N-1
    /// keeper never meets one and a later N never trusts one an N-1 outran.
    /// The copy then reopens at restart, as N-1 does.
    pub fn persist(&self, disk: &Disk, stream: StreamId) -> io::Result<()> {
        if !disk.write_version_allows(crate::stream::consensus::CLUSTER_VERSION_CURRENT) {
            return Ok(());
        }
        // Segments that slices of the selected snapshot left stay named
        // until a rebuilt snapshot is selected.
        let mut segments = self.segments().collect::<Vec<_>>();
        segments.extend(disk.objects.moved_segments(stream));
        segments.sort_unstable();
        segments.dedup();
        let mark = Mark {
            selected: self.selected,
            finalized: self.finalized,
            segments,
        };
        let mut body = PARK_MARK.to_vec();
        options()
            .with_limit(MAX_MARK_BYTES)
            .serialize_into(&mut body, &mark)
            .map_err(io::Error::other)?;
        body.extend_from_slice(&crc32fast::hash(&body).to_le_bytes());
        let directory = ownership::directory(&disk.path, stream, self.generation);
        let temporary = directory.join(format!("{PARK_FILE}.tmp"));
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&temporary)?;
        file.write_all(&body)?;
        sync_file(&file)?;
        fs::rename(&temporary, directory.join(PARK_FILE))?;
        sync_directory(&directory)
    }

    /// The pin a restart restores from the park mark of `stream`'s current
    /// copy. `None` when there is no mark, or the mark was taken for another
    /// selected snapshot than the one the WAL names: the copy then reopens
    /// as usual. A mark for the selected snapshot names every segment its
    /// records lie in; the WAL suffix pins itself.
    pub fn restore(disk: &Disk, stream: StreamId) -> io::Result<Option<Self>> {
        let Some(generation) = disk
            .ownership(stream)
            .and_then(|ownership| ownership.generation())
        else {
            return Ok(None);
        };
        let current = disk.log(stream, |log| log.snapshot);
        let Some(mark) = matching_park_mark(&disk.path, stream, generation, current)? else {
            return Ok(None);
        };
        let files = disk.objects.hold(stream);
        let segments = mark
            .segments
            .into_iter()
            .map(|id| disk.objects.segment(id))
            .collect::<io::Result<_>>()?;
        Ok(Some(Self {
            selected: mark.selected,
            finalized: mark.finalized,
            generation,
            _segments: segments,
            _files: files,
            _lifetime: Arc::new(()),
        }))
    }

    /// Removes the park mark of copy `generation` of `stream`, if any.
    pub fn forget(disk: &Disk, stream: StreamId, generation: u64) -> io::Result<()> {
        let directory = ownership::directory(&disk.path, stream, generation);
        match fs::remove_file(directory.join(PARK_FILE)) {
            Ok(()) => sync_directory(&directory),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(error),
        }
    }
}

const PARK_FILE: &str = "parked";
const PARK_MARK: &[u8; 8] = b"LKRPRK01";
const MAX_MARK_BYTES: u64 = 1024 * 1024;

/// A parked copy's pin on disk.
#[derive(Serialize, Deserialize)]
struct Mark {
    selected: Option<Selected>,
    finalized: Option<Configuration>,
    segments: Vec<u64>,
}

fn matching_park_mark(
    root: &Path,
    stream: StreamId,
    generation: u64,
    current: Option<Selected>,
) -> io::Result<Option<Mark>> {
    let path = ownership::directory(root, stream, generation).join(PARK_FILE);
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    let (body, crc) = bytes
        .split_last_chunk::<4>()
        .ok_or_else(|| invalid("short park mark"))?;
    if crc32fast::hash(body) != u32::from_le_bytes(*crc) || !body.starts_with(PARK_MARK) {
        return Err(invalid("park mark failed its checksum"));
    }
    let mark: Mark = options()
        .with_limit(MAX_MARK_BYTES)
        .deserialize(&body[PARK_MARK.len()..])
        .map_err(io::Error::other)?;
    let matches = match (mark.selected, current) {
        (None, None) => true,
        (Some(mark), Some(current)) => {
            mark.log_id == current.log_id && mark.digest == current.digest
        }
        _ => false,
    };
    Ok(matches.then_some(mark))
}

pub(super) fn is_parked(
    root: &Path,
    stream: StreamId,
    generation: u64,
    current: Option<Selected>,
    objects: &super::objects::Objects,
) -> bool {
    matching_park_mark(root, stream, generation, current).is_ok_and(|mark| {
        mark.is_some_and(|mark| mark.segments.iter().all(|&id| objects.segment(id).is_ok()))
    })
}

/// Captures an applied state before handing snapshot work to a background task.
pub(in crate::stream::consensus) struct Builder {
    inner: Arc<Inner>,
    image: Image,
}

impl StateMachine {
    pub fn durable_tip(&self) -> Option<LogId> {
        self.inner.disk.log(self.inner.genesis.stream, |log| {
            log.entries
                .last_key_value()
                .map(|(_, entry)| entry.log_id)
                .or(log.purged)
        })
    }

    pub fn reserve_command(
        &self,
        command: &Command,
        ticket: uuid::Uuid,
        slots: usize,
    ) -> Result<super::space::Reservation, super::space::Admission> {
        use super::space::{Admission, WAL_METADATA_BYTES};
        let bytes = bincode::serialized_size(command).map_err(|_| Admission::Space)?;
        let disk = &self.inner.disk;
        let scope = self.inner.genesis.stream;
        disk.space.ordinary_slot(
            scope,
            ticket,
            slots,
            bytes.saturating_add(WAL_METADATA_BYTES),
            || disk.log(scope, |log| log.entries.len()),
        )
    }

    pub fn covered(&self) -> Option<LogId> {
        *self.inner.published.borrow()
    }

    pub fn suffix_len(&self) -> usize {
        self.inner
            .disk
            .log(self.inner.genesis.stream, |log| log.entries.len())
    }

    pub fn metrics(&self) -> &Arc<super::super::metrics::Metrics> {
        &self.inner.disk.metrics
    }

    /// Notes that this leader's own application append through `index`
    /// became durable now.
    pub fn appended(&self, index: u64) {
        let mut durable = self.inner.durable.lock();
        if durable.len() >= TIMED_APPENDS {
            durable.pop_front();
        }
        durable.push_back((index, std::time::Instant::now()));
    }

    /// Forgets timed appends from `index` on, which a truncation removed.
    pub fn truncated(&self, index: u64) {
        self.inner.durable.lock().retain(|(last, _)| *last < index);
    }

    pub fn retained_stats(&self) -> (u64, u64) {
        self.inner.applied.read().state.retained_stats()
    }

    pub fn is_deleted(&self) -> bool {
        self.inner.applied.read().state.is_deleted()
    }

    pub async fn open(disk: &Disk, genesis: Genesis, placement: Placement) -> io::Result<Self> {
        let root = disk.path.clone();
        let generation = disk
            .ownership(genesis.stream)
            .and_then(|owner| owner.generation())
            .ok_or_else(|| invalid("replica is detached"))?;
        let (purged, selected) = disk.log(genesis.stream, |log| (log.purged, log.snapshot));
        let disk = disk.clone();
        tokio::task::spawn_blocking(move || {
            let directory =
                crate::stream::consensus::ownership::directory(&root, genesis.stream, generation);
            fs::create_dir_all(&directory)?;
            sync_directory(&root)?;
            let (snapshot, applied) = if let Some(selected) = selected {
                let (meta, image, dependencies) = read_selected(
                    File::open(selected.path(&directory))?,
                    &directory,
                    &genesis,
                    selected,
                    &disk.objects,
                )?;
                image.verify_placement(&placement, &genesis)?;
                (
                    Some(ActiveSnapshot {
                        meta,
                        selected,
                        image: image.clone(),
                        dependencies,
                    }),
                    image,
                )
            } else {
                (None, Image::default())
            };
            if purged.is_some_and(|purged| {
                applied.applied.is_none_or(|id| {
                    id < purged
                        || id.index < purged.index
                        || (id.index == purged.index && id != purged)
                })
            }) {
                return Err(invalid("purged log lacks a durable snapshot"));
            }
            for item in fs::read_dir(&directory)? {
                let item = item?;
                if !item.file_name().to_str().is_some_and(|name| {
                    name.starts_with("incoming-")
                        || name.starts_with("building-")
                        || name.starts_with("outgoing-")
                        || (name.starts_with("snapshot-")
                            && snapshot.as_ref().is_none_or(|state| {
                                state.selected.path(&directory) != item.path()
                                    && !state.dependencies.legacy_files().iter().any(|digest| {
                                        Selected {
                                            digest: *digest,
                                            ..state.selected
                                        }
                                        .path(&directory)
                                            == item.path()
                                    })
                            }))
                }) {
                    continue;
                }
                match fs::remove_file(item.path()) {
                    Ok(()) => (),
                    Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                    Err(error) => return Err(error),
                }
            }
            let published =
                watch::channel(snapshot.as_ref().and_then(|active| active.meta.last_log_id)).0;
            Ok(Self {
                inner: Arc::new(Inner {
                    genesis,
                    generation,
                    lifetime: Arc::new(()),
                    placement,
                    disk,
                    directory,
                    applied: RwLock::new(applied),
                    snapshot: Mutex::new(snapshot),
                    wire: Mutex::default(),
                    stopped: AtomicBool::new(false),
                    healthy: AtomicBool::new(true),
                    publishing: Default::default(),
                    published,
                    changed: watch::channel(()).0,
                    durable: Mutex::default(),
                    #[cfg(test)]
                    snapshot_paused: watch::channel(false).0,
                }),
            })
        })
        .await
        .map_err(io::Error::other)?
    }

    pub fn generation(&self) -> u64 {
        self.inner.generation
    }

    pub fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// Whether this state machine is still allocated, without keeping it.
    #[cfg(test)]
    pub fn downgrade(&self) -> Weak<impl Sized + use<>> {
        Arc::downgrade(&self.inner)
    }

    /// The pins that keep what reopening needs once this state machine is
    /// dropped. Taken after the group shut down, so no later snapshot or
    /// apply can depend on anything else.
    pub fn pin(&self) -> Pin {
        let files = self.inner.disk.objects.hold(self.inner.genesis.stream);
        let mut segments = BTreeMap::new();
        let snapshot = self.inner.snapshot.lock();
        let applied = self.inner.applied.read();
        let images = snapshot
            .as_ref()
            .map(|active| &active.image)
            .into_iter()
            .chain([&*applied]);
        for image in images {
            for payload in image.state.records() {
                if let Payload::Extent { object, .. } = payload
                    && let Some(segment) = object.segment()
                {
                    segments.entry(segment.id()).or_insert(segment);
                }
            }
        }
        Pin {
            selected: snapshot.as_ref().map(|active| active.selected),
            finalized: applied.configuration,
            generation: self.inner.generation,
            _segments: segments.into_values().collect(),
            _files: files,
            _lifetime: self.inner.lifetime.clone(),
        }
    }

    pub fn lifetime(&self) -> Weak<()> {
        Arc::downgrade(&self.inner.lifetime)
    }

    pub fn suspend(&self) {
        self.inner.suspend();
    }

    pub fn quarantine_corrupt(&self, reason: &str) {
        self.inner.quarantine_corrupt(reason);
    }

    pub fn is_quarantined(&self) -> bool {
        self.inner.disk.is_quarantined(self.inner.genesis.stream)
    }

    pub fn healthy(&self) -> bool {
        self.inner.disk.healthy()
            && self.inner.healthy.load(Ordering::Acquire)
            && self
                .inner
                .disk
                .current_generation(self.inner.genesis.stream)
                == Some(self.inner.generation)
    }

    pub fn head(&self) -> journal_contract::Result<Lsn> {
        if !self.healthy() {
            return Err(if self.is_quarantined() {
                JournalError::Corrupted
            } else {
                JournalError::Unavailable
            });
        }
        self.inner.applied.read().state.head()
    }

    pub async fn page(&self, from: Lsn, limit: usize) -> journal_contract::Result<Page> {
        if self.is_quarantined() {
            return Err(JournalError::Corrupted);
        }
        if !self.healthy() {
            return Err(JournalError::Unavailable);
        }
        let page = self.inner.applied.read().state.read(from, limit)?;
        let result = if page.needs_disk() {
            tokio::task::spawn_blocking(move || page.load())
                .await
                .map_err(io::Error::other)
                .and_then(|page| page)
        } else {
            page.load()
        };
        result.map_err(|error| {
            if self.inner.fail(&error) {
                JournalError::Corrupted
            } else {
                JournalError::Unavailable
            }
        })
    }

    pub fn subscribe(&self) -> watch::Receiver<()> {
        self.inner.changed.subscribe()
    }

    pub async fn receive_snapshot(
        &self,
        digest: [u8; 32],
        meta: SnapshotMeta,
    ) -> io::Result<Box<SnapshotFile>> {
        SnapshotFile::receive(
            &self.inner.directory,
            &self.inner.disk.space,
            self.inner.lifetime.clone(),
            digest,
            meta,
        )
        .await
        .map(Box::new)
    }

    pub fn snapshot_digest(&self, meta: &SnapshotMeta) -> Option<[u8; 32]> {
        self.inner
            .wire
            .lock()
            .get(&meta.snapshot_id)
            .and_then(Weak::upgrade)
            .map(|digest| *digest)
    }

    pub async fn shutdown(&self) {
        // OpenRaft can return from shutdown with snapshot workers still running.
        // Exclude any late publication before releasing the keeper lock.
        let _publication = self.inner.publishing.lock().await;
        self.inner.stopped.store(true, Ordering::Relaxed);
    }

    pub async fn wait_for_snapshot(&self, through: LogId) -> io::Result<()> {
        // OpenRaft can enqueue a purge while a snapshot install still runs in
        // the state-machine worker. Only a published file can cover log removal.
        let mut published = self.inner.published.subscribe();
        tokio::time::timeout(
            std::time::Duration::from_secs(60),
            published.wait_for(|snapshot| {
                snapshot
                    .is_some_and(|selected| selected.index > through.index || selected == through)
            }),
        )
        .await
        .map_err(io::Error::other)?
        .map_err(io::Error::other)?;
        Ok(())
    }

    pub fn membership(&self) -> Membership {
        self.inner.applied.read().membership.clone()
    }

    pub fn placement(
        &self,
    ) -> journal_contract::Result<(Lsn, Configuration, Option<u64>, Membership)> {
        let image = self.inner.applied.read();
        Ok((
            image.state.head()?,
            image
                .configuration
                .ok_or(journal_contract::JournalError::Unavailable)?,
            image.previous_revision,
            image.membership.clone(),
        ))
    }

    /// What a timed original stage checks, read from one applied image.
    pub fn timed_view(&self, payload_len: usize) -> journal_contract::Result<TimedView> {
        if !self.healthy() {
            return Err(JournalError::Unavailable);
        }
        let image = self.inner.applied.read();
        Ok(TimedView {
            head: image.state.head()?,
            floor: image.state.retained_floor(),
            writer: image
                .state
                .writer()
                .map(|(fence, owner)| (fence, owner.to_owned())),
            configuration: image.configuration.ok_or(JournalError::Unavailable)?,
            changing: image.stage.is_some()
                || image.membership.membership().get_joint_config().len() > 1,
            fits: image
                .state
                .fits_timed(payload_len, self.inner.genesis.quota_bytes),
        })
    }

    /// The retained timed record at `at`, from the applied image.
    /// Whether a writer of `epoch` appended exactly `payloads` from `at`:
    /// the last LSN when it did, `Conflict` when it did not, and
    /// `Unavailable` when this replica cannot tell.
    pub async fn written(
        &self,
        epoch: journal_contract::Epoch,
        at: Lsn,
        payloads: Vec<bytes::Bytes>,
    ) -> journal_contract::Result<Lsn> {
        if !self.healthy() {
            return Err(JournalError::Unavailable);
        }
        let count = payloads.len() as u64;
        let (records, head) = {
            let image = self.inner.applied.read();
            (
                image.state.written(epoch, at, payloads.len())?,
                image.state.head()?,
            )
        };
        let matches = tokio::task::spawn_blocking(move || {
            records
                .iter()
                .zip(&payloads)
                .try_fold(true, |same, (record, payload)| {
                    Ok::<_, io::Error>(
                        same && record.len() == payload.len() && record.load()? == *payload,
                    )
                })
        })
        .await
        .map_err(|_| JournalError::Unavailable)?
        .map_err(|_| JournalError::Unavailable)?;
        if matches {
            Ok(Lsn(at.0 + count - 1))
        } else {
            Err(JournalError::Conflict { head })
        }
    }

    pub fn timed_record(&self, at: Lsn) -> journal_contract::Result<Payload> {
        if !self.healthy() {
            return Err(JournalError::Unavailable);
        }
        self.inner.applied.read().state.timed_record(at)
    }

    pub fn staged(&self, stage: &Stage) -> bool {
        self.inner.applied.read().stage.as_ref() == Some(stage)
    }

    pub fn staged_intent(&self, stage: &Stage) -> bool {
        let image = self.inner.applied.read();
        image.stage_intent && image.stage.as_ref() == Some(stage)
    }

    pub fn finalized(&self) -> Option<Configuration> {
        self.inner.applied.read().configuration
    }

    pub fn serves_applied_pages(&self, keeper: u128) -> bool {
        self.inner
            .applied
            .read()
            .membership
            .membership()
            .voter_ids()
            .any(|id| id == keeper)
    }

    pub fn active(&self) -> bool {
        self.healthy() && self.inner.disk.installed(self.inner.genesis.stream)
    }

    pub fn placement_proof(
        &self,
    ) -> journal_contract::Result<crate::stream::consensus::network::Proof> {
        let image = self.inner.applied.read();
        let configuration = image.configuration.ok_or(JournalError::Unavailable)?;
        let joint = image
            .membership
            .membership()
            .get_joint_config()
            .get(1)
            .map(|target| {
                let mut target = target.iter().copied().map(uuid::Uuid::from_u128);
                std::array::from_fn(|_| target.next().expect("checked joint roster"))
            });
        Ok(crate::stream::consensus::network::Proof {
            genesis: self.inner.genesis.clone(),
            configuration,
            joint,
            stage: image.stage.clone(),
        })
    }

    #[cfg(test)]
    pub fn snapshot_path(&self) -> Option<PathBuf> {
        self.inner
            .snapshot
            .lock()
            .as_ref()
            .map(|active| active.selected.path(&self.inner.directory))
    }

    /// The file holding the first retained record, and where in it the
    /// record's last byte sits.
    #[cfg(test)]
    pub fn payload_path(&self) -> Option<(PathBuf, u64)> {
        match self.inner.applied.read().state.records().next()? {
            Payload::Extent {
                object,
                offset,
                len,
                ..
            } => Some((
                object.path().to_owned(),
                object.position() + offset + u64::from(*len) - 1,
            )),
            Payload::Snapshot { .. } => None,
        }
    }

    #[cfg(test)]
    pub fn pause_snapshots(&self, pause: bool) {
        self.inner.snapshot_paused.send_replace(pause);
    }

    #[cfg(test)]
    pub fn suffix_slots(&self) -> usize {
        self.inner
            .disk
            .log(self.inner.genesis.stream, |log| log.entries.len())
    }

    #[cfg(test)]
    pub fn occupy_transfers(&self) -> Box<dyn std::any::Any + Send> {
        let mut transfers = Vec::new();
        while let Ok(mut transfer) = self.inner.disk.space.transfer() {
            transfer.grow(64 * 1024).unwrap();
            transfers.push(transfer);
        }
        assert_eq!(transfers.len(), 4);
        Box::new(transfers)
    }

    #[cfg(test)]
    pub fn applied(&self) -> Option<LogId> {
        self.inner.applied.read().applied
    }
}

impl RaftStateMachine<RaftTypes> for StateMachine {
    type SnapshotData = Box<SnapshotFile>;
    type SnapshotBuilder = Builder;

    async fn applied_state(&mut self) -> io::Result<(Option<LogId>, Membership)> {
        let image = self.inner.applied.read();
        Ok((image.applied, image.membership.clone()))
    }

    async fn apply<S>(&mut self, entries: S) -> io::Result<()>
    where
        S: futures::Stream<Item = io::Result<EntryResponder<RaftTypes>>> + Unpin + OptionalSend,
    {
        let (entries, responders): (Vec<_>, Vec<_>) =
            entries.try_collect::<Vec<_>>().await?.into_iter().unzip();
        // A leader can learn an entry is committed from its followers before
        // its own write of it lands. Applying reads the entry's WAL segment.
        if let Some(last) = entries.last() {
            self.inner
                .disk
                .inflight(self.inner.genesis.stream)
                .durable_through(last.log_id.index)
                .await?;
        }
        let started = std::time::Instant::now();
        let last = entries.last().map(|entry| entry.log_id.index);
        let may_read_snapshot = self.head().is_ok_and(|head| entries.iter().any(|entry| {
            matches!(&entry.payload, EntryPayload::Normal(command) if matches!(command.body(), Command::Append { at, .. } | Command::AppendBatch { at, .. } | Command::AppendOriginal { at, .. } if *at <= head))
        }));
        let outcomes = if may_read_snapshot {
            let inner = self.inner.clone();
            tokio::task::spawn_blocking(move || inner.apply(entries))
                .await
                .map_err(io::Error::other)
                .and_then(|outcomes| outcomes)
        } else {
            self.inner.apply(entries)
        };
        let outcomes = outcomes.inspect_err(|error| {
            self.inner.fail(error);
        })?;
        let metrics = &self.inner.disk.metrics;
        metrics.commit_stage_apply.observe(started.elapsed());
        if let Some(last) = last {
            let mut durable = self.inner.durable.lock();
            while let Some(&(index, at)) = durable.front()
                && index <= last
            {
                durable.pop_front();
                metrics
                    .commit_stage_replication
                    .observe(started.saturating_duration_since(at));
            }
        }
        let revision = self
            .inner
            .applied
            .read()
            .configuration
            .map_or(0, |configuration| configuration.revision);
        let scope = self.inner.genesis.stream;
        let disk = &self.inner.disk;
        if disk
            .ownership(scope)
            .is_some_and(|owner| owner.high_water() < revision)
        {
            disk.maintenance(Record::Ownership(
                scope,
                crate::stream::consensus::ownership::Change::Observe {
                    revision,
                    generation: self.inner.generation,
                },
            ))
            .await?;
        }
        for (responder, outcome) in responders.into_iter().zip(outcomes) {
            if let Some(responder) = responder {
                responder.send(outcome);
            }
        }
        Ok(())
    }

    async fn get_snapshot_builder(&mut self) -> Self::SnapshotBuilder {
        Builder {
            inner: self.inner.clone(),
            image: self.inner.applied.read().clone(),
        }
    }

    async fn install_snapshot(
        &mut self,
        meta: &openraft::type_config::alias::SnapshotMetaOf<RaftTypes>,
        snapshot: Box<SnapshotFile>,
    ) -> io::Result<()> {
        let inner = self.inner.clone();
        let source = inner.clone();
        let expected = meta.clone();
        let transferred = snapshot.meta().clone();
        let (file, temporary, digest) = snapshot.received().await?;
        let (meta, image, selected, temporary) = blocking(move || {
            let (stored, image) = read_image(
                file.try_clone()?,
                &source.genesis,
                digest,
                MAX_RETAINED_RECORDS as u64,
            )?;
            if stored != transferred || stored.raft() != expected {
                return Err(invalid("snapshot metadata does not match its body"));
            }
            image.verify_placement(&source.placement, &source.genesis)?;
            let selected = prepare_selection(file, &stored)?;
            if selected.digest != digest {
                return Err(invalid(
                    "incoming snapshot differs from the authenticated source selection",
                ));
            }
            Ok((stored, image, selected, temporary))
        })
        .await?;
        let _publish = inner.publishing.lock().await;
        // An installed image carries its records in its own file.
        let moved = inner.disk.objects.last_move(inner.genesis.stream);
        if inner.applied.read().applied > meta.last_log_id {
            return Err(invalid("snapshot would roll back applied state"));
        }
        inner.select(&temporary.path, selected, true).await?;
        *inner.applied.write() = image.clone();
        inner.installed(ActiveSnapshot {
            meta,
            selected,
            image,
            dependencies: index::Dependencies::legacy(selected.digest),
        });
        if let Some(moved) = moved {
            inner
                .disk
                .objects
                .release_moved(inner.genesis.stream, moved);
        }
        inner.changed.send_replace(());
        Ok(())
    }

    async fn get_current_snapshot(&mut self) -> io::Result<Option<Snapshot>> {
        Ok(self.inner.current_snapshot())
    }
}

impl Inner {
    fn suspend(&self) {
        self.healthy.store(false, Ordering::Release);
        self.changed.send_replace(());
    }

    fn quarantine_corrupt(&self, reason: &str) {
        self.disk.quarantine_stream(self.genesis.stream, reason);
        self.healthy.store(false, Ordering::Release);
        self.changed.send_replace(());
    }

    /// Takes the replica out of service after `error`. Only data that fails
    /// its checksum or does not decode (`InvalidData`) quarantines it
    /// durably; another error, such as a failed read, only suspends it until
    /// it reopens. Whether it was quarantined.
    fn fail(&self, error: &io::Error) -> bool {
        if error.kind() == io::ErrorKind::InvalidData {
            self.quarantine_corrupt(&error.to_string());
            true
        } else {
            self.suspend();
            false
        }
    }

    async fn select(&self, temporary: &Path, selected: Selected, incoming: bool) -> io::Result<()> {
        self.ensure_running()?;
        let directory = self.directory.clone();
        let temporary = temporary.to_path_buf();
        blocking(move || {
            fs::rename(temporary, selected.path(&directory))?;
            sync_directory(&directory)
        })
        .await?;
        let record = Record::Owned(
            self.generation,
            Box::new(Record::Snapshot(self.genesis.stream, selected)),
        );
        if incoming {
            self.disk.maintenance(record).await
        } else {
            self.disk.covered(record).await
        }
    }

    fn installed(&self, active: ActiveSnapshot) {
        let selected = active.selected;
        let keep = active.dependencies.legacy_files().clone();
        let previous = self.snapshot.lock().replace(active);
        self.published.send_replace(Some(selected.log_id));
        if let Some(previous) = previous {
            let mut old = previous.dependencies.legacy_files().clone();
            old.insert(previous.selected.digest);
            for digest in old
                .into_iter()
                .filter(|digest| *digest != selected.digest && !keep.contains(digest))
            {
                // An older read or transfer may still pin the inode. Unlink
                // only removes its name and available_space counts that pin.
                let path = Selected { digest, ..selected }.path(&self.directory);
                tokio::task::spawn_blocking(move || {
                    let _ = fs::remove_file(path);
                });
            }
        }
    }

    fn current_snapshot(self: &Arc<Self>) -> Option<Snapshot> {
        let active = self.snapshot.lock().clone()?;
        let meta = active.meta.clone();
        let inner = self.clone();
        let snapshot = SnapshotFile::send(meta.clone(), move || {
            let mut transfer = inner.disk.space.transfer()?;
            let metadata = options()
                .serialized_size(&(&inner.genesis, &active.meta, &active.image))
                .map_err(io::Error::other)?;
            transfer.grow(
                active
                    .image
                    .state
                    .snapshot_bytes()
                    .saturating_add(metadata)
                    .saturating_add(HEADER_BYTES),
            )?;
            let path = inner
                .directory
                .join(format!("outgoing-{}", uuid::Uuid::new_v4()));
            let mut temporary = Temporary {
                path,
                transfer,
                _pin: Some(inner.lifetime.clone()),
            };
            let mut file = OpenOptions::new()
                .create_new(true)
                .write(true)
                .read(true)
                .open(&temporary.path)?;
            write_image(
                &mut file,
                &inner.genesis,
                &active.meta,
                &active.image,
                |reason| inner.quarantine_corrupt(reason),
            )?;
            temporary.transfer.account(&file.metadata()?);
            file.rewind()?;
            let digest = sha256(&file)?;
            file.rewind()?;
            let digest = {
                let mut wire = inner.wire.lock();
                wire.retain(|_, digest| digest.strong_count() != 0);
                let digest = wire
                    .get(&active.meta.snapshot_id)
                    .and_then(Weak::upgrade)
                    .unwrap_or_else(|| Arc::new(digest));
                wire.insert(active.meta.snapshot_id.clone(), Arc::downgrade(&digest));
                digest
            };
            Ok(WireFile {
                file: tokio::fs::File::from_std(file),
                temporary,
                digest: Some(digest),
                _source: Some(Box::new(active)),
            })
        });
        Some(openraft::Snapshot {
            meta: meta.raft(),
            snapshot: Box::new(snapshot),
        })
    }

    fn ensure_running(&self) -> io::Result<()> {
        if self.stopped.load(Ordering::Relaxed) {
            Err(io::Error::other("snapshot publication stopped"))
        } else {
            Ok(())
        }
    }

    fn apply(&self, entries: Vec<Entry>) -> io::Result<Vec<Outcome>> {
        let mut image = self.applied.write();
        let mut outcomes = Vec::with_capacity(entries.len());
        for entry in entries {
            let outcome = match entry.payload {
                EntryPayload::Blank => Outcome::Unit,
                EntryPayload::Normal(command) => match command.into_body() {
                    Command::Stage(stage) => {
                        image.stage(stage, &self.genesis, &self.placement, false)
                    }
                    Command::StageOwned(stage) => {
                        image.stage(stage, &self.genesis, &self.placement, true)
                    }
                    Command::Recover(stage) => image.recover(stage, &self.genesis, &self.placement),
                    Command::Admitted(..) => return Err(invalid("nested application ticket")),
                    command => {
                        let segment = self
                            .disk
                            .log(self.genesis.stream, |log| {
                                let stored = log.entries.get(&entry.log_id.index)?;
                                if stored.log_id != entry.log_id {
                                    return None;
                                }
                                log.segments.get(&stored.log_id.index).cloned()
                            })
                            .ok_or_else(|| invalid("applied command has no durable WAL segment"))?;
                        image.state.apply(command, &self.genesis, segment)?
                    }
                },
                EntryPayload::Membership(membership) => {
                    image.verify_transition(&membership, &self.placement, &self.genesis)?;
                    if let [voters] = membership.get_joint_config().as_slice() {
                        let voters = voters
                            .iter()
                            .copied()
                            .map(uuid::Uuid::from_u128)
                            .collect::<Vec<_>>();
                        let voters = <[_; 3]>::try_from(voters)
                            .map_err(|_| invalid("invalid finalized voter configuration"))?;
                        if image
                            .configuration
                            .is_none_or(|current| current.voters != voters)
                        {
                            image.previous_revision =
                                image.configuration.map(|current| current.revision);
                            let revision = if image.stage_intent {
                                image
                                    .stage
                                    .as_ref()
                                    .and_then(|stage| stage.source.checked_add(1))
                                    .ok_or_else(|| {
                                        invalid("finalized move lacks its target revision")
                                    })?
                            } else {
                                entry.log_id.index
                            };
                            image.stage = None;
                            image.stage_intent = false;
                            image.configuration = Some(Configuration { revision, voters });
                        }
                    }
                    image.membership = Membership::new(Some(entry.log_id), membership);
                    Outcome::Unit
                }
            };
            image.applied = Some(entry.log_id);
            outcomes.push(outcome);
        }
        drop(image);
        self.changed.send_replace(());
        Ok(outcomes)
    }
}

impl RaftSnapshotBuilder<RaftTypes> for Builder {
    type SnapshotData = Box<SnapshotFile>;

    async fn build_snapshot(&mut self) -> io::Result<Snapshot> {
        #[cfg(test)]
        {
            let mut paused = self.inner.snapshot_paused.subscribe();
            paused.wait_for(|paused| !*paused).await.unwrap();
        }
        let inner = self.inner.clone();
        let source = inner.clone();
        let image = self.image.clone();
        let meta = SnapshotMeta {
            last_log_id: image.applied,
            last_membership: image.membership.clone(),
            snapshot_id: if image.stage_intent {
                format!("{STAGED_IMAGE}{}", uuid::Uuid::new_v4())
            } else {
                uuid::Uuid::new_v4().to_string()
            },
        };
        let _publish = inner.publishing.lock().await;
        let previous = inner.snapshot.lock().clone();
        // Slices this stream's selected snapshot names may have moved. A
        // rebuild then writes every page again, which the scratch for a
        // full page set covers, so the new snapshot names only their new
        // copies and the segments they left can go.
        let moved = inner.disk.objects.last_move(inner.genesis.stream);
        if moved.is_none()
            && previous
                .as_ref()
                .is_some_and(|prior| prior.meta.last_log_id >= meta.last_log_id)
        {
            return inner
                .current_snapshot()
                .ok_or_else(|| invalid("selected image disappeared"));
        }
        let previous = match previous {
            Some(prior) if moved.is_none() => prior.dependencies,
            _ => index::Dependencies::default(),
        };
        let scratch = inner.disk.space.scratch(index::SCRATCH).await?;
        let temporary = inner
            .directory
            .join(format!("building-{}", meta.snapshot_id));
        let target = temporary.clone();
        let (active, scratch) = blocking(move || {
            let mut file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&target)?;
            let dependencies = index::build(
                &mut file,
                &source.disk.objects,
                &source.genesis,
                &meta,
                &image,
                &previous,
            )?;
            let selected = prepare_selection(file, &meta)?;
            Ok((
                ActiveSnapshot {
                    meta,
                    selected,
                    image,
                    dependencies,
                },
                scratch,
            ))
        })
        .await?;
        let (reserved, _worker) = scratch;
        // Synced objects are now accounted by the filesystem. Keep the
        // serialized worker until selection, but do not book them twice.
        drop(reserved);
        inner.select(&temporary, active.selected, false).await?;
        inner.installed(active);
        if let Some(moved) = moved {
            inner
                .disk
                .objects
                .release_moved(inner.genesis.stream, moved);
        }
        crate::stream::consensus::metrics::count(&inner.disk.metrics.snapshots_built);
        inner
            .current_snapshot()
            .ok_or_else(|| invalid("built image disappeared"))
    }
}

fn prepare_selection(mut file: File, meta: &SnapshotMeta) -> io::Result<Selected> {
    let log_id = meta
        .last_log_id
        .ok_or_else(|| invalid("snapshot has no included log"))?;
    file.rewind()?;
    let digest = sha256(&file)?;
    sync_file(&file)?;
    Ok(Selected { log_id, digest })
}

fn read_selected(
    mut file: File,
    directory: &Path,
    genesis: &Genesis,
    selected: Selected,
    objects: &super::objects::Objects,
) -> io::Result<(SnapshotMeta, Image, index::Dependencies)> {
    if sha256(&file)? != selected.digest {
        return Err(invalid("snapshot does not match trusted WAL evidence"));
    }
    file.rewind()?;
    let mut magic = [0; 8];
    file.read_exact(&mut magic)?;
    file.rewind()?;
    if index::indexed(&magic) {
        return index::open(file, directory, selected, genesis, objects);
    }
    let (meta, image) = read_image(file, genesis, selected.digest, u64::MAX)?;
    if meta.last_log_id != Some(selected.log_id) {
        return Err(invalid("snapshot has the wrong included log"));
    }
    Ok((meta, image, index::Dependencies::legacy(selected.digest)))
}

/// A replica's state after applying its whole local log, including entries
/// it never saw committed. An operator recovery commits exactly that log.
pub(in crate::stream::consensus) struct Replayed {
    pub configuration: Option<Configuration>,
    pub uniform: bool,
    pub head: journal_contract::Result<Lsn>,
    pub epoch: Epoch,
}

/// Read-only inspection of one stream's snapshot and replayed suffix state.
pub(super) struct StreamStateView {
    pub snapshot_applied: Option<LogId>,
    pub applied: Option<LogId>,
    pub voters: Vec<uuid::Uuid>,
    pub joint_voters: Option<Vec<uuid::Uuid>>,
    pub learners: Vec<uuid::Uuid>,
    pub configuration: Option<Configuration>,
    pub fence: Option<(super::super::Fence, String)>,
    pub recovering: bool,
    pub head: Option<Lsn>,
    pub floor: Option<Lsn>,
    pub stream_state: &'static str,
    pub retained_records: u64,
    pub retained_bytes: u64,
}

/// Inspects a single stream's snapshot and WAL suffix strictly read-only,
/// returning `Err` if startup would quarantine the replica.
pub(super) fn inspect_stream_readonly(
    data: &Path,
    objects: &super::objects::Objects,
    genesis: &Genesis,
    log: &super::Log,
    placement: &Placement,
) -> io::Result<StreamStateView> {
    if !placement.structural_genesis(genesis)
        || log.entries.values().any(|entry| match &entry.payload {
            EntryPayload::Membership(membership) => !placement.structural_membership(membership),
            EntryPayload::Normal(command) => match command.body() {
                Command::Stage(stage) | Command::StageOwned(stage) => {
                    !placement.structural_stage(stage) || stage.stream != genesis.stream
                }
                Command::Recover(stage) => {
                    !placement.structural_stage(stage)
                        || stage.stream != genesis.stream
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
    let generation = log
        .ownership
        .generation()
        .ok_or_else(|| invalid("replica is detached"))?;
    let directory =
        crate::stream::consensus::ownership::directory(data, genesis.stream, generation);
    let mut image = if let Some(selected) = log.snapshot {
        let (_, image, _) = read_selected(
            File::open(selected.path(&directory))?,
            &directory,
            genesis,
            selected,
            objects,
        )?;
        image.verify_placement(placement, genesis)?;
        image
    } else {
        Image::default()
    };
    let snapshot_applied = image.applied;
    if log.purged.is_some_and(|purged| {
        snapshot_applied.is_none_or(|id| {
            id < purged || id.index < purged.index || (id.index == purged.index && id != purged)
        })
    }) {
        return Err(invalid("purged log lacks a durable snapshot"));
    }
    for entry in log.entries.values() {
        if snapshot_applied.is_some_and(|applied| entry.log_id.index <= applied.index) {
            continue;
        }
        match entry.payload.clone() {
            EntryPayload::Blank => (),
            EntryPayload::Normal(command) => match command.into_body() {
                Command::Stage(stage) => {
                    image.stage(stage, genesis, placement, false);
                }
                Command::StageOwned(stage) => {
                    image.stage(stage, genesis, placement, true);
                }
                Command::Recover(stage) => {
                    image.recover(stage, genesis, placement);
                }
                Command::Admitted(..) => return Err(invalid("nested application ticket")),
                command => {
                    let segment = log
                        .segments
                        .get(&entry.log_id.index)
                        .cloned()
                        .ok_or_else(|| invalid("applied command has no durable WAL segment"))?;
                    image.state.apply(command, genesis, segment)?;
                }
            },
            EntryPayload::Membership(membership) => {
                image.verify_transition(&membership, placement, genesis)?;
                if let [voters] = membership.get_joint_config().as_slice() {
                    let voters = voters
                        .iter()
                        .copied()
                        .map(uuid::Uuid::from_u128)
                        .collect::<Vec<_>>();
                    let voters = <[_; 3]>::try_from(voters)
                        .map_err(|_| invalid("invalid finalized voter configuration"))?;
                    if image
                        .configuration
                        .is_none_or(|current| current.voters != voters)
                    {
                        image.previous_revision =
                            image.configuration.map(|current| current.revision);
                        let revision = if image.stage_intent {
                            image
                                .stage
                                .as_ref()
                                .and_then(|stage| stage.source.checked_add(1))
                                .ok_or_else(|| {
                                    invalid("finalized move lacks its target revision")
                                })?
                        } else {
                            entry.log_id.index
                        };
                        image.stage = None;
                        image.stage_intent = false;
                        image.configuration = Some(Configuration { revision, voters });
                    }
                }
                image.membership = Membership::new(Some(entry.log_id), membership);
            }
        }
        image.applied = Some(entry.log_id);
    }
    let membership = image.membership.membership();
    let configs = membership.get_joint_config();
    let voters = configs
        .first()
        .map(|set| set.iter().copied().map(uuid::Uuid::from_u128).collect())
        .unwrap_or_default();
    let joint_voters = configs
        .get(1)
        .map(|set| set.iter().copied().map(uuid::Uuid::from_u128).collect());
    let all_voters = membership
        .voter_ids()
        .collect::<std::collections::BTreeSet<_>>();
    let learners = membership
        .nodes()
        .map(|(id, _)| *id)
        .filter(|id| !all_voters.contains(id))
        .map(uuid::Uuid::from_u128)
        .collect();
    let (stream_state, head, floor) = match image.state.head() {
        Ok(head) => ("live", Some(head), Some(image.state.retained_floor())),
        Err(JournalError::Deleted) => ("deleted", None, None),
        Err(JournalError::NotFound) => ("absent", None, None),
        Err(_) => ("unknown", None, None),
    };
    let (retained_records, retained_bytes) = image.state.retained_stats();
    Ok(StreamStateView {
        snapshot_applied,
        applied: image.applied,
        voters,
        joint_voters,
        learners,
        configuration: image.configuration,
        fence: image
            .state
            .writer()
            .map(|(fence, owner)| (fence, owner.to_owned())),
        recovering: image.state.recovering(),
        head,
        floor,
        stream_state,
        retained_records,
        retained_bytes,
    })
}

pub(in crate::stream::consensus) async fn replay(
    disk: &Disk,
    genesis: Genesis,
    placement: Placement,
) -> io::Result<Replayed> {
    let machine = StateMachine::open(disk, genesis, placement).await?;
    let inner = machine.inner.clone();
    blocking(move || {
        let applied = inner.applied.read().applied;
        let entries = inner.disk.log(inner.genesis.stream, |log| {
            log.entries
                .values()
                .filter(|entry| applied.is_none_or(|applied| entry.log_id.index > applied.index))
                .cloned()
                .collect::<Vec<_>>()
        });
        inner.apply(entries)?;
        let image = inner.applied.read();
        Ok(Replayed {
            configuration: image.configuration,
            uniform: image.membership.membership().get_joint_config().len() == 1,
            head: image.state.head(),
            epoch: image
                .state
                .writer()
                .map_or(Epoch(0), |(fence, _)| fence.epoch),
        })
    })
    .await
}

pub(in crate::stream::consensus) fn repair_snapshot(
    disk: &Disk,
    stream: StreamId,
    backup: &Path,
    placement: &Placement,
) -> io::Result<()> {
    let genesis = disk
        .genesis(stream)
        .ok_or_else(|| invalid("stream is not installed on this keeper"))?;
    let selected = disk
        .log(stream, |log| log.snapshot)
        .ok_or_else(|| invalid("stream has no trusted snapshot selection"))?;
    let generation = disk
        .ownership(stream)
        .and_then(|owner| owner.generation())
        .ok_or_else(|| invalid("replica is detached"))?;
    let directory = crate::stream::consensus::ownership::directory(&disk.path, stream, generation);
    fs::create_dir_all(&directory)?;
    sync_directory(&disk.path)?;
    let temporary = directory.join(format!("building-repair-{}", uuid::Uuid::new_v4()));
    let result = (|| {
        let mut source = File::open(backup)?;
        let _space = disk.space.reserve(
            source
                .metadata()?
                .len()
                .saturating_add(disk.space.allocation_unit()),
        )?;
        let mut target = OpenOptions::new()
            .write(true)
            .read(true)
            .create_new(true)
            .open(&temporary)?;
        io::copy(&mut source, &mut target)?;
        target.rewind()?;
        let (_, image, _) = read_selected(
            target.try_clone()?,
            &directory,
            &genesis,
            selected,
            &disk.objects,
        )?;
        image.verify_placement(placement, &genesis)?;
        sync_file(&target)?;
        fs::rename(&temporary, selected.path(&directory))?;
        sync_directory(&directory)?;
        let _ = disk.clear_quarantine(stream)?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(temporary);
    }
    result
}

async fn blocking<T: Send + 'static>(
    work: impl FnOnce() -> io::Result<T> + Send + 'static,
) -> io::Result<T> {
    tokio::task::spawn_blocking(work)
        .await
        .map_err(io::Error::other)
        .and_then(|result| result)
}

const MAGIC: &[u8; 8] = b"LKRIMG03";
const STAGED_IMAGE: &str = "lk-stage-";
const HEADER_BYTES: u64 = 12;

// The checksum covers the serialized snapshot body. Use streaming IO so that
// snapshot transfer never needs a second serialized copy in memory.
fn write_image(
    file: &mut File,
    genesis: &Genesis,
    meta: &SnapshotMeta,
    image: &Image,
    quarantine: impl Fn(&str),
) -> io::Result<()> {
    file.write_all(MAGIC)?;
    file.write_all(&[0; 4])?;
    let mut crc = crc32fast::Hasher::new();
    {
        let mut buffer = BufWriter::new(&mut *file);
        let mut writer = HashWriter {
            writer: &mut buffer,
            crc: &mut crc,
            position: HEADER_BYTES,
        };
        options()
            .serialize_into(&mut writer, &(genesis, meta, image))
            .map_err(io::Error::other)?;
        for payload in image.state.records() {
            let bytes = payload
                .load()
                .inspect_err(|error| quarantine(&error.to_string()))?;
            let len = bytes.len() as u32 | if payload.timed() { TIMED_RECORD } else { 0 };
            let crc = crc32fast::hash(&bytes);
            writer.write_all(&len.to_be_bytes())?;
            writer.write_all(&crc.to_be_bytes())?;
            writer.write_all(&bytes)?;
        }
        buffer.flush()?;
    }
    file.seek(SeekFrom::Start(MAGIC.len() as u64))?;
    file.write_all(&crc.finalize().to_be_bytes())?;
    Ok(())
}

fn read_image(
    mut file: File,
    genesis: &Genesis,
    digest: [u8; 32],
    max_records: u64,
) -> io::Result<(SnapshotMeta, Image)> {
    file.rewind()?;
    let size = file.metadata()?.len();
    let extent = Arc::new(Mutex::new(file.try_clone()?));
    let mut file = BufReader::new(file);
    let mut header = [0; 12];
    file.read_exact(&mut header)?;
    if &header[..8] != MAGIC {
        return Err(invalid("invalid snapshot format"));
    }
    let mut crc = crc32fast::Hasher::new();
    let mut reader = HashReader {
        reader: &mut file,
        crc: &mut crc,
        position: HEADER_BYTES,
    };
    let (found, meta, mut image): (Genesis, SnapshotMeta, Image) = options()
        .with_limit(MAX_MESSAGE)
        .deserialize_from(&mut reader)
        .map_err(io::Error::other)?;
    image.stage_intent = meta.snapshot_id.starts_with(STAGED_IMAGE);
    if &found != genesis
        || image.applied != meta.last_log_id
        || image.membership != meta.last_membership
    {
        return Err(invalid("invalid snapshot contents"));
    }
    let count = image.state.record_count()?;
    if count > max_records
        || count > genesis.quota_bytes
        || count > size.saturating_sub(reader.position) / 8
    {
        return Err(invalid("invalid snapshot record count"));
    }
    let mut records = VecDeque::new();
    let mut buffer = [0; 64 * 1024];
    for _ in 0..count {
        let mut frame = [0; 8];
        reader.read_exact(&mut frame)?;
        let len = u32::from_be_bytes(frame[..4].try_into().unwrap());
        let timed = len & TIMED_RECORD != 0;
        let len = len & !TIMED_RECORD;
        let crc = u32::from_be_bytes(frame[4..].try_into().unwrap());
        if len as usize > MAX_RECORD || timed && (len as usize) <= EVIDENCE_BYTES {
            return Err(invalid("invalid snapshot record length"));
        }
        records.push_back(Payload::Snapshot {
            file: extent.clone(),
            digest,
            offset: reader.position,
            len,
            crc,
            timed,
        });
        let mut remaining = len as usize;
        let mut payload = crc32fast::Hasher::new();
        while remaining > 0 {
            let count = remaining.min(buffer.len());
            reader.read_exact(&mut buffer[..count])?;
            payload.update(&buffer[..count]);
            remaining -= count;
        }
        if payload.finalize() != crc {
            return Err(invalid("invalid snapshot record checksum"));
        }
    }
    if reader.position != size || crc.finalize().to_be_bytes() != header[8..] {
        return Err(invalid("invalid snapshot checksum or length"));
    }
    image.state.restore_records(records, genesis.quota_bytes)?;
    Ok((meta, image))
}

struct HashWriter<'a, W> {
    writer: &'a mut W,
    crc: &'a mut crc32fast::Hasher,
    position: u64,
}

impl<W: Write> Write for HashWriter<'_, W> {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        let count = self.writer.write(data)?;
        self.crc.update(&data[..count]);
        self.position += count as u64;
        Ok(count)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

struct HashReader<'a, R> {
    reader: &'a mut R,
    crc: &'a mut crc32fast::Hasher,
    position: u64,
}

impl<R: Read> Read for HashReader<'_, R> {
    fn read(&mut self, data: &mut [u8]) -> io::Result<usize> {
        let count = self.reader.read(data)?;
        self.crc.update(&data[..count]);
        self.position += count as u64;
        Ok(count)
    }
}
