//! The keeper side of continuous offload (`consensus/offload`).
//!
//! **Who uploads.** The leader of each stream. It holds every committed
//! record hot, learns commits first, and already serves the stream's
//! writes, so no other coordination is needed: a designated voter would
//! need its own election and would have to learn the commit index from the
//! leader anyway. Leadership moves with the stream, and uploads are
//! idempotent across leader changes: a new leader starts from the
//! replicated `offloaded_through`, an object key names its lineage and LSN
//! range, the store writes a key at most once, and every record an object
//! holds is committed, so a range uploaded twice holds the same records.
//!
//! **When.** Every `TICK` the loop looks at each stream this keeper leads.
//! It uploads once `batch_bytes` committed bytes wait or the oldest has
//! waited `batch_interval`, one object of at most `batch_bytes` at a time
//! per stream, `concurrency` across the keeper, then proposes
//! `Command::Offloaded`. A failed upload backs off from 100 ms to 30 s.
//! While more than `max_lag_bytes` wait, the leader refuses appends with
//! `Unavailable` (`backpressure`), so a long store outage stops writers
//! instead of filling the keepers.
//!
//! **Retention.** With `retain_local_bytes`, the same proposal asks every
//! voter to drop offloaded records older than the newest
//! `retain_local_bytes` bytes. Reads below the local floor are served from
//! the store by whichever keeper answers the read.

use std::{
    collections::HashMap,
    io,
    sync::Arc,
    time::{Duration, Instant},
};

use journal_contract::{JournalError, Lsn, Page, StreamId};
use openraft::async_runtime::WatchReceiver;
use tokio::sync::Semaphore;

use super::{Engine, Group, Reply, catalog_stream};
use crate::stream::{
    consensus::{
        CLUSTER_VERSION_OFFLOAD, MAX_PAGE, MAX_RECORDS_PER_PAGE, decisions,
        offload::{LineageRecord, OffloadConfig, Store},
        state::{Command, Outcome, RecordKind, Remote},
    },
    timed::EVIDENCE_BYTES,
};

const TICK: Duration = Duration::from_millis(100);
/// How often the loop checks whether retention could drop records without
/// an upload. Each check walks the newest `retain_local_bytes` of a stream.
const RETENTION_CHECK: Duration = Duration::from_secs(5);
const RETRY_FIRST: Duration = Duration::from_millis(100);
const RETRY_MAX: Duration = Duration::from_secs(30);
/// How long a flush (`OffloadStatus` with `flush`) keeps uploading.
const FLUSH_TIMEOUT: Duration = Duration::from_secs(60);

/// What `Request::OffloadStatus` reports about one stream.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OffloadStatus {
    pub stream: StreamId,
    /// The replicated last LSN durably uploaded.
    pub offloaded_through: Lsn,
    /// The current lineage and every lineage with its first LSN.
    pub lineage: u64,
    pub lineages: Vec<(u64, Lsn)>,
    /// Below this the writer trimmed.
    pub floor: Lsn,
    /// The first record the keepers hold locally; the store serves reads
    /// from `floor` up to it.
    pub local_floor: Lsn,
    pub head: Lsn,
    /// The highest writer epoch.
    pub epoch: journal_contract::Epoch,
}

#[derive(Default)]
struct Progress {
    lock: Arc<tokio::sync::Mutex<()>>,
    waiting_bytes: u64,
    waiting_since: Option<Instant>,
    retry_at: Option<Instant>,
    failures: u32,
    lineage_recorded: Option<u64>,
    retention_checked: Option<Instant>,
}

/// One keeper's offload: its store and per-stream upload progress.
pub(in crate::stream::consensus) struct Offloader {
    pub store: Arc<Store>,
    pub config: OffloadConfig,
    uploads: Semaphore,
    progress: parking_lot::Mutex<HashMap<StreamId, Progress>>,
}

impl Offloader {
    pub fn open(config: OffloadConfig) -> io::Result<Self> {
        Ok(Self {
            store: Arc::new(Store::open(&config)?),
            uploads: Semaphore::new(config.concurrency.max(1)),
            config,
            progress: parking_lot::Mutex::default(),
        })
    }

    /// Whether the leader refuses appends to `stream` because too many
    /// committed bytes wait for upload.
    pub fn backpressured(&self, stream: StreamId) -> bool {
        let waiting = self
            .progress
            .lock()
            .get(&stream)
            .map_or(0, |progress| progress.waiting_bytes);
        decisions::offload_backpressure(
            self.config.backpressure,
            waiting,
            self.config.max_lag_bytes,
        )
    }

    fn lock(&self, stream: StreamId) -> Arc<tokio::sync::Mutex<()>> {
        self.progress.lock().entry(stream).or_default().lock.clone()
    }

    fn failed(&self, stream: StreamId) {
        let mut progress = self.progress.lock();
        let progress = progress.entry(stream).or_default();
        progress.failures = progress.failures.saturating_add(1);
        let delay = RETRY_FIRST
            .saturating_mul(1 << progress.failures.min(16))
            .min(RETRY_MAX);
        progress.retry_at = Some(Instant::now() + delay);
    }

    fn succeeded(&self, stream: StreamId) {
        if let Some(progress) = self.progress.lock().get_mut(&stream) {
            progress.failures = 0;
            progress.retry_at = None;
        }
    }

    /// Reads one page below the local floor from the store.
    pub async fn read(
        &self,
        stream: StreamId,
        remote: Remote,
        limit: usize,
    ) -> Result<Page, JournalError> {
        let metrics = &self.store.metrics;
        let records = self
            .store
            .read(
                stream,
                remote.lineage,
                remote.from,
                remote.until,
                limit.min(MAX_RECORDS_PER_PAGE).max(1),
                MAX_PAGE,
            )
            .await
            .map_err(|error| {
                crate::stream::consensus::metrics::count(&metrics.remote_read_failures);
                if let Some(dropped) =
                    crate::stream::consensus::logging::rate_limit("offload.read", None)
                {
                    tracing::warn!(
                        stream = %format!("{:032x}", stream.0),
                        from = remote.from.0,
                        error = %error,
                        dropped = dropped,
                        "offloaded read failed"
                    );
                }
                if error.kind() == io::ErrorKind::InvalidData {
                    JournalError::Corrupted
                } else {
                    JournalError::Unavailable
                }
            })?;
        crate::stream::consensus::metrics::count(&metrics.remote_reads);
        let mut recoveries = Vec::new();
        let records = records
            .into_iter()
            .map(|record| {
                let bytes = match record.kind {
                    RecordKind::Timed => record
                        .bytes
                        .get(EVIDENCE_BYTES..)
                        .map(|payload| record.bytes.slice_ref(payload))
                        .ok_or(JournalError::Corrupted)?,
                    RecordKind::Recovery => {
                        let entry = journal_contract::RecoveryEntry::decode(&record.bytes)
                            .ok_or(JournalError::Corrupted)?;
                        recoveries.push((record.lsn, entry));
                        record.bytes
                    }
                    RecordKind::Data => record.bytes,
                };
                Ok((record.lsn, bytes))
            })
            .collect::<Result<Vec<_>, JournalError>>()?;
        Ok(Page {
            floor: remote.floor,
            records,
            head: remote.head,
            recoveries,
        })
    }
}

impl Engine {
    pub(super) async fn offload_loop(self: Arc<Self>) {
        let Some(offloader) = self.offload.clone() else {
            return;
        };
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = tokio::time::sleep(TICK) => {}
            }
            if !self.disk.write_version_allows(CLUSTER_VERSION_OFFLOAD) {
                continue;
            }
            let groups = self
                .groups
                .lock()
                .await
                .values()
                .cloned()
                .collect::<Vec<_>>();
            let now = Instant::now();
            let (mut lag_bytes, mut lag_age) = (0u64, Duration::ZERO);
            let mut led = std::collections::HashSet::new();
            for group in groups {
                let stream = group.genesis.stream;
                if stream == catalog_stream::STREAM
                    || group.raft.metrics().borrow_watched().state != openraft::ServerState::Leader
                    || !group.state.healthy()
                {
                    continue;
                }
                let Some(view) = group.state.offload_view() else {
                    continue;
                };
                led.insert(stream);
                let next = Lsn((view.offload.through.0 + 1).max(view.logical_floor.0));
                let waiting = group.state.waiting_bytes(next);
                let retention_due = offloader
                    .progress
                    .lock()
                    .get(&stream)
                    .is_none_or(|progress| {
                        progress
                            .retention_checked
                            .is_none_or(|at| now - at >= RETENTION_CHECK)
                    });
                let retain = retention_due
                    && offloader.config.retain_local_bytes.is_some_and(|bytes| {
                        group
                            .state
                            .retention_floor(bytes)
                            .min(Lsn(view.offload.through.0 + 1))
                            > view.local_floor
                    });
                let due = {
                    let mut progress = offloader.progress.lock();
                    let progress = progress.entry(stream).or_default();
                    if retention_due {
                        progress.retention_checked = Some(now);
                    }
                    progress.waiting_bytes = waiting;
                    if waiting == 0 {
                        progress.waiting_since = None;
                    } else if progress.waiting_since.is_none() {
                        progress.waiting_since = Some(now);
                    }
                    let age = progress
                        .waiting_since
                        .map_or(Duration::ZERO, |since| now - since);
                    lag_bytes = lag_bytes.max(waiting);
                    lag_age = lag_age.max(age);
                    let ready = waiting >= offloader.config.batch_bytes
                        || (waiting > 0 && age >= offloader.config.batch_interval())
                        || decisions::offload_backpressure(
                            true,
                            waiting,
                            offloader.config.max_lag_bytes / 2,
                        )
                        || (waiting == 0 && retain);
                    ready && progress.retry_at.is_none_or(|at| at <= now)
                };
                if !due {
                    continue;
                }
                let lock = offloader.lock(stream);
                let Ok(guard) = lock.try_lock_owned() else {
                    continue;
                };
                let engine = self.clone();
                let offloader = offloader.clone();
                tokio::spawn(async move {
                    let _guard = guard;
                    match engine.offload_once(&offloader, &group).await {
                        Ok(_) => offloader.succeeded(stream),
                        Err(error) => {
                            offloader.failed(stream);
                            if let Some(dropped) = crate::stream::consensus::logging::rate_limit(
                                "offload.upload",
                                None,
                            ) {
                                tracing::warn!(
                                    keeper = %engine.id,
                                    stream = %format!("{:032x}", stream.0),
                                    error = %error,
                                    dropped = dropped,
                                    "offload deferred"
                                );
                            }
                        }
                    }
                });
            }
            offloader.progress.lock().retain(|stream, progress| {
                led.contains(stream) || Arc::strong_count(&progress.lock) > 1
            });
            let metrics = &offloader.store.metrics;
            use std::sync::atomic::Ordering::Relaxed;
            metrics.lag_bytes_max.store(lag_bytes, Relaxed);
            metrics
                .lag_age_ms_max
                .store(lag_age.as_millis() as u64, Relaxed);
        }
    }

    /// Uploads the next object of `group`'s committed records, if any wait,
    /// and records the upload and the retention floor through Raft.
    /// Returns the replicated `offloaded_through`.
    pub(super) async fn offload_once(
        &self,
        offloader: &Offloader,
        group: &Group,
    ) -> io::Result<Lsn> {
        let stream = group.genesis.stream;
        let store = &offloader.store;
        let metrics = &store.metrics;
        let view = group
            .state
            .offload_view()
            .ok_or_else(|| io::Error::other("the stream is not live"))?;
        let lineage = view.offload.lineage;
        let next = Lsn((view.offload.through.0 + 1).max(view.logical_floor.0));
        let mut through = view.offload.through;
        if next <= view.head {
            let _permit = offloader
                .uploads
                .acquire()
                .await
                .map_err(io::Error::other)?;
            let recorded = offloader
                .progress
                .lock()
                .get(&stream)
                .and_then(|progress| progress.lineage_recorded);
            if recorded != Some(lineage) {
                store
                    .put_lineage(&LineageRecord {
                        stream,
                        lineage,
                        lineages: view.offload.map(),
                        floor: view.logical_floor,
                        epoch: view.epoch,
                    })
                    .await?;
                offloader
                    .progress
                    .lock()
                    .entry(stream)
                    .or_default()
                    .lineage_recorded = Some(lineage);
            }
            let (records, epochs) = group
                .state
                .offload_records(next, offloader.config.object_bytes())
                .await?;
            let Some(last) = records.last().map(|record| record.lsn) else {
                return Ok(through);
            };
            let started = Instant::now();
            let uploaded = store.upload(stream, lineage, &records, epochs).await;
            let (created, size) = uploaded.inspect_err(|_| {
                crate::stream::consensus::metrics::count(&metrics.upload_failures);
            })?;
            metrics.upload_duration.observe(started.elapsed());
            if created {
                crate::stream::consensus::metrics::count(&metrics.uploaded_objects);
                crate::stream::consensus::metrics::add(&metrics.uploaded_bytes, size as u64);
            } else {
                crate::stream::consensus::metrics::count(&metrics.existing_objects);
            }
            through = last;
        }
        let retain_from = offloader
            .config
            .retain_local_bytes
            .map_or(Lsn(0), |bytes| group.state.retention_floor(bytes));
        if through == view.offload.through
            && retain_from.min(Lsn(through.0 + 1)) <= view.local_floor
        {
            return Ok(through);
        }
        match group
            .write(Command::Offloaded {
                lineage,
                through,
                retain_from,
            })
            .await
        {
            Reply::Decision(Outcome::At(recorded)) => {
                crate::stream::consensus::metrics::count(&metrics.recorded);
                let dropped = group.state.offload_view().map_or(0, |after| {
                    after.local_floor.0.saturating_sub(view.local_floor.0)
                });
                crate::stream::consensus::metrics::add(&metrics.locally_trimmed_records, dropped);
                Ok(recorded)
            }
            reply => {
                crate::stream::consensus::metrics::count(&metrics.record_failures);
                Err(io::Error::other(format!(
                    "offloaded_through did not commit: {}",
                    super::describe_audit_reply(&reply)
                )))
            }
        }
    }

    /// The offload status of `group`, after uploading everything committed
    /// when it was asked if `flush`.
    pub(super) async fn offload_status(&self, group: &Group, flush: bool) -> Reply {
        let Some(offloader) = self.offload.clone() else {
            return super::failure(JournalError::Unsupported);
        };
        if group.raft.metrics().borrow_watched().state != openraft::ServerState::Leader {
            return super::leader_reply(group.raft.metrics().borrow_watched().current_leader);
        }
        if flush {
            if !self.disk.write_version_allows(CLUSTER_VERSION_OFFLOAD) {
                return super::failure(JournalError::Unsupported);
            }
            if let Err(reply) = group
                .barrier(tokio::time::Instant::now() + super::REQUEST_TIMEOUT)
                .await
            {
                return reply;
            }
            let target = group.state.head().unwrap_or(Lsn(0));
            let deadline = Instant::now() + FLUSH_TIMEOUT;
            let lock = offloader.lock(group.genesis.stream);
            let _guard = lock.lock().await;
            loop {
                match self.offload_once(&offloader, group).await {
                    Ok(through) if through >= target => break,
                    Ok(_) => {}
                    Err(_) if Instant::now() < deadline => {
                        tokio::time::sleep(RETRY_FIRST).await;
                    }
                    Err(_) => return super::failure(JournalError::Unavailable),
                }
                if Instant::now() >= deadline {
                    return super::failure(JournalError::Unavailable);
                }
                if group.state.offload_view().is_some_and(|view| {
                    Lsn((view.offload.through.0 + 1).max(view.logical_floor.0)) > target
                }) {
                    break;
                }
            }
        }
        match group.state.offload_view() {
            Some(view) => Reply::Decision(Outcome::Offload(OffloadStatus {
                stream: group.genesis.stream,
                offloaded_through: view.offload.through,
                lineage: view.offload.lineage,
                lineages: view.offload.map(),
                floor: view.logical_floor,
                local_floor: view.local_floor,
                head: view.head,
                epoch: view.epoch,
            })),
            None => super::failure(JournalError::NotFound),
        }
    }

    /// Restores `group`, a fresh stream, from records an operator put in
    /// the store under its lineage 0.
    pub(super) async fn restore_fresh(
        &self,
        group: &Group,
        restore: crate::stream::consensus::state::Restore,
    ) -> Reply {
        let Some(offloader) = self.offload.clone() else {
            return super::failure(JournalError::Unsupported);
        };
        if !self.disk.write_version_allows(CLUSTER_VERSION_OFFLOAD) {
            return super::failure(JournalError::Unsupported);
        }
        if let Err(reply) = group
            .barrier(tokio::time::Instant::now() + super::REQUEST_TIMEOUT)
            .await
        {
            return reply;
        }
        let Some(view) = group.state.offload_view() else {
            return super::failure(JournalError::NotFound);
        };
        if view.head != Lsn(0) || view.offload.lineage != 0 || !restore.replace {
            return super::failure(JournalError::Conflict { head: view.head });
        }
        let stream = group.genesis.stream;
        // The store must hold the whole run before the stream points at it.
        match offloader
            .store
            .plan(stream, &[(0, Lsn(1))], restore.floor)
            .await
        {
            Ok(plan)
                if restore.head < restore.floor
                    || plan.run == Some((restore.floor, restore.head)) => {}
            Ok(_) => return super::failure(JournalError::Conflict { head: Lsn(0) }),
            Err(_) => return super::failure(JournalError::Unavailable),
        }
        let lineages = vec![(0, Lsn(1)), (restore.lineage, Lsn(restore.head.0 + 1))];
        if offloader
            .store
            .put_lineage(&LineageRecord {
                stream,
                lineage: restore.lineage,
                lineages,
                floor: restore.floor,
                epoch: restore.epoch,
            })
            .await
            .is_err()
        {
            return super::failure(JournalError::Unavailable);
        }
        group.write(Command::Restore(restore)).await
    }
}

/// What an operator recovery found in the offload store, and kept.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OffloadRecovery {
    /// The head of the survivor's history the recovery started from: its
    /// committed prefix once leases are finalized, its whole log before.
    pub survivor_head: Lsn,
    /// The `offloaded_through` the survivor had applied.
    pub offloaded_through: Lsn,
    /// The end of the committed run the store holds, if any.
    pub store_end: Option<Lsn>,
    /// The loss point: every record at or below it is kept, from `floor`.
    /// Records a writer was acknowledged above it are lost.
    pub kept_through: Lsn,
    pub floor: Lsn,
    /// The lineage the recovered history uploads under.
    pub lineage: u64,
    /// Whether the store's run replaced the survivor's shorter copy.
    pub restored: bool,
}

impl std::fmt::Display for OffloadRecovery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Loss point: records {}..={} are kept (survivor head {}, survivor's offloaded_through \
             {}, object store run ending at {}{}); acknowledged records above {} are lost. \
             Offload continues under lineage {}.",
            self.floor.0,
            self.kept_through.0,
            self.survivor_head.0,
            self.offloaded_through.0,
            self.store_end
                .map_or_else(|| "none".to_owned(), |end| end.0.to_string()),
            if self.restored {
                ", which replaced the survivor's copy"
            } else {
                ""
            },
            self.kept_through.0,
            self.lineage,
        )
    }
}

/// Plans the offload half of an operator recovery: the committed run the
/// store holds under the survivor's lineages, the `Command::Restore` that
/// starts a new lineage and, when the run is longer than the survivor's
/// log, makes it the history. Records the new lineage in the store first,
/// so a later restore with no voter left finds it. `survivor_head` is the
/// head of the history the survivor keeps: its committed prefix once leases
/// are finalized, so the store's committed run replaces every survivor
/// record it never knew committed (`decisions::recovered_head`).
pub(super) async fn plan_recovery(
    store: &Store,
    stream: StreamId,
    survivor_head: Lsn,
    survivor_epoch: journal_contract::Epoch,
    view: &crate::stream::consensus::state::OffloadView,
    revision: u64,
) -> io::Result<(crate::stream::consensus::state::Restore, OffloadRecovery)> {
    let lineages = view.offload.map();
    let highest = store.lineages(stream).await?.into_iter().max().unwrap_or(0);
    // A recovery's lineage is the stream configuration epoch it installs,
    // its revision, which the catalog records too, unless the store already
    // holds that lineage or a later one.
    let lineage = (highest.max(view.offload.lineage) + 1).max(revision);
    let plan = store.plan(stream, &lineages, view.logical_floor).await?;
    let store_end = plan.end();
    let kept = Lsn(decisions::recovered_head(
        survivor_head.0,
        store_end.map_or(0, |end| end.0),
    ));
    let restored = store_end.is_some_and(|end| end > survivor_head);
    let (floor, epoch) = if restored {
        let mut epoch = survivor_epoch;
        for (segment, _, _) in store.segments(stream, &plan).await? {
            epoch = epoch.max(segment.max_epoch());
        }
        let first = plan.run.map_or(view.logical_floor, |(first, _)| first);
        (first.max(view.logical_floor), epoch)
    } else {
        (view.logical_floor, survivor_epoch)
    };
    let restore = crate::stream::consensus::state::Restore {
        lineage,
        floor,
        head: if restored {
            kept
        } else {
            store_end.unwrap_or(view.offload.through).min(survivor_head)
        },
        epoch,
        replace: restored,
    };
    let through = if restored {
        kept
    } else {
        Lsn(decisions::offloaded_through(
            view.offload.through.0,
            restore.head.0,
            survivor_head.0,
        ))
    };
    let mut recorded = lineages;
    recorded.push((lineage, Lsn(through.0 + 1)));
    store
        .put_lineage(&LineageRecord {
            stream,
            lineage,
            lineages: recorded,
            floor,
            epoch,
        })
        .await?;
    Ok((
        restore,
        OffloadRecovery {
            survivor_head,
            offloaded_through: view.offload.through,
            store_end,
            kept_through: kept,
            floor,
            lineage,
            restored,
        },
    ))
}
