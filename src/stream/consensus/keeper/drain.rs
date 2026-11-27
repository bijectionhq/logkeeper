//! A keeper's durable operator mode. A draining keeper hands off the
//! streams it leads, starts no election, takes no handed-off leadership and
//! reports that it accepts no new streams, so placement and repair choose
//! other keepers. A decommissioning keeper also moves its replicas off. The
//! mode is a file in the data directory and survives restarts until the
//! operator clears it.

use std::{
    fs, io,
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use openraft::{ServerState, async_runtime::WatchReceiver};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use super::{Engine, Group};
use crate::server::durability::{sync_directory, sync_file};

/// The mode's file in the keeper's data directory.
pub(super) const MODE_FILE: &str = "operator-mode.json";
/// How often a draining keeper retries handing off what it still leads.
pub(super) const DRAIN_INTERVAL: Duration = Duration::from_secs(1);
/// Election timeouts a stream may go without a leader before a draining
/// voter campaigns for it as a last resort.
const LEADERLESS_TIMEOUTS: u32 = 3;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum Mode {
    /// Takes leaderships and placements as usual.
    #[default]
    Serving,
    /// Leads nothing and takes no new placements.
    Draining,
    /// Drains, and moves each replica it votes in to another keeper.
    Decommissioning,
}

impl Mode {
    pub(super) fn draining(self) -> bool {
        self != Self::Serving
    }

    pub(super) fn name(self) -> &'static str {
        match self {
            Self::Serving => "serving",
            Self::Draining => "draining",
            Self::Decommissioning => "decommissioning",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Mark {
    pub mode: Mode,
    /// When the operator set this mode; zero while serving.
    pub since_unix_secs: u64,
}

pub(super) struct OperatorMode {
    path: PathBuf,
    /// Whether the mode drains, for the groups' own election retries.
    pub(super) flag: Arc<AtomicBool>,
    mark: parking_lot::Mutex<Mark>,
    /// Wakes the drain loop when the mode changes.
    pub(super) changed: tokio::sync::Notify,
    /// Serializes new replica ownership with a change of operator mode.
    placement: tokio::sync::RwLock<()>,
    /// Whether this process bumped its epoch after decommissioning.
    pub(super) fenced: AtomicBool,
}

impl OperatorMode {
    /// Reads the mode the operator left in `data`, serving when none.
    pub(super) fn open(data: &Path) -> io::Result<Self> {
        let path = data.join(MODE_FILE);
        let mark = match fs::read(&path) {
            Ok(bytes) => serde_json::from_slice(&bytes).map_err(|error| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: {error}", path.display()),
                )
            })?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Mark::default(),
            Err(error) => return Err(error),
        };
        Ok(Self {
            path,
            flag: Arc::new(AtomicBool::new(mark.mode.draining())),
            mark: parking_lot::Mutex::new(mark),
            changed: tokio::sync::Notify::new(),
            placement: tokio::sync::RwLock::new(()),
            fenced: AtomicBool::new(false),
        })
    }

    pub(super) fn mark(&self) -> Mark {
        *self.mark.lock()
    }

    pub(super) fn mode(&self) -> Mode {
        self.mark.lock().mode
    }

    pub(super) fn draining(&self) -> bool {
        self.flag.load(Ordering::Acquire)
    }

    pub(super) async fn admit_placement(&self) -> io::Result<tokio::sync::RwLockReadGuard<'_, ()>> {
        let guard = self.placement.read().await;
        if self.draining() {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "keeper is draining",
            ));
        }
        Ok(guard)
    }

    /// Durably records `mode` before it takes effect, and returns the mark
    /// in force. Setting the current mode again keeps its time.
    pub(super) fn set(&self, mode: Mode) -> io::Result<Mark> {
        let mut mark = self.mark.lock();
        if mark.mode == mode {
            return Ok(*mark);
        }
        let next = Mark {
            mode,
            since_unix_secs: if mode == Mode::Serving {
                0
            } else {
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs()
            },
        };
        let directory = self.path.parent().unwrap_or(Path::new("."));
        if mode == Mode::Serving {
            match fs::remove_file(&self.path) {
                Ok(()) => (),
                Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                Err(error) => return Err(error),
            }
        } else {
            let temporary = self.path.with_extension("json.tmp");
            let file = fs::File::create(&temporary)?;
            serde_json::to_writer(&file, &next)?;
            sync_file(&file)?;
            drop(file);
            fs::rename(&temporary, &self.path)?;
        }
        sync_directory(directory)?;
        *mark = next;
        self.flag.store(mode.draining(), Ordering::Release);
        drop(mark);
        self.changed.notify_one();
        Ok(next)
    }
}

/// `GET /drain`: what the mode leaves to do.
#[derive(Debug, Serialize)]
pub(super) struct DrainReport {
    pub keeper: Uuid,
    pub mode: Mode,
    pub since_unix_secs: u64,
    /// Streams this keeper still leads.
    pub led: usize,
    /// Streams with a replica on this keeper.
    pub hosted: usize,
    /// Hosted streams whose last configuration this keeper knows names it
    /// as a voter.
    pub voter_streams: usize,
    /// True once a draining keeper leads nothing.
    pub drained: bool,
    /// True once a decommissioning keeper has retired all its live copies.
    pub safe_to_delete: bool,
}

impl Engine {
    /// Applies the mode to one open group: a draining keeper starts no
    /// election of its own, nor does one without authority over the stream
    /// (`keeper/lease.rs`). It still votes, so the other voters elect.
    pub(super) fn apply_mode(&self, group: &Group) {
        group
            .raft
            .runtime_config()
            .elect(!self.mode.draining() && self.holds_authority(group));
    }

    /// Records `mode` durably and applies it to every open group.
    pub(super) async fn set_mode(self: &Arc<Self>, mode: Mode, actor: &str) -> io::Result<Mark> {
        if mode == Mode::Decommissioning && self.catalog.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "replicate the single-keeper catalog before decommissioning its keeper",
            ));
        }
        let engine = self.clone();
        let actor = actor.to_owned();
        // Finish applying the durable change even if the requesting client
        // disconnects while the mark is being synced.
        tokio::spawn(async move {
            let _placement = engine.mode.placement.write().await;
            let persistent = engine.clone();
            let mark = tokio::task::spawn_blocking(move || persistent.mode.set(mode))
                .await
                .map_err(io::Error::other)??;
            for group in engine.groups.lock().await.values() {
                engine.apply_mode(group);
            }
            tracing::info!(
                keeper = %engine.id,
                mode = ?mark.mode,
                "operator mode changed"
            );
            crate::stream::consensus::logging::audit_mode(engine.id, &actor, mark.mode.name());
            Ok(mark)
        })
        .await
        .map_err(io::Error::other)?
    }

    /// While draining, hands off every led stream each `DRAIN_INTERVAL`.
    pub(super) async fn drain_loop(self: &Arc<Self>) {
        let mut leaderless = std::collections::HashMap::new();
        loop {
            if self.mode.draining() {
                self.campaign_when_leaderless(&mut leaderless).await;
                self.evict_leaders(DRAIN_INTERVAL, true).await;
                self.fence_decommissioned().await;
                tokio::select! {
                    () = self.stop.cancelled() => return,
                    () = tokio::time::sleep(DRAIN_INTERVAL) => (),
                }
            } else {
                tokio::select! {
                    () = self.stop.cancelled() => return,
                    () = self.mode.changed.notified() => (),
                }
            }
        }
    }

    /// Once a decommissioning keeper holds nothing, bumps its epoch in the
    /// catalog: whatever authority it held before is in doubt, and every
    /// lease issued under the old epoch ends. Done once per process.
    async fn fence_decommissioned(&self) {
        if self.mode.mode() != Mode::Decommissioning
            || self.mode.fenced.load(Ordering::Acquire)
            || !self.drain_report().await.safe_to_delete
        {
            return;
        }
        match self
            .catalog_request(super::Request::FenceKeeper(self.id))
            .await
        {
            Ok(super::Reply::Decision(crate::stream::consensus::state::Outcome::Unit)) => {
                tracing::info!(keeper = %self.id, "decommissioned: bumped this keeper's epoch");
                self.mode.fenced.store(true, Ordering::Release);
            }
            // Before leases are finalized there is no epoch to bump.
            Ok(super::Reply::Decision(crate::stream::consensus::state::Outcome::Refused(
                journal_contract::JournalError::Unsupported,
            )))
            | Ok(super::Reply::Unsupported(_)) => self.mode.fenced.store(true, Ordering::Release),
            _ => (),
        }
    }

    /// A draining keeper starts no election of its own, but it may be the
    /// only voter that can win one: when the other voters' logs are behind
    /// its own or their keepers are down. A stream with no leader for
    /// `LEADERLESS_TIMEOUTS` election timeouts, or whose leader's keeper is
    /// suspected dead for as long, gets one campaign from it;
    /// once it leads, the drain loop hands the stream off as usual.
    async fn campaign_when_leaderless(
        &self,
        leaderless: &mut std::collections::HashMap<
            journal_contract::StreamId,
            tokio::time::Instant,
        >,
    ) {
        let limit =
            Duration::from_millis(self.raft_config.election_timeout_max) * LEADERLESS_TIMEOUTS;
        let now = tokio::time::Instant::now();
        let groups = self.groups.lock().await.clone();
        leaderless.retain(|stream, _| groups.contains_key(stream));
        for (stream, group) in groups {
            // A follower keeps naming a leader that died until a new vote
            // reaches it, which pre-vote prevents when nobody can win, so a
            // leader whose keeper stopped answering pings counts as none.
            let leader = group.raft.metrics().borrow_watched().current_leader;
            if leader.is_some_and(|leader| {
                leader == self.id.as_u128() || !self.suspect(uuid::Uuid::from_u128(leader))
            }) {
                leaderless.remove(&stream);
                continue;
            }
            let since = *leaderless.entry(stream).or_insert(now);
            if now.duration_since(since) >= limit {
                leaderless.insert(stream, now);
                if group.raft.trigger().elect(false).await.is_ok() {
                    tracing::info!(
                        keeper = %self.id,
                        stream = %crate::stream::consensus::logging::stream_uuid(stream),
                        "draining keeper campaigns for a stream left without a leader"
                    );
                }
            }
        }
    }

    pub(super) async fn drain_report(&self) -> DrainReport {
        let _placement = self.mode.placement.read().await;
        let mark = self.mode.mark();
        let groups = self.groups.lock().await.clone();
        let led = groups
            .values()
            .filter(|group| group.raft.metrics().borrow_watched().state == ServerState::Leader)
            .count();
        let closed = self.closed_views();
        let deleted = self.deleted.read().clone();
        let mut hosted = 0;
        let mut voter_streams = 0;
        for genesis in self.disk.streams() {
            let stream = genesis.stream;
            if deleted.contains(&stream)
                || !self
                    .disk
                    .ownership(stream)
                    .is_some_and(|owner| owner.generation().is_some())
            {
                continue;
            }
            hosted += 1;
            let voters = match groups.get(&stream) {
                Some(group) => group
                    .state
                    .finalized()
                    .map(|configuration| configuration.voters.to_vec())
                    .unwrap_or_else(|| genesis.voters.to_vec()),
                None => match closed.get(&stream) {
                    Some(view) if !view.voters.is_empty() => view.voters.iter().copied().collect(),
                    _ => genesis.voters.to_vec(),
                },
            };
            if voters.contains(&self.id) {
                voter_streams += 1;
            }
        }
        DrainReport {
            keeper: self.id,
            mode: mark.mode,
            since_unix_secs: mark.since_unix_secs,
            led,
            hosted,
            voter_streams,
            drained: mark.mode.draining() && led == 0,
            safe_to_delete: mark.mode == Mode::Decommissioning
                && self.replayed.load(Ordering::Acquire)
                && self.disk.healthy()
                && led == 0
                && hosted == 0,
        }
    }
}
