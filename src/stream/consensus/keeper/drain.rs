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
        })
    }

    pub(super) fn mark(&self) -> Mark {
        *self.mark.lock()
    }

    pub(super) fn mode(&self) -> Mode {
        self.mark.lock().mode
    }

    pub(super) fn draining(&self) -> bool {
        self.mode().draining()
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
        self.changed.notify_waiters();
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
    /// True once a decommissioning keeper votes in no stream: its data may
    /// be deleted after it stops.
    pub safe_to_delete: bool,
}

impl Engine {
    /// Applies the mode to one open group: a draining keeper starts no
    /// election of its own. It still votes, so the other voters elect.
    pub(super) fn apply_mode(&self, group: &Group) {
        group.raft.runtime_config().elect(!self.mode.draining());
    }

    /// Records `mode` durably and applies it to every open group.
    pub(super) async fn set_mode(self: &Arc<Self>, mode: Mode, actor: &str) -> io::Result<Mark> {
        let engine = self.clone();
        let mark = tokio::task::spawn_blocking(move || engine.mode.set(mode))
            .await
            .map_err(io::Error::other)??;
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for group in &groups {
            self.apply_mode(group);
        }
        tracing::info!(
            keeper = %self.id,
            mode = ?mark.mode,
            "operator mode changed"
        );
        crate::stream::consensus::logging::audit_mode(self.id, actor, mark.mode.name());
        Ok(mark)
    }

    /// While draining, hands off every led stream each `DRAIN_INTERVAL`.
    pub(super) async fn drain_loop(self: &Arc<Self>) {
        loop {
            if self.mode.draining() {
                self.shed_leadership_when_full().await;
                tokio::select! {
                    () = self.stop.cancelled() => return,
                    () = tokio::time::sleep(DRAIN_INTERVAL) => (),
                }
            } else {
                tokio::select! {
                    () = self.stop.cancelled() => return,
                    () = self.mode.changed.notified() => (),
                    // A missed notification costs at most one interval.
                    () = tokio::time::sleep(DRAIN_INTERVAL * 10) => (),
                }
            }
        }
    }

    pub(super) async fn drain_report(&self) -> DrainReport {
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
            safe_to_delete: mark.mode == Mode::Decommissioning && led == 0 && voter_streams == 0,
        }
    }
}
