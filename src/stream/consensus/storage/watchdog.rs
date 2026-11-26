//! Fails a keeper fast when its WAL round stops making progress.
//!
//! One WAL thread serves every stream group on a keeper. A sync that never
//! returns would freeze every stream while idle leaders kept their leadership.
//! The watchdog ends the process once a round runs past its limit, so the
//! other voters elect new leaders, as CockroachDB does after
//! `storage.max_sync_duration`.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};

/// A WAL round longer than this ends the keeper process.
pub(super) const MAX_ROUND_DURATION: Duration = Duration::from_secs(20);
const CHECK_INTERVAL: Duration = Duration::from_millis(500);

pub(super) struct Watchdog {
    epoch: Instant,
    /// Milliseconds since `epoch` at which the current round started, plus
    /// one; zero when no round is in progress.
    started: AtomicU64,
}

/// Marks a round in progress until dropped.
pub(super) struct Round<'a>(&'a Watchdog);

impl Drop for Round<'_> {
    fn drop(&mut self) {
        self.0.started.store(0, Ordering::Release);
    }
}

impl Watchdog {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            epoch: Instant::now(),
            started: AtomicU64::new(0),
        })
    }

    pub fn begin(&self) -> Round<'_> {
        let now = self.epoch.elapsed().as_millis() as u64;
        self.started.store(now + 1, Ordering::Release);
        Round(self)
    }

    /// How long the current round has run, if one is in progress.
    fn running(&self) -> Option<Duration> {
        let started = self.started.load(Ordering::Acquire);
        (started != 0).then(|| {
            let now = self.epoch.elapsed().as_millis() as u64;
            Duration::from_millis((now + 1).saturating_sub(started))
        })
    }

    /// Checks the round every `CHECK_INTERVAL` while `active` holds. A round
    /// past `limit` clears `active` and calls `on_stall`.
    pub fn spawn(
        self: &Arc<Self>,
        active: Arc<AtomicBool>,
        limit: Duration,
        on_stall: impl Fn(Duration) + Send + 'static,
    ) -> std::io::Result<()> {
        let watchdog = self.clone();
        std::thread::Builder::new()
            .name("logkeeper-wal-watchdog".into())
            .spawn(move || {
                while active.load(Ordering::Acquire) {
                    std::thread::sleep(CHECK_INTERVAL.min(limit));
                    if let Some(running) = watchdog.running().filter(|running| *running > limit) {
                        active.store(false, Ordering::Release);
                        on_stall(running);
                        return;
                    }
                }
            })
            .map(drop)
    }
}

/// The production stall action: report and end the process.
pub(super) fn exit_on_stall(running: Duration) {
    eprintln!("logkeeper consensus WAL round stalled for {running:?}; exiting");
    std::process::exit(70);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_stalled_round_trips_the_watchdog_and_a_finished_one_does_not() {
        let watchdog = Watchdog::new();
        let active = Arc::new(AtomicBool::new(true));
        let (tripped, trips) = std::sync::mpsc::channel();
        watchdog
            .spawn(active.clone(), Duration::from_millis(50), move |running| {
                let _ = tripped.send(running);
            })
            .unwrap();
        {
            let _round = watchdog.begin();
            std::thread::sleep(Duration::from_millis(10));
        }
        std::thread::sleep(Duration::from_millis(120));
        assert!(trips.try_recv().is_err());
        let _round = watchdog.begin();
        let running = trips.recv_timeout(Duration::from_secs(2)).unwrap();
        assert!(running > Duration::from_millis(50));
        assert!(!active.load(Ordering::Acquire));
    }
}
