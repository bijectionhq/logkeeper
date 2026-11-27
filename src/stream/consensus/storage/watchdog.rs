//! Fails a keeper fast when its WAL round stops making progress.
//!
//! One WAL thread serves every stream group on a keeper. A sync that never
//! returns would freeze every stream while idle leaders kept their leadership.
//! The watchdog ends the process once a round runs past its limit, so the
//! other voters elect new leaders, as CockroachDB does after
//! `storage.max_sync_duration`.
//!
//! Well before that, a round past `SLOW_ROUND` marks the media slow for
//! `SLOW_HOLD` after the round ends. A slow keeper hands off the streams it
//! leads, refuses votes and reports that it accepts no streams, so a disk
//! that stalls for seconds costs its streams a leadership change instead of
//! seconds of latency.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};

/// A WAL round longer than this ends the keeper process.
pub(super) const MAX_ROUND_DURATION: Duration = Duration::from_secs(20);
/// A WAL round longer than this marks the media slow.
pub(super) const SLOW_ROUND: Duration = Duration::from_millis(2_500);
/// How long the media stays slow after its last slow round.
pub(super) const SLOW_HOLD: Duration = Duration::from_secs(10);
const CHECK_INTERVAL: Duration = Duration::from_millis(500);

pub(super) struct Watchdog {
    epoch: Instant,
    /// Milliseconds since `epoch` at which the current round started, plus
    /// one; zero when no round is in progress.
    started: AtomicU64,
    /// Milliseconds since `epoch` until which the media counts as slow.
    slow_until: AtomicU64,
    slowed: tokio::sync::Notify,
}

/// Marks a round in progress until dropped.
pub(super) struct Round<'a>(&'a Watchdog);

impl Drop for Round<'_> {
    fn drop(&mut self) {
        let started = self.0.started.swap(0, Ordering::AcqRel);
        let now = self.0.now();
        if started != 0 && (now + 1).saturating_sub(started) > SLOW_ROUND.as_millis() as u64 {
            self.0.hold_slow(now);
        }
    }
}

impl Watchdog {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            epoch: Instant::now(),
            started: AtomicU64::new(0),
            slow_until: AtomicU64::new(0),
            slowed: tokio::sync::Notify::new(),
        })
    }

    fn now(&self) -> u64 {
        self.epoch.elapsed().as_millis() as u64
    }

    fn hold_slow(&self, now: u64) {
        self.slow_until
            .fetch_max(now + SLOW_HOLD.as_millis() as u64, Ordering::AcqRel);
    }

    /// Whether the media keeps up: no round runs past `SLOW_ROUND` and
    /// none did within `SLOW_HOLD`.
    pub fn responsive(&self) -> bool {
        let now = self.now();
        crate::stream::consensus::decisions::media_responsive(
            self.running()
                .map_or(0, |running| running.as_millis() as u64),
            self.slow_until.load(Ordering::Acquire),
            now,
            SLOW_ROUND.as_millis() as u64,
        )
    }

    /// Resolves once the media turns slow.
    pub async fn slowed(&self) {
        self.slowed.notified().await;
    }

    /// Marks the media slow for `hold`, as a slow round would.
    #[cfg(test)]
    pub fn mark_slow(&self, hold: Duration) {
        self.slow_until
            .fetch_max(self.now() + hold.as_millis() as u64, Ordering::AcqRel);
        self.slowed.notify_one();
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
    /// past `SLOW_ROUND` marks the media slow once; one past `limit` clears
    /// `active` and calls `on_stall`.
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
                let mut flagged = 0;
                while active.load(Ordering::Acquire) {
                    std::thread::sleep(CHECK_INTERVAL.min(limit));
                    let Some(running) = watchdog.running() else {
                        continue;
                    };
                    if running > limit {
                        active.store(false, Ordering::Release);
                        on_stall(running);
                        return;
                    }
                    let round = watchdog.started.load(Ordering::Acquire);
                    if running > SLOW_ROUND && flagged != round {
                        flagged = round;
                        eprintln!(
                            "logkeeper consensus WAL round slow for {running:?}; \
                             handing off leadership"
                        );
                        watchdog.hold_slow(watchdog.now());
                        watchdog.slowed.notify_one();
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

    #[test]
    fn a_slow_round_marks_the_media_slow_before_the_stall_limit() {
        let watchdog = Watchdog::new();
        let active = Arc::new(AtomicBool::new(true));
        watchdog
            .spawn(active.clone(), MAX_ROUND_DURATION, |_| {
                panic!("a slow round must not end the process")
            })
            .unwrap();
        assert!(watchdog.responsive());
        let slowed = {
            let _round = watchdog.begin();
            let runtime = tokio::runtime::Builder::new_current_thread()
                .enable_time()
                .build()
                .unwrap();
            runtime.block_on(async {
                tokio::time::timeout(SLOW_ROUND * 2, watchdog.slowed())
                    .await
                    .is_ok()
            })
        };
        assert!(slowed, "the watchdog reports a slow round while it runs");
        // The media stays slow after the round ends, then recovers.
        assert!(!watchdog.responsive());
        assert!(active.load(Ordering::Acquire));
        watchdog.slow_until.store(watchdog.now(), Ordering::Release);
        assert!(watchdog.responsive());
        active.store(false, Ordering::Release);
    }
}
