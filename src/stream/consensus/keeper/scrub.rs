use std::{io, sync::Arc, time::Duration};

use tokio::time::{Instant, MissedTickBehavior};

use super::Engine;
use crate::stream::consensus::{
    invalid, logging, metrics,
    storage::scrub::{CHUNK, Failure, Scrub},
};

pub(super) const DEFAULT_BYTES_PER_SECOND: u64 = 2 * 1024 * 1024;
#[cfg(not(test))]
const PASS_PAUSE: Duration = Duration::from_secs(60);
#[cfg(test)]
const PASS_PAUSE: Duration = Duration::from_millis(200);

impl Engine {
    pub(super) async fn scrub_loop(self: &Arc<Self>) {
        if self.scrub_rate == 0 {
            self.stop.cancelled().await;
            return;
        }
        let seconds = (CHUNK as f64 / self.scrub_rate as f64).max(0.05);
        let interval = Duration::from_secs_f64(seconds);
        let budget = ((self.scrub_rate as f64 * seconds) as usize).clamp(CHUNK, 4 << 20);
        let mut schedule = tokio::time::interval_at(Instant::now() + interval, interval);
        schedule.set_missed_tick_behavior(MissedTickBehavior::Skip);
        let mut scrub = Scrub::default();
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => {}
            }
            if !self.disk.responsive() || self.disk.near_slow() {
                continue;
            }
            let disk = self.disk.clone();
            let result = tokio::task::spawn_blocking(move || {
                let (failure, complete) = scrub.pass(&disk, budget);
                (scrub, failure, complete)
            })
            .await;
            let (next, failure, complete) = match result {
                Ok(result) => result,
                Err(error) => {
                    tracing::error!(keeper = %self.id, %error, "online integrity scrub worker stopped");
                    return;
                }
            };
            scrub = next;
            if let Some(failure) = failure {
                self.scrub_failure(failure).await;
            }
            if complete {
                metrics::count(&self.disk.metrics.scrub_passes);
                tokio::select! {
                    () = self.stop.cancelled() => return,
                    () = tokio::time::sleep(PASS_PAUSE) => schedule.reset(),
                }
            }
        }
    }

    async fn scrub_failure(self: &Arc<Self>, failure: Failure) {
        let scope = failure.scope;
        let Ok(opening) = self.opening(scope).await else {
            return;
        };
        let Ok(guard) = opening.try_lock_owned() else {
            return;
        };
        if self.is_quarantined(scope) || !failure.current(&self.disk) {
            return;
        }
        if !matches!(
            failure.error.kind(),
            io::ErrorKind::InvalidData | io::ErrorKind::NotFound | io::ErrorKind::UnexpectedEof
        ) {
            if let Some(dropped) = logging::rate_limit("keeper.scrub_read", Some(scope)) {
                tracing::warn!(keeper = %self.id, stream = %logging::stream_uuid(scope),
                    error = %failure.error, dropped, "online integrity scrub could not read selected data");
            }
            return;
        }
        let Ok(media) = self.disk.hold_media_lock() else {
            return;
        };
        if let Some(group) = self.groups.lock().await.get(&scope) {
            group.state.suspend();
        }
        let engine = self.clone();
        let marked = tokio::task::spawn_blocking(move || {
            // A serving task may be cancelled during fsync. Keep the
            // enrollment locked until the write completes.
            let _media = media;
            engine.quarantine(
                scope,
                &invalid(format!("integrity scrub: {}", failure.error)),
            );
            metrics::count(&engine.disk.metrics.scrub_corrupt);
            guard
        })
        .await;
        if let Ok(_guard) = marked {
            // The opening lock excludes a concurrent replacement or reopen.
            self.close_copy(scope).await;
        }
    }
}
