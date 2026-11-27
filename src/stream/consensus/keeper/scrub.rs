use std::{io, sync::Arc, time::Duration};

use tokio::time::{Instant, MissedTickBehavior};

use super::Engine;
use crate::stream::consensus::{invalid, logging, metrics, storage::scrub::Scrub};

impl Engine {
    pub(super) async fn scrub_loop(self: &Arc<Self>) {
        let interval = Duration::from_secs(1);
        let mut schedule = tokio::time::interval_at(Instant::now() + interval, interval);
        schedule.set_missed_tick_behavior(MissedTickBehavior::Skip);
        let mut scrub = Scrub::default();
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => {}
            }
            if !self.disk.responsive() {
                continue;
            }
            let disk = self.disk.clone();
            let result = tokio::task::spawn_blocking(move || {
                let failure = scrub.pass(&disk);
                (scrub, failure)
            })
            .await;
            let (next, failure) = match result {
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
        }
    }

    async fn scrub_failure(
        self: &Arc<Self>,
        failure: crate::stream::consensus::storage::scrub::Failure,
    ) {
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
            tracing::warn!(keeper = %self.id, stream = %logging::stream_uuid(scope),
                error = %failure.error, "online integrity scrub could not read selected data");
            return;
        }
        if let Some(group) = self.groups.lock().await.get(&scope) {
            group.state.suspend();
        }
        let engine = self.clone();
        let marked = tokio::task::spawn_blocking(move || {
            engine.quarantine(
                scope,
                &invalid(format!("integrity scrub: {}", failure.error)),
            );
            metrics::count(&engine.disk.metrics.scrub_corruptions);
            guard
        })
        .await;
        if let Ok(_guard) = marked {
            // The opening lock excludes a concurrent replacement or reopen.
            self.close_copy(scope).await;
        }
    }
}
