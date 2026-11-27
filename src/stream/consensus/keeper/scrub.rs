//! Background scrub (G8).
//!
//! A checksum is only checked when something reads the data, and a stream
//! may keep a record for weeks that nobody reads. So each keeper reads back
//! every retained log slice and selected snapshot of every copy it hosts,
//! open, parked or not yet opened, at `scrub_bytes_per_second` with a fifth
//! of jitter, and starts again after each pass. It waits while the media
//! nears its slow-round gate, so it never pushes a keeper into handing off
//! its leaders. A slice or snapshot that fails its checksum or digest
//! quarantines the copy durably, as a failed read does: the keeper reports
//! it unhealthy, the stream's leader replaces it, and the replaced copy
//! retires. The model is BookKeeper's `ScrubberService`.

use std::time::Duration;

use super::Engine;
use crate::stream::consensus::metrics;

/// The default pace: a 1 TiB keeper is read back about every six days.
pub(super) const DEFAULT_BYTES_PER_SECOND: u64 = 2 * 1024 * 1024;
/// The pause between passes.
#[cfg(not(test))]
const PASS_PAUSE: Duration = Duration::from_secs(60);
#[cfg(test)]
const PASS_PAUSE: Duration = Duration::from_millis(200);
/// How often a paused scrubber looks at the media again.
const GATE_RECHECK: Duration = Duration::from_millis(500);

impl Engine {
    pub(super) async fn scrub_loop(&self) {
        if self.scrub_rate == 0 {
            // The keeper stops when any of its tasks ends, so this one waits.
            self.stop.cancelled().await;
            return;
        }
        loop {
            if !self.scrub_pass().await {
                return;
            }
            metrics::count(&self.disk.metrics.scrub_passes);
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = tokio::time::sleep(jittered(PASS_PAUSE)) => (),
            }
        }
    }

    /// One pass over every hosted copy. False once the keeper stops.
    async fn scrub_pass(&self) -> bool {
        for genesis in self.disk.streams() {
            let stream = genesis.stream;
            if self.disk.is_quarantined(stream) {
                continue;
            }
            for target in self.disk.scrub_targets(stream) {
                while self.disk.near_slow() {
                    tokio::select! {
                        () = self.stop.cancelled() => return false,
                        () = tokio::time::sleep(GATE_RECHECK) => (),
                    }
                }
                let bytes = target.len();
                let checked = tokio::task::spawn_blocking(move || target.verify()).await;
                metrics::add(&self.disk.metrics.scrub_bytes, bytes);
                metrics::count(&self.disk.metrics.scrub_objects);
                if let Ok(Err(error)) = checked
                    && error.kind() == std::io::ErrorKind::InvalidData
                {
                    self.scrub_found_corrupt(stream, &error).await;
                    break;
                }
                let pace = Duration::from_secs_f64(bytes as f64 / self.scrub_rate as f64);
                tokio::select! {
                    () = self.stop.cancelled() => return false,
                    () = tokio::time::sleep(jittered(pace)) => (),
                }
            }
        }
        true
    }

    /// Quarantines `stream`'s copy durably, through its open group when it
    /// has one so that group stops serving at once.
    async fn scrub_found_corrupt(
        &self,
        stream: journal_contract::StreamId,
        error: &std::io::Error,
    ) {
        metrics::count(&self.disk.metrics.scrub_corrupt);
        let reason = format!("scrub: {error}");
        let group = self.groups.lock().await.get(&stream).cloned();
        match group {
            Some(group) => group.state.quarantine_corrupt(&reason),
            None => self.disk.quarantine_stream(stream, &reason),
        }
        self.quarantined.write().insert(stream);
        tracing::error!(
            keeper = %self.id,
            stream = %crate::stream::consensus::logging::stream_uuid(stream),
            error = %error,
            "scrub found a corrupt copy and quarantined it"
        );
    }
}

/// `duration` with up to a fifth added or taken away.
fn jittered(duration: Duration) -> Duration {
    let fifth = duration.as_nanos() as u64 / 5;
    if fifth == 0 {
        return duration;
    }
    let offset = uuid::Uuid::new_v4().as_u128() as u64 % (2 * fifth);
    duration + Duration::from_nanos(offset) - Duration::from_nanos(fifth)
}
