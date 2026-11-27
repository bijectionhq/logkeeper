//! Segment compaction.
//!
//! A WAL segment is deleted once no slice holds it, so one retained record
//! keeps its whole segment. Each pass looks at sealed segments before the
//! published checkpoint whose live slices hold under half their bytes and
//! that only those slices hold (a parked copy's pins, a quarantine or a
//! relocation hold keep a segment out), least live first:
//!
//! 1. Owners first. A stream whose WAL suffix still holds entries there is
//!    asked to snapshot and purge, which frees them without copying. The
//!    segment is left alone for that pass.
//! 2. Then its remaining live slices, which snapshots and applied images
//!    hold, are copied to the active segment grouped by stream, at most
//!    `PASS_BYTES` a pass, drawing on the maintenance floor and suspended
//!    unless ordinary writes keep room for twice the batch.
//! 3. A stream whose selected snapshot may name a moved slice is asked to
//!    snapshot again; its rebuilt snapshot names only the copies, which
//!    releases the segment.
//!
//! Passes run every `PASS_INTERVAL` with up to a fifth of jitter. The model
//! is BookKeeper's `GarbageCollectorThread` with its `EntryLogCompactor`,
//! and raft-engine's purge, which asks owners to compact before it
//! rewrites their entries.

use std::{collections::HashMap, time::Duration};

use tokio::time::Instant;

use super::Engine;

/// A segment is cold once its live slices hold under this share, in percent.
const COLD_SHARE: u64 = 50;
const PASS_INTERVAL: Duration = Duration::from_secs(10);
/// Bytes copied per pass at most, so compaction takes about 1.6 MiB/s.
const PASS_BYTES: u64 = 16 * 1024 * 1024;
/// Streams asked to snapshot and purge per pass at most. Each purge books
/// against the covered budget the keeper's own purges share, so a burst of
/// them must not exhaust it.
const ASKS_PER_PASS: usize = 4;
/// How long owners get to free a segment before its slices are copied.
const OWNER_GRACE: Duration = Duration::from_secs(30);

#[derive(Default)]
pub(super) struct Compaction {
    /// When the owners of each segment were asked to free it.
    asked: HashMap<u64, Instant>,
}

impl Engine {
    pub(super) async fn compaction_loop(&self) {
        loop {
            let jitter =
                uuid::Uuid::new_v4().as_u128() as u64 % (PASS_INTERVAL.as_millis() as u64 / 5);
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = tokio::time::sleep(PASS_INTERVAL + Duration::from_millis(jitter)) => {}
            }
            self.compact_pass(OWNER_GRACE).await;
        }
    }

    /// One compaction pass. Owners asked longer than `grace` ago have had
    /// their chance; their segment's slices are copied.
    pub(super) async fn compact_pass(&self, grace: Duration) {
        self.disk.release_moved_of_detached();
        let mut asks = ASKS_PER_PASS;
        for stream in self.disk.moved_scopes() {
            let group = self.groups.lock().await.get(&stream).cloned();
            if let Some(group) = group
                && asks > 0
            {
                asks -= 1;
                let _ = group.raft.trigger().snapshot().await;
            }
        }
        let now = Instant::now();
        let cold = self.disk.cold_segments(COLD_SHARE);
        self.compaction
            .lock()
            .asked
            .retain(|id, _| cold.contains(id));
        let mut budget = PASS_BYTES;
        for id in cold {
            if budget == 0 {
                break;
            }
            let owners = self.disk.suffix_owners(id);
            let asked = self.compaction.lock().asked.get(&id).copied();
            if !owners.is_empty() && asked.is_none_or(|at| now.duration_since(at) < grace) {
                if asked.is_some() || asks == 0 {
                    // Asked already, or no asks left this pass.
                    continue;
                }
                self.compaction.lock().asked.insert(id, now);
                // Owners past this pass's asks have their slices copied
                // once the grace ends.
                for stream in owners.into_iter().take(asks) {
                    asks -= 1;
                    let group = self.groups.lock().await.get(&stream).cloned();
                    if let Some(group) = group {
                        let _ = group.raft.trigger().snapshot().await;
                        let _ = group.raft.trigger().purge_log(u64::MAX).await;
                    }
                }
                continue;
            }
            match self.disk.relocate_segment(id, budget).await {
                Ok(0) => break,
                Ok(copied) => {
                    super::super::metrics::add(&self.disk.metrics.compacted_bytes, copied);
                    budget = budget.saturating_sub(copied);
                }
                Err(error) => {
                    if let Some(dropped) =
                        crate::stream::consensus::logging::rate_limit("compaction.deferred", None)
                    {
                        tracing::warn!(
                            keeper = %self.id,
                            error = %error,
                            dropped = dropped,
                            "segment compaction deferred"
                        );
                    }
                    break;
                }
            }
        }
    }
}
