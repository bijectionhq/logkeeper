//! Placement certification, which fences the voters an operator recovery
//! lost.
//!
//! A recovery makes the survivor's copy the only history without a quorum
//! of the configuration it leaves. The two lost voters may still hold a
//! suffix the recovered stream no longer has, and together they are a
//! quorum of that configuration: Raft cannot tell them from a healthy pair.
//! So a copy this keeper process has not certified neither campaigns (its
//! network sends no vote or pre-vote) nor serves reads
//! (`decisions::serves_reads`). A copy is certified, until it closes, by:
//!
//! - an append its leader's vote does not lose to: that leader campaigned
//!   certified;
//! - a bootstrap that registers it, empty, from the catalog;
//! - the catalog. The certifier asks for the stream's latest staged move,
//!   which every move and every recovery records before it changes the
//!   stream, and `decisions::fences_copy` fences a copy whose effective
//!   configuration is neither side of that move, or the configuration a
//!   recovery lost. A fenced copy retires on a certified placement proof.
//!
//! Certification lives in memory, keyed by the copy's generation, and
//! survives parking. Only a copy that opened in this process without
//! hearing a leader asks the catalog, so a stream's normal path makes no
//! catalog round trip, and a catalog outage holds back only such copies.
//! The replicated catalog stream certifies itself: it cannot ask itself.

use std::{sync::Arc, time::Duration};

use journal_contract::StreamId;
use openraft::async_runtime::WatchReceiver;

use super::{Engine, Group, Outcome, Reply, Request, catalog_stream};
use crate::stream::consensus::Voters;
use crate::stream::consensus::{Stage, decisions};

/// How often the certifier looks for copies that still need certification,
/// besides the wake-ups of copies that tried to campaign or serve.
#[cfg(not(test))]
const CERTIFY_INTERVAL: Duration = Duration::from_secs(5);
#[cfg(test)]
const CERTIFY_INTERVAL: Duration = Duration::from_millis(250);
/// Catalog requests one certification pass makes at once.
const CERTIFY_BATCH: usize = 32;

/// The copies this keeper certified or the catalog fenced, by generation.
#[derive(Default)]
pub(super) struct Certification {
    certified: parking_lot::RwLock<std::collections::HashMap<StreamId, u64>>,
    fenced: parking_lot::RwLock<std::collections::HashMap<StreamId, u64>>,
    /// Wakes the certifier when an uncertified copy tried to campaign or
    /// serve a read.
    pub wake: tokio::sync::Notify,
}

impl Certification {
    /// Whether this process certified `generation` of `stream`.
    pub fn certified(&self, stream: StreamId, generation: u64) -> bool {
        stream == catalog_stream::STREAM || self.certified.read().get(&stream) == Some(&generation)
    }

    /// Certifies `generation` of `stream` until that copy closes.
    pub fn certify(&self, stream: StreamId, generation: u64) {
        if self.certified.read().get(&stream) != Some(&generation) {
            self.certified.write().insert(stream, generation);
        }
    }

    /// Whether the catalog fenced `generation` of `stream`.
    pub fn fenced(&self, stream: StreamId, generation: u64) -> bool {
        self.fenced.read().get(&stream) == Some(&generation)
    }

    /// Fences `generation` of `stream`, as the catalog's keeper record did.
    pub fn fence(&self, stream: StreamId, generation: u64) {
        self.certified.write().remove(&stream);
        self.fenced.write().insert(stream, generation);
    }

    /// Clears a fence that a certified placement proof contradicted.
    pub fn unfence(&self, stream: StreamId) {
        self.fenced.write().remove(&stream);
    }

    /// Forgets every certification and fence, as a bump of this keeper's
    /// epoch requires: each copy certifies again.
    pub fn reset(&self) {
        self.certified.write().clear();
        self.fenced.write().clear();
        self.wake.notify_one();
    }

    /// Forgets a copy that closed for good.
    pub fn forget(&self, stream: StreamId) {
        self.certified.write().remove(&stream);
        self.fenced.write().remove(&stream);
    }

    /// Whether a copy about to campaign or serve is certified; when it is
    /// not, wakes the certifier.
    pub fn require(&self, stream: StreamId, generation: u64) -> bool {
        let certified = self.certified(stream, generation);
        if !certified {
            self.wake.notify_one();
        }
        certified
    }
}

impl Engine {
    /// Whether this keeper certified its open copy of the group's stream.
    pub(super) fn certified(&self, group: &Group) -> bool {
        self.certification
            .require(group.genesis.stream, group.state.generation())
    }

    /// Certifies every open copy that needs it, at each wake-up and
    /// interval, until the keeper stops.
    pub(super) async fn certify_loop(self: &Arc<Self>) {
        let mut schedule = tokio::time::interval(CERTIFY_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = self.certification.wake.notified() => (),
                _ = schedule.tick() => (),
            }
            self.certify_pending().await;
        }
    }

    async fn certify_pending(&self) {
        let pending = self
            .groups
            .lock()
            .await
            .values()
            .filter(|group| {
                let (stream, generation) = (group.genesis.stream, group.state.generation());
                !self.certification.certified(stream, generation)
                    && !self.certification.fenced(stream, generation)
            })
            .cloned()
            .collect::<Vec<_>>();
        for batch in pending.chunks(CERTIFY_BATCH) {
            futures::future::join_all(batch.iter().map(|group| self.certify_copy(group))).await;
        }
    }

    /// Asks the catalog for the stream's latest staged move and certifies
    /// or fences the copy. An unavailable catalog leaves it uncertified.
    async fn certify_copy(&self, group: &Group) {
        let stream = group.genesis.stream;
        let generation = group.state.generation();
        let staged = match self.catalog_request(Request::Staging(stream)).await {
            Ok(Reply::Staged(stage)) if stage.stream == stream => Some(stage),
            Ok(Reply::Decision(Outcome::Unit)) => None,
            _ => return,
        };
        // An append may have certified the copy while the catalog answered.
        if self.certification.certified(stream, generation) {
            return;
        }
        // A copy the catalog's latest recovery goes on from refuses
        // the voters it lost, also once a restart compacted the recovery away
        // from its own log.
        if let Some(stage) = staged
            .as_ref()
            .filter(|stage| stage.target.contains(&self.id))
        {
            self.exclusions.install(
                stream,
                &crate::stream::consensus::storage::recovery_fenced(stage),
                stage.source.saturating_add(1),
            );
        }
        let fenced = staged.as_ref().is_some_and(|stage| {
            let metrics = group.raft.metrics();
            let current = metrics.borrow_watched();
            fences(
                current.membership_config.membership().get_joint_config(),
                stage,
            )
        });
        if fenced {
            tracing::warn!(
                keeper = %self.id,
                stream = %crate::stream::consensus::logging::stream_uuid(stream),
                staged = ?staged.map(|stage| (stage.source, stage.old, stage.target)),
                "fenced this copy: the catalog's latest move leaves its configuration"
            );
            self.certification.fenced.write().insert(stream, generation);
            self.retire_now.notify_one();
        } else {
            self.certification.certify(stream, generation);
        }
    }
}

/// Whether `stage`, the catalog's latest move, fences a copy whose effective
/// membership has the voter sets `configs`.
fn fences(configs: &[std::collections::BTreeSet<u128>], stage: &Stage) -> bool {
    let set = |voters: Voters| voters.map(|id| id.as_u128()).into_iter().collect();
    let (old, target): (std::collections::BTreeSet<u128>, _) = (set(stage.old), set(stage.target));
    let uniform =
        |voters: &std::collections::BTreeSet<u128>| matches!(configs, [only] if only == voters);
    decisions::fences_copy(
        !configs.is_empty(),
        stage.recovery(),
        uniform(&old),
        uniform(&target),
        matches!(configs, [from, to] if *from == old && *to == target),
    )
}
