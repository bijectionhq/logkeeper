//! Keeper identity across media installations.
//!
//! A keeper's vote and log live on its data volume, and its enrollment in
//! the registry. A keeper that lost both and was installed again under its
//! old ID would come back as an empty voter: it would register the streams
//! its peers name it in and grant votes as if it had never acknowledged an
//! entry, so a lagging voter could win and erase a committed one.
//!
//! Each installation draws a new media incarnation. Liveness pings carry
//! the sender's, and each keeper records the incarnation it first sees each
//! peer under, durably in its registry. A ping's answer names the
//! incarnation the receiver first saw the sender under. A keeper told that
//! a peer knows it under another incarnation marks itself reused, durably,
//! and from then on registers no replica it does not hold: it takes copies
//! only through staging, as any replacement does. Until one peer answered
//! without such a report, it registers none either. Peers that see another
//! incarnation also stop counting its vote grants.

use std::{
    collections::HashSet,
    io,
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use uuid::Uuid;

use crate::stream::consensus::{NodeId, decisions, storage::Incarnations};

pub(super) struct Recognition {
    /// This keeper's media incarnation.
    own: Uuid,
    path: PathBuf,
    /// The durable record, held while it is stored so stores keep order,
    /// and whether it changed since its last successful store.
    record: tokio::sync::Mutex<(Incarnations, bool)>,
    /// Peers seen under another incarnation, shared with each group's
    /// network.
    reincarnated: Arc<parking_lot::RwLock<HashSet<NodeId>>>,
    /// Whether a peer answered a ping since this keeper started.
    confirmed: AtomicBool,
    /// Whether a peer knows this keeper under another incarnation.
    reused: AtomicBool,
    /// Serializes the pings that wait for confirmation.
    checking: tokio::sync::Mutex<()>,
    /// Ignores reused keeper IDs, as keepers did before incarnations, so
    /// the fault harness can show it still finds Raft amnesia.
    #[cfg(test)]
    ignore_reuse: AtomicBool,
}

impl Recognition {
    pub fn open(registry: &Path, keeper: Uuid, own: Uuid) -> io::Result<Self> {
        let path = Incarnations::path(registry, keeper);
        let record = Incarnations::load(&path)?;
        Ok(Self {
            own,
            path,
            reincarnated: Arc::new(parking_lot::RwLock::new(
                record.reincarnated.iter().map(Uuid::as_u128).collect(),
            )),
            confirmed: AtomicBool::new(false),
            reused: AtomicBool::new(record.reused),
            record: tokio::sync::Mutex::new((record, false)),
            checking: tokio::sync::Mutex::new(()),
            #[cfg(test)]
            ignore_reuse: AtomicBool::new(false),
        })
    }

    /// Stops recognizing reused keeper IDs: no peer is marked reincarnated
    /// and this keeper never marks itself reused.
    #[cfg(test)]
    pub fn ignore_reuse(&self) {
        self.ignore_reuse.store(true, Ordering::Release);
    }

    #[cfg(test)]
    fn ignoring_reuse(&self) -> bool {
        self.ignore_reuse.load(Ordering::Acquire)
    }

    #[cfg(not(test))]
    fn ignoring_reuse(&self) -> bool {
        false
    }

    pub fn own(&self) -> Uuid {
        self.own
    }

    pub fn reincarnated_peers(&self) -> Arc<parking_lot::RwLock<HashSet<NodeId>>> {
        self.reincarnated.clone()
    }

    pub fn confirmed(&self) -> bool {
        self.confirmed.load(Ordering::Acquire)
    }

    pub fn reused(&self) -> bool {
        self.reused.load(Ordering::Acquire)
    }

    #[cfg(test)]
    pub async fn recorded(&self, peer: Uuid) -> Option<Uuid> {
        self.record.lock().await.0.peers.get(&peer).copied()
    }

    /// Whether this keeper may register a replica it does not hold.
    pub fn registers(&self, genesis_voter: bool) -> bool {
        decisions::registers(genesis_voter, self.confirmed(), self.reused())
    }

    /// The incarnation this keeper first saw `peer` under, which it records
    /// on first contact.
    pub async fn greet(&self, peer: Uuid, incarnation: Uuid) -> Option<Uuid> {
        let mut guard = self.record.lock().await;
        let (record, unsaved) = &mut *guard;
        let known = record.peers.get(&peer).copied();
        *unsaved |= self.note(record, peer, incarnation);
        self.store(record, unsaved).await;
        known
    }

    /// Records what the peers that answered this keeper's pings reported:
    /// each peer's incarnation, and the one each first saw this keeper
    /// under. Confirms this keeper's identity when one peer answered and none
    /// knows it under another incarnation.
    pub async fn answered(&self, answers: &[(Uuid, Uuid, Option<Uuid>)]) {
        if answers.is_empty() {
            return;
        }
        let mut guard = self.record.lock().await;
        let (record, unsaved) = &mut *guard;
        for (peer, incarnation, _) in answers {
            *unsaved |= self.note(record, *peer, *incarnation);
        }
        if let Some((peer, _, known)) = answers.iter().find(|(_, _, known)| {
            decisions::reincarnated(known.map(|known| known.as_u128()), self.own.as_u128())
        }) && !record.reused
            && !self.ignoring_reuse()
        {
            record.reused = true;
            *unsaved = true;
            tracing::error!(
                peer = %peer,
                known = ?known,
                incarnation = %self.own,
                "a peer knows this keeper under another incarnation: its media was installed \
                 again under a used keeper ID, so it registers no replica it does not hold; \
                 give it a new keeper ID"
            );
        }
        // Reuse is recorded before it takes effect, and takes effect before
        // the confirmation can.
        self.store(record, unsaved).await;
        if record.reused {
            self.reused.store(true, Ordering::Release);
        } else {
            self.confirmed.store(true, Ordering::Release);
        }
    }

    /// Marks this keeper reused because `source`, an authority other than
    /// its peers, knows its ID under another incarnation.
    pub async fn mark_reused(&self, source: &str) {
        if self.reused() || self.ignoring_reuse() {
            return;
        }
        let mut guard = self.record.lock().await;
        let (record, unsaved) = &mut *guard;
        if !record.reused {
            record.reused = true;
            *unsaved = true;
            tracing::error!(
                source = source,
                incarnation = %self.own,
                "{source} knows this keeper under another incarnation: its media was installed \
                 again under a used keeper ID, so it registers no replica it does not hold; \
                 give it a new keeper ID"
            );
        }
        self.store(record, unsaved).await;
        self.reused.store(true, Ordering::Release);
    }

    /// Records `peer`'s incarnation on first contact and marks the peer
    /// when it differs from the first. Whether the record changed.
    fn note(&self, record: &mut Incarnations, peer: Uuid, incarnation: Uuid) -> bool {
        let mut changed = false;
        let first = *record.peers.entry(peer).or_insert_with(|| {
            changed = true;
            incarnation
        });
        if decisions::reincarnated(Some(first.as_u128()), incarnation.as_u128())
            && !self.ignoring_reuse()
            && record.reincarnated.insert(peer)
        {
            changed = true;
            self.reincarnated.write().insert(peer.as_u128());
            tracing::warn!(
                peer = %peer,
                incarnation = %incarnation,
                first = %first,
                "peer answered under a new incarnation: its votes no longer count"
            );
        }
        changed
    }

    /// Stores the record when it changed. A failed store leaves the change
    /// in memory, and the next exchange stores it again.
    async fn store(&self, record: &Incarnations, unsaved: &mut bool) {
        if !*unsaved {
            return;
        }
        let path = self.path.clone();
        let current = record.clone();
        match tokio::task::spawn_blocking(move || current.store(&path)).await {
            Ok(Ok(())) => *unsaved = false,
            Ok(Err(error)) => {
                tracing::warn!(error = %error, "could not record peer incarnations")
            }
            Err(error) => tracing::warn!(error = %error, "could not record peer incarnations"),
        }
    }

    /// Holds the right to ping for a confirmation, or `None` once the
    /// identity check is over.
    pub async fn checking(&self) -> Option<tokio::sync::MutexGuard<'_, ()>> {
        if self.confirmed() || self.reused() {
            return None;
        }
        let checking = self.checking.lock().await;
        (!self.confirmed() && !self.reused()).then_some(checking)
    }
}
