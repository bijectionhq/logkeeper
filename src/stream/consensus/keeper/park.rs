//! Parking idle streams.
//!
//! An idle stream's group still runs timers and heartbeats on every voter.
//! Once a stream has served no client and appended nothing for the park
//! delay, its leader asks each follower that matches its whole log to park
//! the stream: close the group and keep only a mark. When every follower has
//! parked, the leader parks too, unless a repair, a write or a vote started
//! meanwhile. A parked follower answers empty heartbeats as busy without
//! opening the group; entries, votes, snapshots and client requests reopen
//! it, and so do heartbeats that outlast the park round, which come from a
//! leader that stayed open because another follower declined. A leader
//! whose park was declined waits the park delay before asking again. The
//! voter that led the stream restores its leadership as soon as it reopens,
//! so waking costs one vote round rather than an election timeout. A
//! follower whose keeper is dead is skipped.

use std::time::Duration;

use journal_contract::StreamId;
use openraft::{ServerState, async_runtime::WatchReceiver};
use tokio::time::Instant;

use super::{Engine, Group};
use crate::stream::consensus::{
    LogId, NodeId, Vote, decisions,
    network::{Frame, PeerRequest},
};

const PARK_TIMEOUT: Duration = Duration::from_secs(2);
/// How long a parked follower refuses empty heartbeats. A leader asks its
/// followers at once and parks within `PARK_TIMEOUT`, so heartbeats after
/// twice that come from a leader that did not park.
pub(super) const PARKED_HEARTBEATS: Duration = Duration::from_secs(4);

impl Engine {
    /// Whether `group` served no client, grew no log and ran no repair for
    /// the park delay. The replicated catalog is never idle.
    fn idle(&self, group: &Group, now: Instant) -> bool {
        if self.catalog_stream.is_some() && group.genesis.stream == super::catalog_stream::STREAM {
            return false;
        }
        if self.repairing(group.genesis.stream) || group.membership.try_lock().is_err() {
            return false;
        }
        let metrics = group.raft.metrics().borrow_watched().clone();
        let mut activity = self.activity.lock();
        let entry = activity
            .entry(group.genesis.stream)
            .or_insert((metrics.last_log_index, now));
        if entry.0 != metrics.last_log_index {
            *entry = (metrics.last_log_index, now);
        }
        let quiet = now.duration_since(entry.1).as_nanos();
        drop(activity);
        decisions::idle(
            quiet,
            now.duration_since(*group.used.lock()).as_nanos(),
            self.park_after.as_nanos(),
            metrics.last_applied.map(|applied| applied.index),
            metrics.last_log_index,
            metrics
                .membership_config
                .membership()
                .get_joint_config()
                .len()
                == 1,
            !group
                .snapshot_receive
                .try_lock()
                .is_ok_and(|receive| receive.is_none()),
        )
    }

    /// Parks every idle stream this keeper leads.
    pub(super) async fn park_idle(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let now = Instant::now();
        self.activity
            .lock()
            .retain(|stream, _| groups.iter().any(|group| group.genesis.stream == *stream));
        // Every replica tracks its own activity, so a follower asked to park
        // already knows how long it has been idle.
        let idle = groups
            .iter()
            .map(|group| self.idle(group, now))
            .collect::<Vec<_>>();
        for (group, idle) in groups.into_iter().zip(idle) {
            let metrics = group.raft.metrics().borrow_watched().clone();
            let dead = |id: NodeId| self.dead(uuid::Uuid::from_u128(id));
            if !decisions::leader_parks(
                metrics.state == ServerState::Leader,
                group.settled_except(&dead),
                idle,
            ) {
                continue;
            }
            let stream = group.genesis.stream;
            let (vote, last) = (metrics.vote, metrics.last_applied);
            // A dead follower cannot answer. Parking without it keeps a zone
            // outage from holding every stream awake; the wake sweep reopens
            // the stream for repair.
            let followers = metrics
                .membership_config
                .membership()
                .voter_ids()
                .filter(|id| *id != self.id.as_u128())
                .map(uuid::Uuid::from_u128)
                .filter(|follower| !self.dead(*follower))
                .collect::<Vec<_>>();
            // Asked at once, so the round ends within `PARK_TIMEOUT` and a
            // follower that parked for nothing reopens soon after.
            let answers = futures::future::join_all(followers.into_iter().map(|follower| {
                let frame = Frame::Peer(group.genesis.clone(), PeerRequest::Park { vote, last });
                self.control.call::<bool>(follower, frame, PARK_TIMEOUT)
            }))
            .await;
            let accepted = answers.into_iter().all(|answer| answer.unwrap_or(false));
            // A repair, a write or a vote may have started while the
            // followers answered. Holding the membership lock keeps a
            // replacement from starting on the group being closed.
            let current = group.raft.metrics().borrow_watched().clone();
            let unchanged = current.vote == vote
                && current.last_applied == last
                && current.last_log_index == metrics.last_log_index;
            let membership = (accepted && unchanged && self.idle(&group, Instant::now()))
                .then(|| group.membership.try_lock().ok())
                .flatten();
            if let Some(_membership) = membership {
                self.park(stream).await;
            } else {
                super::super::metrics::count(&super::super::metrics::COUNTERS.park_declined);
                // Ask again only after another park delay.
                self.activity
                    .lock()
                    .insert(stream, (current.last_log_index, Instant::now()));
            }
        }
    }

    pub(super) async fn park(&self, stream: StreamId) {
        let parked = self
            .close_retaining(stream, || {
                self.parked.write().insert(stream, Instant::now());
            })
            .await;
        if parked {
            super::super::metrics::count(&super::super::metrics::COUNTERS.parked);
        }
        self.activity.lock().remove(&stream);
    }

    /// A follower parks when it is idle itself and holds exactly the
    /// leader's applied log under the leader's vote.
    pub(super) async fn accept_park(&self, group: &Group, vote: Vote, last: Option<LogId>) -> bool {
        let metrics = group.raft.metrics().borrow_watched().clone();
        let ready = decisions::accepts_park(
            metrics.state == ServerState::Follower,
            metrics.vote == vote,
            metrics.last_applied == last,
            metrics.last_log_index,
            last.map(|log| log.index),
            self.idle(group, Instant::now()),
        );
        if ready {
            self.park(group.genesis.stream).await;
        }
        ready
    }
}
