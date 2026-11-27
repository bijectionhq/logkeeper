//! Parking idle streams.
//!
//! An idle stream's group still runs timers and heartbeats on every voter.
//! Once a stream has served no client and appended nothing for the park
//! delay, its leader asks each follower that matches its whole log to park
//! the stream: close the group and keep only a mark. When every follower has
//! parked, the leader parks too. A parked follower answers empty heartbeats
//! as busy without opening the group; entries, votes, snapshots and client
//! requests reopen it. The voter that led the stream restores its
//! leadership as soon as it reopens, so waking costs one vote round rather
//! than an election timeout. A follower whose keeper is dead is skipped.

use std::time::Duration;

use journal_contract::StreamId;
use openraft::{ServerState, async_runtime::WatchReceiver};
use tokio::time::Instant;

use super::{Engine, Group};
use crate::stream::consensus::{
    LogId, NodeId, Vote,
    network::{Frame, PeerRequest},
};

const PARK_TIMEOUT: Duration = Duration::from_secs(2);

impl Engine {
    /// Whether `group` served no client and grew no log for the park delay.
    /// The replicated catalog is never idle.
    fn idle(&self, group: &Group, now: Instant) -> bool {
        if self.catalog_stream.is_some() && group.genesis.stream == super::catalog_stream::STREAM {
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
        now.duration_since(entry.1) >= self.park_after
            && now.duration_since(*group.used.lock()) >= self.park_after
            && metrics.last_applied.map(|applied| applied.index) == metrics.last_log_index
            && metrics
                .membership_config
                .membership()
                .get_joint_config()
                .len()
                == 1
            && group
                .snapshot_receive
                .try_lock()
                .is_ok_and(|receive| receive.is_none())
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
            if metrics.state != ServerState::Leader || !group.settled_except(&dead) || !idle {
                continue;
            }
            let stream = group.genesis.stream;
            let (vote, last) = (metrics.vote, metrics.last_applied);
            let followers = metrics
                .membership_config
                .membership()
                .voter_ids()
                .filter(|id| *id != self.id.as_u128())
                .collect::<Vec<_>>();
            let mut parked = true;
            for follower in followers {
                // A dead follower cannot answer. Parking without it keeps a
                // zone outage from holding every stream awake; the wake
                // sweep reopens the stream for repair.
                if self.dead(uuid::Uuid::from_u128(follower)) {
                    continue;
                }
                let frame = Frame::Peer(group.genesis.clone(), PeerRequest::Park { vote, last });
                let accepted: bool = self
                    .control
                    .call(uuid::Uuid::from_u128(follower), frame, PARK_TIMEOUT)
                    .await
                    .unwrap_or(false);
                parked &= accepted;
            }
            if parked {
                self.park(stream).await;
            } else {
                super::super::metrics::count(&super::super::metrics::COUNTERS.park_declined);
            }
        }
    }

    pub(super) async fn park(&self, stream: StreamId) {
        let parked = self
            .close_retaining(stream, || {
                self.parked.write().insert(stream);
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
        let ready = metrics.state == ServerState::Follower
            && metrics.vote == vote
            && metrics.last_applied == last
            && metrics.last_log_index == last.map(|log| log.index)
            && self.idle(group, Instant::now());
        if ready {
            self.park(group.genesis.stream).await;
        }
        ready
    }
}
