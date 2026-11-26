//! Keeper status and leader-driven repair of dead voters.
//!
//! Each stream's leader watches when every voter last acknowledged it. A
//! voter silent for the repair delay whose keeper does not answer, or that
//! answers without a healthy replica, is replaced by the best-ranked live
//! keeper with room in a free failure domain. Nothing moves without two live
//! voters, and a keeper moves at most one voter per pass.

use std::{collections::BTreeMap, time::Duration};

use journal_contract::StreamId;
use openraft::{Instant as _, ServerState, async_runtime::WatchReceiver};
use tokio::time::{Instant, timeout};
use uuid::Uuid;

use super::{Engine, Reply, Request};
use crate::stream::consensus::{
    KeeperStatus,
    assignment::{self, Health, View},
    network::Frame,
};

#[cfg(not(test))]
const REPAIR_INTERVAL: Duration = Duration::from_secs(30);
#[cfg(test)]
const REPAIR_INTERVAL: Duration = Duration::from_millis(500);
const STATUS_TIMEOUT: Duration = Duration::from_secs(2);

impl Engine {
    pub(super) async fn status(&self, stream: StreamId) -> KeeperStatus {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let led = groups
            .iter()
            .filter(|group| group.raft.metrics().borrow_watched().state == ServerState::Leader)
            .count();
        let replica = if self.quarantined.read().contains(&stream) {
            Some(false)
        } else {
            groups
                .iter()
                .find(|group| group.genesis.stream == stream)
                .map(|group| group.state.healthy())
        };
        KeeperStatus {
            keeper: self.id,
            accepting: self.disk.healthy() && self.disk.space.accepts_streams(),
            streams: groups.len() as u32,
            led: led as u32,
            replica,
        }
    }

    async fn peer_status(&self, keeper: Uuid, stream: StreamId) -> Option<KeeperStatus> {
        if keeper == self.id {
            return Some(self.status(stream).await);
        }
        match timeout(
            STATUS_TIMEOUT,
            self.rpc.call(
                keeper,
                Frame::Client(Request::KeeperStatus(stream)),
                STATUS_TIMEOUT,
            ),
        )
        .await
        {
            Ok(Ok(Reply::Status(status))) if status.keeper == keeper => Some(status),
            _ => None,
        }
    }

    pub(super) async fn repair_loop(&self) {
        let mut schedule = tokio::time::interval(REPAIR_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => {
                    self.shed_leadership_when_full().await;
                    self.repair_once().await;
                    self.retire_removed().await;
                    self.park_idle().await;
                }
            }
        }
    }

    /// A keeper whose media is unhealthy or full cannot accept the writes of
    /// the streams it leads, even when their followers have room. It hands
    /// each to a follower that has matched its log and whose keeper accepts
    /// streams.
    async fn shed_leadership_when_full(&self) {
        if self.disk.healthy() && self.disk.space.accepts_streams() {
            return;
        }
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for group in groups {
            let metrics = group.raft.metrics().borrow_watched().clone();
            if metrics.state != ServerState::Leader {
                continue;
            }
            let matched = metrics
                .replication
                .iter()
                .flatten()
                .filter(|(id, log)| {
                    **id != metrics.id && log.map(|log| log.index) == metrics.last_log_index
                })
                .map(|(id, _)| Uuid::from_u128(*id))
                .collect::<Vec<_>>();
            for target in matched {
                if self
                    .peer_status(target, group.genesis.stream)
                    .await
                    .is_some_and(|status| status.accepting)
                {
                    let _ = group.raft.trigger().transfer_leader(target.as_u128()).await;
                    break;
                }
            }
        }
    }

    /// Retires this keeper's copy of a stream that has heard from no leader
    /// for the repair delay and whose current placement, certified by another
    /// keeper, no longer names this keeper. That copy belongs to a voter
    /// replaced while it was down or moved off by a drain.
    async fn retire_removed(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .iter()
            .map(|(stream, group)| (*stream, group.clone()))
            .collect::<Vec<_>>();
        let now = Instant::now();
        let orphaned = groups
            .iter()
            .filter(|(_, group)| {
                group.raft.metrics().borrow_watched().state != ServerState::Leader
                    && now.duration_since(*group.heard.lock()) >= self.repair_after
            })
            .cloned()
            .collect::<Vec<_>>();
        for (stream, group) in orphaned {
            let Some(generation) = self
                .disk
                .ownership(stream)
                .and_then(|book| book.generation())
            else {
                continue;
            };
            for authority in self.placement.domains().keys().copied() {
                if authority == self.id {
                    continue;
                }
                let Ok(proof) = self.verified_proof(authority, &group.genesis).await else {
                    continue;
                };
                let named = proof.configuration.voters.contains(&self.id)
                    || proof.joint.is_some_and(|roster| roster.contains(&self.id));
                if !named {
                    let result = self
                        .retire_copy(stream, authority, proof.configuration.revision, generation)
                        .await;
                    eprintln!(
                        "logkeeper retired its removed copy of stream {stream:?}: {}",
                        match result {
                            Ok(_) => "retired".to_owned(),
                            Err(error) => error.to_string(),
                        }
                    );
                }
                break;
            }
        }
    }

    /// Repairs at most one stream this keeper leads.
    async fn repair_once(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .iter()
            .map(|(stream, group)| (*stream, group.clone()))
            .collect::<Vec<_>>();
        let now = Instant::now();
        let mut silent = Vec::new();
        {
            let mut led = self.led_since.lock();
            led.retain(|stream, _| groups.iter().any(|(open, _)| open == stream));
            for (stream, group) in &groups {
                let metrics = group.raft.metrics().borrow_watched().clone();
                if metrics.state != ServerState::Leader
                    || metrics
                        .membership_config
                        .membership()
                        .get_joint_config()
                        .len()
                        != 1
                {
                    led.remove(stream);
                    continue;
                }
                let term = metrics.current_term;
                let since = match led.get(stream) {
                    Some((led_term, since)) if *led_term == term => *since,
                    _ => {
                        led.insert(*stream, (term, now));
                        now
                    }
                };
                let Some(heartbeat) = metrics.heartbeat.as_ref() else {
                    continue;
                };
                let quiet = heartbeat
                    .iter()
                    .filter(|(id, _)| **id != self.id.as_u128())
                    .filter(|(_, acked)| match acked {
                        Some(acked) => acked.elapsed() >= self.repair_after,
                        None => now.duration_since(since) >= self.repair_after,
                    })
                    .map(|(id, _)| Uuid::from_u128(*id))
                    .collect::<Vec<_>>();
                if !quiet.is_empty() {
                    silent.push((*stream, group.clone(), quiet));
                }
            }
        }
        for (stream, group, quiet) in silent {
            let Ok((_, configuration, _, _)) = group.state.placement() else {
                continue;
            };
            let mut health = BTreeMap::new();
            for keeper in self.placement.domains().keys().copied() {
                let voter = configuration.voters.contains(&keeper);
                if voter && !quiet.contains(&keeper) {
                    continue;
                }
                let status = self.peer_status(keeper, stream).await;
                let live = status.is_some_and(|status| !voter || status.replica == Some(true));
                health.insert(
                    keeper,
                    Health {
                        live,
                        accepting: status.is_some_and(|status| status.accepting),
                        streams: status.map_or(0, |status| status.streams),
                    },
                );
            }
            let view = View {
                eligible: self.placement.domains(),
                health: &health,
            };
            let Some(next) = assignment::repair_roster(stream, configuration.voters, &view) else {
                continue;
            };
            let result = self.replace(&group, configuration.revision, next).await;
            eprintln!(
                "logkeeper repair of stream {stream:?}: {:?} to {next:?}: {}",
                configuration.voters,
                match result {
                    Ok(Reply::Decision(_)) => "replaced".to_owned(),
                    Ok(_) => "refused".to_owned(),
                    Err(error) => error.to_string(),
                }
            );
            return;
        }
    }
}
