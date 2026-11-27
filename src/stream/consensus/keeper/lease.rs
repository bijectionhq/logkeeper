//! The keeper's liveness lease with the configuration authority.
//!
//! Each keeper renews one lease with the catalog in the background, so the
//! cost does not grow with the number of streams. The lease runs on this
//! keeper's monotonic clock from the moment it sent the renewal the catalog
//! granted, for the lease duration less the drift margin
//! (`decisions::lease_valid`). The catalog waits a whole lease plus the
//! margin after a recovery commits before the recovered configuration
//! serves, so with clock rates within `margin / duration` of each other the
//! holder always counts its lease expired first.
//!
//! A keeper campaigns, leads or serves reads for a stream only while its
//! lease is valid, its epoch is current and the catalog does not fence its
//! copy of the stream (`decisions::holds_authority`). Its network sends no
//! vote, pre-vote, append or snapshot for a stream it holds no authority
//! over, so a leader whose lease lapses commits nothing more and steps down
//! once its quorum check fails, and its request path refuses reads, heads
//! and writes at once. Elections, replication and commits never wait on the
//! catalog: the checks are local.
//!
//! Renewals run one at a time, so an answer never arrives out of order. A
//! renewal refused because the catalog bumped this keeper's epoch ends the
//! lease and every certification this process made: the keeper rejoins
//! under the new epoch and certifies its copies again.
//!
//! Until the cluster finalizes `CLUSTER_VERSION_LEASES` the lease is
//! advisory: the keeper renews and reports it, but the older defences decide
//! alone. The first enforced grant is recorded in the data directory, so a
//! keeper that restarts cut off from the catalog keeps enforcing.
//!
//! The replicated catalog stream itself is never gated: it is the authority.

use std::{
    collections::HashMap,
    io,
    path::{Path, PathBuf},
    sync::Arc,
    sync::atomic::{AtomicBool, AtomicU64, Ordering},
    time::Duration,
};

use journal_contract::StreamId;
use openraft::async_runtime::WatchReceiver;
use tokio::time::{Instant, timeout};

use super::{Engine, Reply, Request, catalog_stream};
use crate::{
    server::durability::{sync_directory, sync_file},
    stream::consensus::{authority::Grant, decisions},
};

/// The marker of a keeper that once held an enforced lease.
pub(super) const ENFORCED_FILE: &str = "lease-enforced";
/// The shortest and longest wait before a failed renewal is retried.
const RETRY_MIN: Duration = Duration::from_millis(100);
const RETRY_MAX: Duration = Duration::from_secs(1);

pub(in crate::stream::consensus) struct Lease {
    duration: Duration,
    margin: Duration,
    base: Instant,
    /// Nanoseconds after `base` when this keeper sent the renewal of its
    /// current lease, plus one; zero without a lease.
    sent: AtomicU64,
    /// The lease and margin of the current grant, in nanoseconds: never
    /// longer, nor a smaller margin, than this keeper's own.
    granted_duration: AtomicU64,
    granted_margin: AtomicU64,
    enforced: AtomicBool,
    epoch: AtomicU64,
    /// False once the catalog reported a newer epoch, until this keeper
    /// rejoins under it.
    current: AtomicBool,
    fenced: parking_lot::RwLock<HashMap<StreamId, u64>>,
    any_fenced: AtomicBool,
    marker: PathBuf,
    /// Nanoseconds after `base` of the last granted renewal, plus one.
    renewed: AtomicU64,
    pub failures: AtomicU64,
    pub lapses: AtomicU64,
    pub refusals: AtomicU64,
    /// Requests refused because this keeper held no authority.
    pub gated: AtomicU64,
    /// Stops renewals, so a test can make the lease lapse.
    #[cfg(test)]
    pub suspended: AtomicBool,
    /// This keeper's clock rate in thousandths of real time, to drift it.
    #[cfg(test)]
    pub rate_permille: AtomicU64,
}

impl Lease {
    pub fn open(data: &Path, duration: Duration, margin: Duration) -> io::Result<Self> {
        let marker = data.join(ENFORCED_FILE);
        let enforced = marker.try_exists()?;
        Ok(Self {
            duration,
            margin,
            base: Instant::now(),
            sent: AtomicU64::new(0),
            granted_duration: AtomicU64::new(nanos(duration)),
            granted_margin: AtomicU64::new(nanos(margin)),
            enforced: AtomicBool::new(enforced),
            epoch: AtomicU64::new(0),
            current: AtomicBool::new(false),
            fenced: parking_lot::RwLock::default(),
            any_fenced: AtomicBool::new(false),
            marker,
            renewed: AtomicU64::new(0),
            failures: AtomicU64::new(0),
            lapses: AtomicU64::new(0),
            refusals: AtomicU64::new(0),
            gated: AtomicU64::new(0),
            #[cfg(test)]
            suspended: AtomicBool::new(false),
            #[cfg(test)]
            rate_permille: AtomicU64::new(1000),
        })
    }

    fn now(&self) -> u64 {
        let elapsed = nanos(self.base.elapsed());
        #[cfg(test)]
        let elapsed = {
            let rate = u128::from(self.rate_permille.load(Ordering::Relaxed));
            u64::try_from(u128::from(elapsed) * rate / 1000).unwrap_or(u64::MAX)
        };
        elapsed
    }

    /// This keeper's monotonic clock as the lease reads it, in nanoseconds.
    fn at(&self, instant: Instant) -> u64 {
        let elapsed = nanos(instant.saturating_duration_since(self.base));
        #[cfg(test)]
        let elapsed = {
            let rate = u128::from(self.rate_permille.load(Ordering::Relaxed));
            u64::try_from(u128::from(elapsed) * rate / 1000).unwrap_or(u64::MAX)
        };
        elapsed
    }

    pub fn duration(&self) -> Duration {
        self.duration
    }

    pub fn margin(&self) -> Duration {
        self.margin
    }

    /// Whether leases are authoritative on this keeper.
    pub fn enforced(&self) -> bool {
        self.enforced.load(Ordering::Acquire)
    }

    /// Whether this keeper holds a valid lease now.
    pub fn valid(&self) -> bool {
        let sent = self.sent.load(Ordering::Acquire);
        sent != 0
            && decisions::lease_valid(
                sent - 1,
                self.granted_duration.load(Ordering::Acquire),
                self.granted_margin.load(Ordering::Acquire),
                self.now(),
            )
    }

    /// The configuration revision below which the catalog fences this
    /// keeper's copy of `stream`.
    pub fn fenced_below(&self, stream: StreamId) -> Option<u64> {
        if !self.any_fenced.load(Ordering::Acquire) {
            return None;
        }
        self.fenced.read().get(&stream).copied()
    }

    /// Whether this keeper may campaign, lead or serve reads for its copy of
    /// `stream`, whose finalized configuration revision (0 when none)
    /// `revision` reads only when the stream is fenced for this keeper.
    pub fn permits(&self, stream: StreamId, revision: impl FnOnce() -> u64) -> bool {
        if stream == catalog_stream::STREAM {
            return true;
        }
        let enforced = self.enforced();
        if !enforced {
            return true;
        }
        let below = self.fenced_below(stream);
        let revision = if below.is_some() { revision() } else { 0 };
        decisions::holds_authority(
            enforced,
            self.valid(),
            self.current.load(Ordering::Acquire),
            decisions::copy_fenced(below, revision),
        )
    }

    /// The epoch of the current lease, zero before the keeper enrolled.
    pub fn epoch(&self) -> u64 {
        self.epoch.load(Ordering::Acquire)
    }

    /// How long ago the last renewal was granted.
    pub fn age(&self) -> Option<Duration> {
        match self.renewed.load(Ordering::Acquire) {
            0 => None,
            renewed => Some(Duration::from_nanos(self.now().saturating_sub(renewed - 1))),
        }
    }

    /// How much longer the lease is valid.
    pub fn remaining(&self) -> Duration {
        let sent = self.sent.load(Ordering::Acquire);
        if sent == 0 {
            return Duration::ZERO;
        }
        let end = (sent - 1)
            .saturating_add(self.granted_duration.load(Ordering::Acquire))
            .saturating_sub(self.granted_margin.load(Ordering::Acquire));
        Duration::from_nanos(end.saturating_sub(self.now()))
    }

    pub fn fenced_streams(&self) -> usize {
        self.fenced.read().len()
    }

    /// The wait between renewals: a third of the holder's validity, so two
    /// renewals may fail before the lease lapses.
    fn interval(&self) -> Duration {
        self.duration.saturating_sub(self.margin) / 3
    }

    /// Ends the lease at once, as a lapse would.
    #[cfg(test)]
    pub fn expire(&self) {
        self.sent.store(0, Ordering::Release);
    }

    /// Records that this keeper holds enforced leases from now on.
    fn enforce(&self) -> io::Result<()> {
        if self.enforced() {
            return Ok(());
        }
        let file = std::fs::File::create(&self.marker)?;
        sync_file(&file)?;
        if let Some(directory) = self.marker.parent() {
            sync_directory(directory)?;
        }
        self.enforced.store(true, Ordering::Release);
        Ok(())
    }
}

/// Whether the lease lets this keeper campaign, lead or serve reads for its
/// copy of `stream`, whose state machine is `state`.
pub(super) fn permits(
    lease: &Lease,
    stream: StreamId,
    state: &crate::stream::consensus::storage::StateMachine,
) -> bool {
    lease.permits(stream, || {
        state
            .finalized()
            .map_or(0, |configuration| configuration.revision)
    })
}

fn nanos(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

impl Engine {
    /// Whether this keeper may campaign, lead or serve reads for the
    /// group's stream.
    pub(super) fn holds_authority(&self, group: &super::Group) -> bool {
        permits(&self.lease, group.genesis.stream, &group.state)
    }

    /// What the metrics scrape reports of the lease.
    pub(super) fn lease_scrape(&self) -> super::super::metrics::LeaseScrape {
        let lease = &self.lease;
        super::super::metrics::LeaseScrape {
            enforced: lease.enforced(),
            valid: lease.valid(),
            age_secs: lease.age().map(|age| age.as_secs_f64()),
            remaining_secs: lease.remaining().as_secs_f64(),
            epoch: lease.epoch(),
            fenced_streams: lease.fenced_streams(),
            renewal_failures: lease.failures.load(Ordering::Relaxed),
            renewal_refusals: lease.refusals.load(Ordering::Relaxed),
            lapses: lease.lapses.load(Ordering::Relaxed),
            gated: lease.gated.load(Ordering::Relaxed),
        }
    }

    /// Renews this keeper's lease until it stops.
    pub(super) async fn lease_loop(&self) {
        let mut valid = false;
        loop {
            #[cfg(test)]
            let renewed = if self.lease.suspended.load(Ordering::Acquire) {
                false
            } else {
                self.renew_lease().await
            };
            #[cfg(not(test))]
            let renewed = self.renew_lease().await;
            let interval = self.lease.interval();
            let wait = if renewed {
                interval
            } else {
                (interval / 10).clamp(RETRY_MIN, RETRY_MAX)
            };
            let now_valid = self.lease.valid();
            if valid != now_valid && self.lease.enforced() {
                self.apply_authority().await;
            }
            if valid && !now_valid {
                super::super::metrics::count(&self.lease.lapses);
                if self.lease.enforced() {
                    tracing::warn!(
                        keeper = %self.id,
                        "liveness lease lapsed: this keeper campaigns, leads and serves no stream \
                         until the catalog renews it"
                    );
                }
            }
            valid = now_valid;
            // Wake at the lapse too, so the lapse is counted when it happens.
            let lapse = self.lease.remaining();
            let wait = if valid && lapse < wait {
                lapse + Duration::from_millis(1)
            } else {
                wait
            };
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = tokio::time::sleep(wait) => (),
            }
        }
    }

    /// Applies the lease to every open group: a group this keeper holds no
    /// authority over starts no election, and its leader steps down. OpenRaft
    /// only stops a leader without a quorum from taking proposals; a hand-off
    /// that no one takes ends with the leader stepping down after an
    /// election timeout, and its campaign fails without authority.
    pub(super) async fn apply_authority(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for group in groups {
            if group.genesis.stream == catalog_stream::STREAM {
                continue;
            }
            if self.holds_authority(&group) {
                self.apply_mode(&group);
            } else {
                self.step_down(&group).await;
            }
        }
    }

    /// Makes this keeper step down from `group` and start no election. A
    /// leader hands leadership to another voter: OpenRaft steps it down once
    /// no one takes it within an election timeout and it campaigns, which
    /// needs elections on, so they turn off only once it no longer leads.
    pub(super) async fn step_down(&self, group: &Arc<super::Group>) {
        let metrics = group.raft.metrics().borrow_watched().clone();
        if metrics.state != openraft::ServerState::Leader {
            self.apply_mode(group);
            return;
        }
        // A leader's pre-vote leaves it leading, and fails without
        // authority anyway: its timed-out hand-off starts a real election,
        // which ends its leadership.
        group.raft.runtime_config().pre_vote(false);
        group.raft.runtime_config().elect(true);
        if let Some(target) = metrics
            .membership_config
            .membership()
            .voter_ids()
            .find(|id| *id != self.id.as_u128())
        {
            let _ = group.raft.trigger().transfer_leader(target).await;
        }
        let mut watched = group.raft.metrics();
        let _ = timeout(super::REQUEST_TIMEOUT, async {
            while watched.borrow_watched().state == openraft::ServerState::Leader {
                if watched.changed().await.is_err() {
                    return;
                }
            }
        })
        .await;
        group.raft.runtime_config().pre_vote(true);
        self.apply_mode(group);
    }

    /// Sends one renewal and applies the answer. Whether it was granted.
    async fn renew_lease(&self) -> bool {
        let lease = &self.lease;
        let epoch = if lease.current.load(Ordering::Acquire) {
            lease.epoch()
        } else {
            0
        };
        let sent = Instant::now();
        let request = Request::RenewLease {
            keeper: self.id,
            incarnation: self.recognition.own(),
            epoch,
        };
        let attempt = lease.interval().min(super::REQUEST_TIMEOUT);
        match timeout(attempt, self.catalog_request(request)).await {
            Ok(Ok(Reply::Lease(grant))) => self.adopt_lease(sent, epoch, grant).await,
            _ => {
                super::super::metrics::count(&lease.failures);
                false
            }
        }
    }

    async fn adopt_lease(&self, sent: Instant, asked: u64, grant: Grant) -> bool {
        let lease = &self.lease;
        if grant.enforced && !lease.enforced() {
            // One small file, once per keeper.
            let marked = lease.enforce();
            if let Err(error) = marked {
                tracing::warn!(keeper = %self.id, error = %error, "could not record lease enforcement");
                return false;
            }
            tracing::info!(keeper = %self.id, "liveness leases are enforced");
        }
        if grant.reused {
            self.recognition.mark_reused("the catalog").await;
        }
        let fenced = grant.fenced.into_iter().collect::<HashMap<_, _>>();
        let newly = fenced
            .iter()
            .filter(|(stream, floor)| lease.fenced_below(**stream) != Some(**floor))
            .map(|(stream, _)| *stream)
            .collect::<Vec<_>>();
        lease
            .any_fenced
            .store(!fenced.is_empty(), Ordering::Release);
        *lease.fenced.write() = fenced;
        // A copy the catalog fenced only retires: wake the repair loop.
        if !newly.is_empty() && grant.enforced {
            let groups = self.groups.lock().await.clone();
            for stream in newly {
                if let Some(group) = groups.get(&stream)
                    && decisions::copy_fenced(
                        lease.fenced_below(stream),
                        group
                            .state
                            .finalized()
                            .map_or(0, |configuration| configuration.revision),
                    )
                {
                    tracing::warn!(
                        keeper = %self.id,
                        stream = %crate::stream::consensus::logging::stream_uuid(stream),
                        "the catalog fenced this copy: a recovery left its configuration"
                    );
                    self.certification.fence(stream, group.state.generation());
                    self.step_down(group).await;
                    self.retire_now.notify_one();
                }
            }
        }
        if !grant.granted {
            super::super::metrics::count(&lease.refusals);
            if lease.current.swap(false, Ordering::AcqRel) || asked != 0 {
                lease.sent.store(0, Ordering::Release);
                // Every certification this process made was under the old
                // epoch: the copies certify again under the new one.
                self.certification.reset();
                tracing::warn!(
                    keeper = %self.id,
                    epoch = asked,
                    current = grant.epoch,
                    "the catalog bumped this keeper's epoch: its lease ended; rejoining"
                );
            } else {
                lease.sent.store(0, Ordering::Release);
                tracing::error!(
                    keeper = %self.id,
                    "the catalog refused this keeper's media incarnation: another one replaced it"
                );
            }
            return false;
        }
        let own = (nanos(lease.duration), nanos(lease.margin));
        let duration = own.0.min(grant.duration_ms.saturating_mul(1_000_000));
        let margin = own.1.max(grant.margin_ms.saturating_mul(1_000_000));
        lease.granted_duration.store(duration, Ordering::Release);
        lease.granted_margin.store(margin, Ordering::Release);
        lease.epoch.store(grant.epoch, Ordering::Release);
        lease.current.store(grant.epoch != 0, Ordering::Release);
        let sent = lease.at(sent).saturating_add(1);
        // Renewals run one at a time, so a later grant was sent later.
        lease.sent.fetch_max(sent, Ordering::AcqRel);
        lease
            .renewed
            .store(lease.now().saturating_add(1), Ordering::Release);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The worst case of rate drift: the holder's clock runs slow by `rho`,
    /// so its validity lasts longer in real time, and the clock the recovery
    /// waits on runs fast by `rho`, so its wait is shorter. Within the bound
    /// `rho <= margin / duration` the holder's lease ends no later than the
    /// wait, and the renewal was sent before the recovery committed.
    #[test]
    fn a_holder_within_the_drift_bound_expires_before_the_recovery_serves() {
        for duration in [1_000_u128, 2_000, 30_000, 120_000] {
            for margin in [1, duration / 100, duration / 10, duration / 3] {
                if !decisions::lease_bounds(duration as u64, margin as u64) {
                    continue;
                }
                // Real time, scaled by `duration` to stay in integers, with
                // rho = margin / duration.
                let holder = (duration - margin) * duration * duration / (duration - margin);
                let wait = (duration + margin) * duration * duration / (duration + margin);
                assert!(holder <= wait, "{duration} {margin}");
                // Past the bound the holder can outlive the wait.
                let rho = 2 * margin;
                if rho < duration {
                    let holder = (duration - margin) * duration * duration / (duration - rho);
                    let wait = (duration + margin) * duration * duration / (duration + rho);
                    assert!(holder > wait, "{duration} {margin}");
                }
            }
        }
    }

    fn granted(lease: &Lease) {
        lease.sent.store(
            lease.at(Instant::now()).saturating_add(1),
            Ordering::Release,
        );
        lease.current.store(true, Ordering::Release);
        lease.enforced.store(true, Ordering::Release);
    }

    #[tokio::test(start_paused = true)]
    async fn a_slow_clock_within_the_bound_still_lapses_before_the_wait() {
        let dir = tempfile::tempdir().unwrap();
        let (duration, margin) = (Duration::from_millis(1_000), Duration::from_millis(100));
        let wait = Duration::from_millis(
            decisions::recovery_wait(duration.as_millis() as u64, margin.as_millis() as u64)
                .unwrap(),
        );
        // A holder clock 10% slow, the bound for this lease.
        let lease = Lease::open(dir.path(), duration, margin).unwrap();
        lease.rate_permille.store(900, Ordering::Relaxed);
        granted(&lease);
        assert!(lease.valid() && lease.permits(StreamId(1), || 0));
        tokio::time::advance(Duration::from_millis(990)).await;
        assert!(lease.valid(), "the slow clock still counts the lease valid");
        // The recovery's wait, a little short as a fast clock measures it.
        tokio::time::advance(wait * 1000 / 1100 - Duration::from_millis(990)).await;
        assert!(!lease.valid());
        assert!(!lease.permits(StreamId(1), || 0));
        // The catalog stream is never gated.
        assert!(lease.permits(catalog_stream::STREAM, || 0));

        // A true clock lapses at the lease less the margin.
        let lease = Lease::open(dir.path(), duration, margin).unwrap();
        granted(&lease);
        tokio::time::advance(duration - margin - Duration::from_millis(1)).await;
        assert!(lease.valid());
        tokio::time::advance(Duration::from_millis(1)).await;
        assert!(!lease.valid());
    }

    #[tokio::test(start_paused = true)]
    async fn a_fence_gates_only_older_copies_and_advisory_leases_gate_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let lease =
            Lease::open(dir.path(), Duration::from_secs(30), Duration::from_secs(3)).unwrap();
        // Advisory: nothing is gated, even without a lease.
        assert!(lease.permits(StreamId(7), || 0));
        granted(&lease);
        lease.fenced.write().insert(StreamId(7), 5);
        lease.any_fenced.store(true, Ordering::Release);
        assert!(!lease.permits(StreamId(7), || 4));
        assert!(lease.permits(StreamId(7), || 5));
        assert!(lease.permits(StreamId(8), || 0));
        // A stale epoch gates everything.
        lease.current.store(false, Ordering::Release);
        assert!(!lease.permits(StreamId(8), || 0));
        // The enforcement marker survives a restart.
        lease.enforce().unwrap_or(());
        lease.enforced.store(false, Ordering::Release);
        lease.enforce().unwrap();
        assert!(
            Lease::open(dir.path(), Duration::from_secs(30), Duration::from_secs(3))
                .unwrap()
                .enforced()
        );
    }
}
