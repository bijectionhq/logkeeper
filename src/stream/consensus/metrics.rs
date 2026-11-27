//! Per-keeper counters, lock-free histograms, and Prometheus exposition format
//! for the consensus keeper.

use std::{
    collections::BTreeMap,
    fmt::Write as _,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Duration,
};

use tokio_util::sync::CancellationToken;
use uuid::Uuid;

/// Upper bounds for WAL round size (in records).
const WAL_ROUND_RECORDS_BUCKETS: &[u64] = &[1, 2, 4, 8, 16, 32, 64, 128];

/// Upper bounds for WAL round size (in bytes).
const WAL_ROUND_BYTES_BUCKETS: &[u64] = &[
    256, 1_024, 4_096, 16_384, 65_536, 262_144, 1_048_576, 4_194_304, 16_777_216, 33_554_432,
];

/// Upper bounds in nanoseconds for latency histograms (0.1 ms .. 20 s).
const LATENCY_BUCKETS_NS: &[u64] = &[
    100_000,        // 0.0001 s
    250_000,        // 0.00025 s
    500_000,        // 0.0005 s
    1_000_000,      // 0.001 s
    2_500_000,      // 0.0025 s
    5_000_000,      // 0.005 s
    10_000_000,     // 0.01 s
    25_000_000,     // 0.025 s
    50_000_000,     // 0.05 s
    100_000_000,    // 0.1 s
    250_000_000,    // 0.25 s
    500_000_000,    // 0.5 s
    1_000_000_000,  // 1 s
    2_500_000_000,  // 2.5 s
    5_000_000_000,  // 5 s
    10_000_000_000, // 10 s
    20_000_000_000, // 20 s, the WAL round watchdog limit
];

/// Lock-free fixed-bucket histogram over unsigned integer counts/sizes.
pub(super) struct CountHistogram {
    bounds: &'static [u64],
    buckets: Box<[AtomicU64]>,
    sum: AtomicU64,
    count: AtomicU64,
}

impl CountHistogram {
    fn new(bounds: &'static [u64]) -> Self {
        let buckets = (0..=bounds.len())
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Self {
            bounds,
            buckets,
            sum: AtomicU64::new(0),
            count: AtomicU64::new(0),
        }
    }

    pub(super) fn observe(&self, value: u64) {
        let idx = self.bounds.partition_point(|bound| *bound < value);
        self.buckets[idx].fetch_add(1, Ordering::Relaxed);
        self.sum.fetch_add(value, Ordering::Relaxed);
        self.count.fetch_add(1, Ordering::Relaxed);
    }

    fn write_prometheus(&self, out: &mut String, name: &str, labels: Option<&str>) {
        let mut cumulative = 0u64;
        for (bound, bucket) in self.bounds.iter().zip(self.buckets.iter()) {
            cumulative += bucket.load(Ordering::Relaxed);
            match labels {
                Some(labels) => {
                    let _ = writeln!(out, "{name}_bucket{{{labels},le=\"{bound}\"}} {cumulative}");
                }
                None => {
                    let _ = writeln!(out, "{name}_bucket{{le=\"{bound}\"}} {cumulative}");
                }
            }
        }
        cumulative += self.buckets[self.bounds.len()].load(Ordering::Relaxed);
        let sum = self.sum.load(Ordering::Relaxed);
        let count = self.count.load(Ordering::Relaxed).max(cumulative);
        match labels {
            Some(labels) => {
                let _ = writeln!(out, "{name}_bucket{{{labels},le=\"+Inf\"}} {count}");
                let _ = writeln!(out, "{name}_sum{{{labels}}} {sum}");
                let _ = writeln!(out, "{name}_count{{{labels}}} {count}");
            }
            None => {
                let _ = writeln!(out, "{name}_bucket{{le=\"+Inf\"}} {count}");
                let _ = writeln!(out, "{name}_sum {sum}");
                let _ = writeln!(out, "{name}_count {count}");
            }
        }
    }
}

/// Lock-free fixed-bucket histogram over durations, exported in seconds.
pub(super) struct DurationHistogram {
    bounds_ns: &'static [u64],
    buckets: Box<[AtomicU64]>,
    sum_ns: AtomicU64,
    count: AtomicU64,
}

impl DurationHistogram {
    fn new(bounds_ns: &'static [u64]) -> Self {
        let buckets = (0..=bounds_ns.len())
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Self {
            bounds_ns,
            buckets,
            sum_ns: AtomicU64::new(0),
            count: AtomicU64::new(0),
        }
    }

    pub(super) fn observe(&self, duration: Duration) {
        self.observe_n(duration, 1);
    }

    /// Records `times` observations of the same `duration`.
    pub(super) fn observe_n(&self, duration: Duration, times: u64) {
        if times == 0 {
            return;
        }
        let nanos = duration.as_nanos().min(u64::MAX as u128) as u64;
        let idx = self.bounds_ns.partition_point(|bound| *bound < nanos);
        self.buckets[idx].fetch_add(times, Ordering::Relaxed);
        self.sum_ns
            .fetch_add(nanos.saturating_mul(times), Ordering::Relaxed);
        self.count.fetch_add(times, Ordering::Relaxed);
    }

    fn write_prometheus(&self, out: &mut String, name: &str, labels: Option<&str>) {
        let mut cumulative = 0u64;
        for (bound_ns, bucket) in self.bounds_ns.iter().zip(self.buckets.iter()) {
            cumulative += bucket.load(Ordering::Relaxed);
            let secs = *bound_ns as f64 / 1e9;
            match labels {
                Some(labels) => {
                    let _ = writeln!(out, "{name}_bucket{{{labels},le=\"{secs}\"}} {cumulative}");
                }
                None => {
                    let _ = writeln!(out, "{name}_bucket{{le=\"{secs}\"}} {cumulative}");
                }
            }
        }
        cumulative += self.buckets[self.bounds_ns.len()].load(Ordering::Relaxed);
        let sum_secs = self.sum_ns.load(Ordering::Relaxed) as f64 / 1e9;
        let count = self.count.load(Ordering::Relaxed).max(cumulative);
        match labels {
            Some(labels) => {
                let _ = writeln!(out, "{name}_bucket{{{labels},le=\"+Inf\"}} {count}");
                let _ = writeln!(out, "{name}_sum{{{labels}}} {sum_secs:.9}");
                let _ = writeln!(out, "{name}_count{{{labels}}} {count}");
            }
            None => {
                let _ = writeln!(out, "{name}_bucket{{le=\"+Inf\"}} {count}");
                let _ = writeln!(out, "{name}_sum {sum_secs:.9}");
                let _ = writeln!(out, "{name}_count {count}");
            }
        }
    }
}

/// Per-keeper consensus metrics: refusal counters, operational counters, and
/// lock-free histograms.
pub(super) struct Metrics {
    // Refusal counters (existing G1 set)
    pub write_unhealthy: AtomicU64,
    pub write_pending: AtomicU64,
    pub write_full_suffix: AtomicU64,
    pub write_space: AtomicU64,
    pub write_proposal: AtomicU64,
    pub write_timeout: AtomicU64,
    pub head_queue: AtomicU64,
    pub head_timeout: AtomicU64,
    pub peer_busy: AtomicU64,
    pub peer_unreachable: AtomicU64,
    // Park / wake counters (existing G1 set)
    pub parked: AtomicU64,
    pub unparked_by_peer: AtomicU64,
    pub unparked_by_client: AtomicU64,
    pub unparked_for_repair: AtomicU64,
    pub park_declined: AtomicU64,
    pub reopened_stopped: AtomicU64,
    pub evicted: AtomicU64,
    pub compacted_bytes: AtomicU64,
    // Election counters
    pub elections_started: AtomicU64,
    pub elections_won: AtomicU64,
    pub votes_granted: AtomicU64,
    pub votes_denied: AtomicU64,
    pub pre_votes_granted: AtomicU64,
    pub pre_votes_denied: AtomicU64,
    // Snapshot counters
    pub snapshots_sent_ok: AtomicU64,
    pub snapshots_sent_failed: AtomicU64,
    pub snapshot_bytes_sent: AtomicU64,
    pub snapshots_received_ok: AtomicU64,
    pub snapshots_received_failed: AtomicU64,
    pub snapshot_bytes_received: AtomicU64,
    pub snapshots_built: AtomicU64,
    // Repair counters
    pub repairs_joint_ok: AtomicU64,
    pub repairs_joint_failed: AtomicU64,
    pub repairs_learners_ok: AtomicU64,
    pub repairs_learners_failed: AtomicU64,
    pub repairs_voter_ok: AtomicU64,
    pub repairs_voter_failed: AtomicU64,
    // Histograms
    pub wal_round_records: CountHistogram,
    pub wal_round_bytes: CountHistogram,
    pub wal_round_duration: DurationHistogram,
    pub wal_fsync_segment_duration: DurationHistogram,
    pub wal_fsync_boundary_duration: DurationHistogram,
    pub commit_duration: DurationHistogram,
    /// Leader application appends waiting for a WAL round.
    pub commit_stage_queue: DurationHistogram,
    /// The WAL round that made a leader application append durable.
    pub commit_stage_wal: DurationHistogram,
    /// From the leader's durable append to the start of its apply, which
    /// covers follower replication, the quorum commit and the apply queue.
    pub commit_stage_replication: DurationHistogram,
    /// One state machine apply batch.
    pub commit_stage_apply: DurationHistogram,
    /// Proposals that took at least `SLOW_PROPOSAL` to commit or fail.
    pub slow_proposals: AtomicU64,
}

/// Critical invariant violations this process logged (see `critical!`).
/// Process-wide, since a violation site need not know its keeper.
pub(crate) static CRITICAL: AtomicU64 = AtomicU64::new(0);

impl Default for Metrics {
    fn default() -> Self {
        Self::new()
    }
}

impl Metrics {
    pub(super) fn new() -> Self {
        Self {
            write_unhealthy: AtomicU64::new(0),
            write_pending: AtomicU64::new(0),
            write_full_suffix: AtomicU64::new(0),
            write_space: AtomicU64::new(0),
            write_proposal: AtomicU64::new(0),
            write_timeout: AtomicU64::new(0),
            head_queue: AtomicU64::new(0),
            head_timeout: AtomicU64::new(0),
            peer_busy: AtomicU64::new(0),
            peer_unreachable: AtomicU64::new(0),
            parked: AtomicU64::new(0),
            unparked_by_peer: AtomicU64::new(0),
            unparked_by_client: AtomicU64::new(0),
            unparked_for_repair: AtomicU64::new(0),
            park_declined: AtomicU64::new(0),
            reopened_stopped: AtomicU64::new(0),
            evicted: AtomicU64::new(0),
            compacted_bytes: AtomicU64::new(0),
            elections_started: AtomicU64::new(0),
            elections_won: AtomicU64::new(0),
            votes_granted: AtomicU64::new(0),
            votes_denied: AtomicU64::new(0),
            pre_votes_granted: AtomicU64::new(0),
            pre_votes_denied: AtomicU64::new(0),
            snapshots_sent_ok: AtomicU64::new(0),
            snapshots_sent_failed: AtomicU64::new(0),
            snapshot_bytes_sent: AtomicU64::new(0),
            snapshots_received_ok: AtomicU64::new(0),
            snapshots_received_failed: AtomicU64::new(0),
            snapshot_bytes_received: AtomicU64::new(0),
            snapshots_built: AtomicU64::new(0),
            repairs_joint_ok: AtomicU64::new(0),
            repairs_joint_failed: AtomicU64::new(0),
            repairs_learners_ok: AtomicU64::new(0),
            repairs_learners_failed: AtomicU64::new(0),
            repairs_voter_ok: AtomicU64::new(0),
            repairs_voter_failed: AtomicU64::new(0),
            wal_round_records: CountHistogram::new(WAL_ROUND_RECORDS_BUCKETS),
            wal_round_bytes: CountHistogram::new(WAL_ROUND_BYTES_BUCKETS),
            wal_round_duration: DurationHistogram::new(LATENCY_BUCKETS_NS),
            wal_fsync_segment_duration: DurationHistogram::new(LATENCY_BUCKETS_NS),
            wal_fsync_boundary_duration: DurationHistogram::new(LATENCY_BUCKETS_NS),
            commit_duration: DurationHistogram::new(LATENCY_BUCKETS_NS),
            commit_stage_queue: DurationHistogram::new(LATENCY_BUCKETS_NS),
            commit_stage_wal: DurationHistogram::new(LATENCY_BUCKETS_NS),
            commit_stage_replication: DurationHistogram::new(LATENCY_BUCKETS_NS),
            commit_stage_apply: DurationHistogram::new(LATENCY_BUCKETS_NS),
            slow_proposals: AtomicU64::new(0),
        }
    }

    fn summary_snapshot(&self) -> Vec<(&'static str, u64)> {
        vec![
            (
                "write.unhealthy",
                self.write_unhealthy.load(Ordering::Relaxed),
            ),
            (
                "write.pending_limit",
                self.write_pending.load(Ordering::Relaxed),
            ),
            (
                "write.full_suffix",
                self.write_full_suffix.load(Ordering::Relaxed),
            ),
            ("write.space", self.write_space.load(Ordering::Relaxed)),
            (
                "write.proposal_failed",
                self.write_proposal.load(Ordering::Relaxed),
            ),
            ("write.timeout", self.write_timeout.load(Ordering::Relaxed)),
            ("head.queue_full", self.head_queue.load(Ordering::Relaxed)),
            ("head.timeout", self.head_timeout.load(Ordering::Relaxed)),
            ("peer.busy", self.peer_busy.load(Ordering::Relaxed)),
            (
                "peer.unreachable",
                self.peer_unreachable.load(Ordering::Relaxed),
            ),
            ("stream.parked", self.parked.load(Ordering::Relaxed)),
            (
                "stream.unparked_by_peer",
                self.unparked_by_peer.load(Ordering::Relaxed),
            ),
            (
                "stream.unparked_by_client",
                self.unparked_by_client.load(Ordering::Relaxed),
            ),
            (
                "stream.unparked_for_repair",
                self.unparked_for_repair.load(Ordering::Relaxed),
            ),
            (
                "stream.park_declined",
                self.park_declined.load(Ordering::Relaxed),
            ),
            (
                "stream.reopened_stopped",
                self.reopened_stopped.load(Ordering::Relaxed),
            ),
            ("stream.evicted", self.evicted.load(Ordering::Relaxed)),
            (
                "segments.compacted_bytes",
                self.compacted_bytes.load(Ordering::Relaxed),
            ),
        ]
    }

    /// Renders all counters, histograms, and live scrape gauges in Prometheus
    /// text exposition format (version 0.0.4).
    pub(super) fn render_prometheus(&self, scrape: &ScrapeSnapshot) -> String {
        let mut out = String::with_capacity(8192);

        // Build / version info
        let _ = writeln!(
            out,
            "# HELP logkeeper_build_info Build and keeper identity metadata."
        );
        let _ = writeln!(out, "# TYPE logkeeper_build_info gauge");
        let _ = writeln!(
            out,
            "logkeeper_build_info{{version=\"{}\",keeper=\"{}\",domain=\"{}\",control_alpn=\"{}\",replication_alpn=\"{}\",bulk_alpn=\"{}\"}} 1",
            escape_label(env!("CARGO_PKG_VERSION")),
            scrape.keeper,
            escape_label(&scrape.domain),
            escape_label(std::str::from_utf8(super::CONTROL_ALPN).unwrap_or("")),
            escape_label(std::str::from_utf8(super::REPLICATION_ALPN).unwrap_or("")),
            escape_label(std::str::from_utf8(super::BULK_ALPN).unwrap_or("")),
        );

        // Keeper status gauges
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_healthy Whether the local WAL thread is healthy (1) or stopped (0)."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_wal_healthy gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_wal_healthy {}",
            u8::from(scrape.wal_healthy)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_accepting Whether the keeper accepts new streams (1) or not (0)."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_accepting gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_accepting {}",
            u8::from(scrape.accepting)
        );

        // Refusals
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_refusals_total Consensus requests refused as unavailable, by reason."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_refusals_total counter");
        for (reason, counter) in [
            ("write.unhealthy", &self.write_unhealthy),
            ("write.pending_limit", &self.write_pending),
            ("write.full_suffix", &self.write_full_suffix),
            ("write.space", &self.write_space),
            ("write.proposal_failed", &self.write_proposal),
            ("write.timeout", &self.write_timeout),
            ("head.queue_full", &self.head_queue),
            ("head.timeout", &self.head_timeout),
            ("peer.busy", &self.peer_busy),
            ("peer.unreachable", &self.peer_unreachable),
        ] {
            let _ = writeln!(
                out,
                "logkeeper_consensus_refusals_total{{reason=\"{reason}\"}} {}",
                counter.load(Ordering::Relaxed)
            );
        }

        // Parks / wakes
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_stream_parks_total Idle streams parked by this keeper."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_stream_parks_total counter");
        let _ = writeln!(
            out,
            "logkeeper_consensus_stream_parks_total {}",
            self.parked.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_stream_park_declined_total Idle stream park attempts declined by a follower."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_stream_park_declined_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_stream_park_declined_total {}",
            self.park_declined.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_stream_wakes_total Parked streams reopened, by trigger."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_stream_wakes_total counter");
        for (trigger, counter) in [
            ("peer", &self.unparked_by_peer),
            ("client", &self.unparked_by_client),
            ("repair", &self.unparked_for_repair),
        ] {
            let _ = writeln!(
                out,
                "logkeeper_consensus_stream_wakes_total{{trigger=\"{trigger}\"}} {}",
                counter.load(Ordering::Relaxed)
            );
        }

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_stream_reopened_stopped_total Replicas reopened after their Raft core stopped on a storage error."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_stream_reopened_stopped_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_stream_reopened_stopped_total {}",
            self.reopened_stopped.load(Ordering::Relaxed)
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_stream_evictions_total Idle replicas closed to stay under the open-stream limit."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_stream_evictions_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_stream_evictions_total {}",
            self.evicted.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_compacted_bytes_total Live bytes copied out of cold WAL segments by compaction."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_compacted_bytes_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_wal_compacted_bytes_total {}",
            self.compacted_bytes.load(Ordering::Relaxed)
        );

        // Elections & votes
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_elections_total Elections started and won by this keeper."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_elections_total counter");
        let _ = writeln!(
            out,
            "logkeeper_consensus_elections_total{{outcome=\"started\"}} {}",
            self.elections_started.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_elections_total{{outcome=\"won\"}} {}",
            self.elections_won.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_votes_total Vote and pre-vote requests answered by this keeper."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_votes_total counter");
        for (kind, outcome, counter) in [
            ("vote", "granted", &self.votes_granted),
            ("vote", "denied", &self.votes_denied),
            ("pre_vote", "granted", &self.pre_votes_granted),
            ("pre_vote", "denied", &self.pre_votes_denied),
        ] {
            let _ = writeln!(
                out,
                "logkeeper_consensus_votes_total{{kind=\"{kind}\",outcome=\"{outcome}\"}} {}",
                counter.load(Ordering::Relaxed)
            );
        }

        // Snapshots
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_snapshots_sent_total Snapshots sent to followers by outcome."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_snapshots_sent_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshots_sent_total{{outcome=\"ok\"}} {}",
            self.snapshots_sent_ok.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshots_sent_total{{outcome=\"error\"}} {}",
            self.snapshots_sent_failed.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_snapshot_bytes_sent_total Snapshot payload bytes sent to followers."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_snapshot_bytes_sent_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshot_bytes_sent_total {}",
            self.snapshot_bytes_sent.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_snapshots_received_total Snapshots received from leaders by outcome."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_snapshots_received_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshots_received_total{{outcome=\"ok\"}} {}",
            self.snapshots_received_ok.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshots_received_total{{outcome=\"error\"}} {}",
            self.snapshots_received_failed.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_snapshot_bytes_received_total Snapshot payload bytes received from leaders."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_snapshot_bytes_received_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshot_bytes_received_total {}",
            self.snapshot_bytes_received.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_snapshots_built_total Local snapshots built."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_snapshots_built_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_snapshots_built_total {}",
            self.snapshots_built.load(Ordering::Relaxed)
        );

        // Repairs
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_repairs_total Automatic repair attempts by kind and outcome."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_repairs_total counter");
        for (kind, outcome, counter) in [
            ("joint", "ok", &self.repairs_joint_ok),
            ("joint", "failed", &self.repairs_joint_failed),
            ("learners", "ok", &self.repairs_learners_ok),
            ("learners", "failed", &self.repairs_learners_failed),
            ("voter", "ok", &self.repairs_voter_ok),
            ("voter", "failed", &self.repairs_voter_failed),
        ] {
            let _ = writeln!(
                out,
                "logkeeper_consensus_repairs_total{{kind=\"{kind}\",outcome=\"{outcome}\"}} {}",
                counter.load(Ordering::Relaxed)
            );
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_repairs_in_flight Repairs currently executing."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_repairs_in_flight gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_repairs_in_flight {}",
            scrape.repairs_in_flight
        );

        // Histograms
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_round_records Number of records committed per WAL round."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_round_records histogram"
        );
        self.wal_round_records.write_prometheus(
            &mut out,
            "logkeeper_consensus_wal_round_records",
            None,
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_round_bytes Serialized bytes committed per WAL round."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_wal_round_bytes histogram");
        self.wal_round_bytes.write_prometheus(
            &mut out,
            "logkeeper_consensus_wal_round_bytes",
            None,
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_round_duration_seconds End-to-end duration of a WAL round."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_round_duration_seconds histogram"
        );
        self.wal_round_duration.write_prometheus(
            &mut out,
            "logkeeper_consensus_wal_round_duration_seconds",
            None,
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_fsync_duration_seconds Duration of WAL fdatasync calls by target."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_fsync_duration_seconds histogram"
        );
        self.wal_fsync_segment_duration.write_prometheus(
            &mut out,
            "logkeeper_consensus_wal_fsync_duration_seconds",
            Some("target=\"segment\""),
        );
        self.wal_fsync_boundary_duration.write_prometheus(
            &mut out,
            "logkeeper_consensus_wal_fsync_duration_seconds",
            Some("target=\"boundary\""),
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_commit_duration_seconds Leader write commit latency from admission to Raft decision."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_commit_duration_seconds histogram"
        );
        self.commit_duration.write_prometheus(
            &mut out,
            "logkeeper_consensus_commit_duration_seconds",
            None,
        );

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_commit_stage_seconds Leader commit latency by stage: WAL queue wait, WAL round, replication to apply, and apply."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_commit_stage_seconds histogram"
        );
        for (stage, histogram) in [
            ("queue", &self.commit_stage_queue),
            ("wal", &self.commit_stage_wal),
            ("replication", &self.commit_stage_replication),
            ("apply", &self.commit_stage_apply),
        ] {
            histogram.write_prometheus(
                &mut out,
                "logkeeper_consensus_commit_stage_seconds",
                Some(&format!("stage=\"{stage}\"")),
            );
        }

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_slow_proposals_total Proposals that took at least one second to commit or fail."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_slow_proposals_total counter"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_slow_proposals_total {}",
            self.slow_proposals.load(Ordering::Relaxed)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_slow_proposals Proposals in flight for at least one second."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_slow_proposals gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_slow_proposals {}",
            scrape.slow_proposals
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_oldest_proposal_seconds Age of the oldest proposal in flight, or zero."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_oldest_proposal_seconds gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_oldest_proposal_seconds {:.3}",
            scrape.oldest_proposal_secs
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_critical_total Critical invariant violations logged by this keeper."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_critical_total counter");
        let _ = writeln!(
            out,
            "logkeeper_consensus_critical_total {}",
            CRITICAL.load(Ordering::Relaxed)
        );

        // Disk headroom and the WAL health gate
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_disk_available_bytes Free bytes on the keeper data volume."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_disk_available_bytes gauge");
        if let Some(available) = scrape.disk_available {
            let _ = writeln!(out, "logkeeper_consensus_disk_available_bytes {available}");
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_disk_reserved_bytes Bytes reserved for writes in flight and not yet allocated."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_disk_reserved_bytes gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_disk_reserved_bytes {}",
            scrape.disk_reserved
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_disk_ordinary_floor_bytes Free bytes below which the keeper refuses ordinary writes."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_disk_ordinary_floor_bytes gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_disk_ordinary_floor_bytes {}",
            super::decisions::ORDINARY_FLOOR
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_media_responsive Whether the WAL is healthy and no recent round ran past the slow-round limit (1) or not (0)."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_media_responsive gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_media_responsive {}",
            u8::from(scrape.media_responsive)
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_slow_round_seconds WAL round duration past which the keeper marks its media slow and hands off leadership."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_slow_round_seconds gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_wal_slow_round_seconds {}",
            super::storage::SLOW_ROUND.as_secs_f64()
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_round_limit_seconds WAL round duration at which the watchdog ends the keeper."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_round_limit_seconds gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_wal_round_limit_seconds {}",
            super::storage::MAX_ROUND_DURATION.as_secs_f64()
        );

        // Repair queue
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_repair_pending_streams Led streams that need a repair."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_repair_pending_streams gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_repair_pending_streams {}",
            scrape.repair_pending
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_repair_oldest_pending_seconds How long the oldest pending repair has waited, or zero."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_repair_oldest_pending_seconds gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_repair_oldest_pending_seconds {:.3}",
            scrape.repair_oldest_secs
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_repair_backoff_streams Streams whose last repair failed and that wait out a backoff."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_repair_backoff_streams gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_repair_backoff_streams {}",
            scrape.repair_backoff
        );

        // Hosted stream counts & aggregated retention
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_streams Hosted stream counts by state."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_streams gauge");
        for (state, count) in [
            ("hosted", scrape.streams_hosted),
            ("open", scrape.streams_open),
            ("led", scrape.streams_led),
            ("parked", scrape.streams_parked),
            ("quarantined", scrape.streams_quarantined),
            ("deleted", scrape.streams_deleted),
        ] {
            let _ = writeln!(
                out,
                "logkeeper_consensus_streams{{state=\"{state}\"}} {count}"
            );
        }

        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_retained_records_total Total retained records summed across all hosted streams."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_retained_records_total gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_retained_records_total {}",
            scrape.retained_records_total
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_retained_records_max Maximum retained records on any single hosted stream."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_retained_records_max gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_retained_records_max {}",
            scrape.retained_records_max
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_retained_bytes_total Total retained bytes summed across all hosted streams."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_retained_bytes_total gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_retained_bytes_total {}",
            scrape.retained_bytes_total
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_retained_bytes_max Maximum retained bytes on any single hosted stream."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_retained_bytes_max gauge");
        let _ = writeln!(
            out,
            "logkeeper_consensus_retained_bytes_max {}",
            scrape.retained_bytes_max
        );
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_wal_suffix_entries_max Maximum unpurged WAL suffix entries on any single hosted stream."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_wal_suffix_entries_max gauge"
        );
        let _ = writeln!(
            out,
            "logkeeper_consensus_wal_suffix_entries_max {}",
            scrape.suffix_entries_max
        );

        // Replication lag per follower
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_replication_lag_entries_max Maximum Raft log entry lag for a follower across led streams."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_replication_lag_entries_max gauge"
        );
        for lag in &scrape.replication_lag {
            let _ = writeln!(
                out,
                "logkeeper_consensus_replication_lag_entries_max{{follower=\"{}\"}} {}",
                lag.follower, lag.max_lag
            );
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_replication_lag_entries_total Total Raft log entry lag summed for a follower across led streams."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_replication_lag_entries_total gauge"
        );
        for lag in &scrape.replication_lag {
            let _ = writeln!(
                out,
                "logkeeper_consensus_replication_lag_entries_total{{follower=\"{}\"}} {}",
                lag.follower, lag.total_lag
            );
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_replication_lag_streams Number of led streams where a follower lags behind the leader."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_replication_lag_streams gauge"
        );
        for lag in &scrape.replication_lag {
            let _ = writeln!(
                out,
                "logkeeper_consensus_replication_lag_streams{{follower=\"{}\"}} {}",
                lag.follower, lag.lagging_streams
            );
        }

        // Liveness state per keeper
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_keeper_liveness Liveness state per keeper in the cluster (1 for current state)."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_keeper_liveness gauge");
        for peer in &scrape.liveness {
            let domain = escape_label(&peer.domain);
            for state in [
                LivenessState::Alive,
                LivenessState::Suspect,
                LivenessState::Dead,
            ] {
                let active = u8::from(peer.state == state);
                let _ = writeln!(
                    out,
                    "logkeeper_consensus_keeper_liveness{{keeper=\"{}\",domain=\"{domain}\",state=\"{}\"}} {active}",
                    peer.keeper,
                    state.as_str()
                );
            }
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_keeper_accepting Whether each keeper reports accepting new streams (1) or not (0)."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_keeper_accepting gauge");
        for peer in &scrape.liveness {
            let domain = escape_label(&peer.domain);
            let _ = writeln!(
                out,
                "logkeeper_consensus_keeper_accepting{{keeper=\"{}\",domain=\"{domain}\"}} {}",
                peer.keeper,
                u8::from(peer.accepting)
            );
        }
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_keeper_silent_seconds Seconds since each keeper last answered a liveness ping."
        );
        let _ = writeln!(
            out,
            "# TYPE logkeeper_consensus_keeper_silent_seconds gauge"
        );
        for peer in &scrape.liveness {
            let domain = escape_label(&peer.domain);
            let _ = writeln!(
                out,
                "logkeeper_consensus_keeper_silent_seconds{{keeper=\"{}\",domain=\"{domain}\"}} {:.3}",
                peer.keeper, peer.silent_secs
            );
        }

        // Problem stream summary gauges
        let _ = writeln!(
            out,
            "# HELP logkeeper_consensus_problem_streams Hosted streams currently exhibiting a problem, by reason."
        );
        let _ = writeln!(out, "# TYPE logkeeper_consensus_problem_streams gauge");
        for (reason, count) in &scrape.problem_streams {
            let _ = writeln!(
                out,
                "logkeeper_consensus_problem_streams{{reason=\"{reason}\"}} {count}"
            );
        }

        out
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LivenessState {
    Alive,
    Suspect,
    Dead,
}

impl LivenessState {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Alive => "alive",
            Self::Suspect => "suspect",
            Self::Dead => "dead",
        }
    }
}

pub(super) struct FollowerLag {
    pub follower: Uuid,
    pub max_lag: u64,
    pub total_lag: u64,
    pub lagging_streams: u64,
}

pub(super) struct KeeperLiveness {
    pub keeper: Uuid,
    pub domain: String,
    pub state: LivenessState,
    pub accepting: bool,
    pub silent_secs: f64,
}

/// Live cluster/keeper gauges collected on demand during a `/metrics` scrape.
pub(super) struct ScrapeSnapshot {
    pub keeper: Uuid,
    pub domain: String,
    pub wal_healthy: bool,
    pub media_responsive: bool,
    pub accepting: bool,
    pub streams_hosted: usize,
    pub streams_open: usize,
    pub streams_led: usize,
    pub streams_parked: usize,
    pub streams_quarantined: usize,
    pub streams_deleted: usize,
    pub repairs_in_flight: usize,
    pub replication_lag: Vec<FollowerLag>,
    pub liveness: Vec<KeeperLiveness>,
    pub retained_records_total: u64,
    pub retained_records_max: u64,
    pub retained_bytes_total: u64,
    pub retained_bytes_max: u64,
    pub suffix_entries_max: u64,
    pub problem_streams: BTreeMap<&'static str, u64>,
    pub slow_proposals: u64,
    pub oldest_proposal_secs: f64,
    /// Free bytes on the keeper volume, when it could be measured.
    pub disk_available: Option<u64>,
    /// Bytes reserved for writes in flight but not yet allocated.
    pub disk_reserved: u64,
    /// Streams this keeper leads that need repair, and how long the oldest
    /// of them has waited.
    pub repair_pending: usize,
    pub repair_oldest_secs: f64,
    /// Streams whose last repair failed and wait out a backoff.
    pub repair_backoff: usize,
}

fn escape_label(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            _ => out.push(ch),
        }
    }
    out
}

static SAMPLES: AtomicU64 = AtomicU64::new(0);

/// Logs the detail of refusals, rate-limited per reason with a dropped count.
pub(super) fn sample(reason: &'static str, detail: impl FnOnce() -> String) {
    if SAMPLES.fetch_add(1, Ordering::Relaxed) < 8 {
        tracing::warn!(reason = reason, detail = %detail(), dropped = 0u64, "consensus refusal");
    } else if let Some(dropped) = super::logging::rate_limit(reason, None) {
        tracing::warn!(reason = reason, detail = %detail(), dropped = dropped, "consensus refusal");
    }
}

pub(super) fn count(counter: &AtomicU64) {
    counter.fetch_add(1, Ordering::Relaxed);
}

pub(super) fn add(counter: &AtomicU64, amount: u64) {
    counter.fetch_add(amount, Ordering::Relaxed);
}

/// The counters that changed since `previous`, as `name=total(+delta)` pairs.
fn changed(previous: &[(&'static str, u64)], current: &[(&'static str, u64)]) -> Vec<String> {
    current
        .iter()
        .zip(previous)
        .filter(|((_, now), (_, before))| now != before)
        .map(|((name, now), (_, before))| format!("{name}={now}(+{})", now - before))
        .collect()
}

/// Logs the counters that changed every `interval` until `stop`.
pub(super) async fn report(
    keeper: Uuid,
    metrics: Arc<Metrics>,
    interval: Duration,
    stop: CancellationToken,
    gauges: impl Fn() -> String,
) {
    let mut previous = metrics.summary_snapshot();
    let mut summary = gauges();
    loop {
        tokio::select! {
            () = stop.cancelled() => return,
            () = tokio::time::sleep(interval) => {}
        }
        let current = metrics.summary_snapshot();
        let changes = changed(&previous, &current);
        if !changes.is_empty() {
            tracing::info!(
                keeper = %keeper,
                refusals = %changes.join(" "),
                "consensus refusal counters"
            );
        }
        previous = current;
        let current = gauges();
        if current != summary {
            tracing::info!(keeper = %keeper, segments = %current, "consensus WAL segments");
            summary = current;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    fn sample_scrape() -> ScrapeSnapshot {
        let k1 = Uuid::from_u128(1);
        let k2 = Uuid::from_u128(2);
        let mut problems = BTreeMap::new();
        problems.insert("leaderless", 1);
        ScrapeSnapshot {
            keeper: k1,
            domain: "zone-a".into(),
            wal_healthy: true,
            media_responsive: true,
            accepting: true,
            streams_hosted: 5,
            streams_open: 4,
            streams_led: 2,
            streams_parked: 1,
            streams_quarantined: 0,
            streams_deleted: 0,
            repairs_in_flight: 1,
            replication_lag: vec![FollowerLag {
                follower: k2,
                max_lag: 7,
                total_lag: 10,
                lagging_streams: 2,
            }],
            liveness: vec![
                KeeperLiveness {
                    keeper: k1,
                    domain: "zone-a".into(),
                    state: LivenessState::Alive,
                    accepting: true,
                    silent_secs: 0.0,
                },
                KeeperLiveness {
                    keeper: k2,
                    domain: "zone-b".into(),
                    state: LivenessState::Dead,
                    accepting: false,
                    silent_secs: 605.0,
                },
            ],
            retained_records_total: 1000,
            retained_records_max: 400,
            retained_bytes_total: 1_000_000,
            retained_bytes_max: 500_000,
            suffix_entries_max: 42,
            problem_streams: problems,
            slow_proposals: 0,
            oldest_proposal_secs: 0.0,
            disk_available: Some(1 << 30),
            disk_reserved: 0,
            repair_pending: 1,
            repair_oldest_secs: 12.0,
            repair_backoff: 0,
        }
    }

    /// Every `logkeeper_*` series name in `source`.
    fn metric_names(source: &str) -> BTreeSet<&str> {
        let mut names = BTreeSet::new();
        let mut rest = source;
        while let Some(at) = rest.find("logkeeper_") {
            let tail = &rest[at..];
            let end = tail
                .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
                .unwrap_or(tail.len());
            names.insert(&tail[..end]);
            rest = &tail[end..];
        }
        names
    }

    #[test]
    fn alert_rules_and_dashboard_name_only_rendered_metrics() {
        let text = Metrics::new().render_prometheus(&sample_scrape());
        let rendered = text
            .lines()
            .filter(|line| !line.starts_with('#'))
            .filter_map(|line| line.split(['{', ' ']).next())
            .collect::<BTreeSet<_>>();
        let rules = include_str!("../../../deploy/prometheus/logkeeper-alerts.yml");
        let dashboard = include_str!("../../../deploy/grafana/logkeeper.json");
        for (file, source) in [("alert rules", rules), ("dashboard", dashboard)] {
            let names = metric_names(source);
            assert!(names.len() > 10, "{file} names too few metrics");
            for name in names {
                // A histogram's family name stands for its series.
                assert!(
                    rendered.contains(name) || rendered.contains(format!("{name}_bucket").as_str()),
                    "{file} name {name}, which /metrics does not render"
                );
            }
        }
        // Each rule carries what the README's runbook and the pager need.
        let alerts = rules.matches("- alert: ").count();
        assert!(alerts >= 15);
        for field in [
            "expr: ",
            "for: ",
            "severity: ",
            "summary: ",
            "description: ",
        ] {
            assert_eq!(
                rules.matches(field).count(),
                alerts,
                "every alert has {field}"
            );
        }
        serde_json::from_str::<serde_json::Value>(dashboard).unwrap();
    }

    #[test]
    fn only_changed_counters_are_reported() {
        let before = vec![("a", 1), ("b", 2)];
        let after = vec![("a", 1), ("b", 5)];
        assert_eq!(changed(&before, &after), vec!["b=5(+3)".to_owned()]);
    }

    #[test]
    fn histograms_and_prometheus_rendering_cover_all_families() {
        let metrics = Metrics::new();
        count(&metrics.write_pending);
        count(&metrics.parked);
        count(&metrics.unparked_by_client);
        count(&metrics.elections_started);
        count(&metrics.elections_won);
        count(&metrics.snapshots_sent_ok);
        add(&metrics.snapshot_bytes_sent, 4096);
        count(&metrics.snapshots_received_ok);
        add(&metrics.snapshot_bytes_received, 2048);
        count(&metrics.repairs_voter_ok);
        metrics.wal_round_records.observe(1);
        metrics.wal_round_records.observe(12);
        metrics.wal_round_bytes.observe(512);
        metrics.wal_round_duration.observe(Duration::from_millis(3));
        metrics
            .wal_fsync_segment_duration
            .observe(Duration::from_micros(600));
        metrics
            .wal_fsync_boundary_duration
            .observe(Duration::from_micros(400));
        metrics.commit_duration.observe(Duration::from_millis(8));

        let k2 = Uuid::from_u128(2);
        let scrape = sample_scrape();

        let text = metrics.render_prometheus(&scrape);
        assert!(text.contains("logkeeper_build_info{version=\""));
        assert!(
            text.contains("logkeeper_consensus_refusals_total{reason=\"write.pending_limit\"} 1")
        );
        assert!(text.contains("logkeeper_consensus_wal_round_records_bucket{le=\"1\"} 1"));
        assert!(text.contains("logkeeper_consensus_wal_round_records_bucket{le=\"16\"} 2"));
        assert!(text.contains("logkeeper_consensus_wal_round_records_sum 13"));
        assert!(text.contains("logkeeper_consensus_wal_round_records_count 2"));
        assert!(text.contains("logkeeper_consensus_wal_round_bytes_sum 512"));
        assert!(text.contains("logkeeper_consensus_wal_round_duration_seconds_count 1"));
        assert!(text.contains(
            "logkeeper_consensus_wal_fsync_duration_seconds_count{target=\"segment\"} 1"
        ));
        assert!(text.contains(
            "logkeeper_consensus_wal_fsync_duration_seconds_count{target=\"boundary\"} 1"
        ));
        assert!(text.contains("logkeeper_consensus_commit_duration_seconds_count 1"));
        assert!(text.contains(&format!(
            "logkeeper_consensus_replication_lag_entries_max{{follower=\"{k2}\"}} 7"
        )));
        assert!(text.contains("logkeeper_consensus_elections_total{outcome=\"started\"} 1"));
        assert!(text.contains("logkeeper_consensus_elections_total{outcome=\"won\"} 1"));
        assert!(text.contains("logkeeper_consensus_snapshots_sent_total{outcome=\"ok\"} 1"));
        assert!(text.contains("logkeeper_consensus_snapshot_bytes_sent_total 4096"));
        assert!(text.contains("logkeeper_consensus_snapshots_received_total{outcome=\"ok\"} 1"));
        assert!(
            text.contains("logkeeper_consensus_repairs_total{kind=\"voter\",outcome=\"ok\"} 1")
        );
        assert!(text.contains("logkeeper_consensus_stream_parks_total 1"));
        assert!(text.contains("logkeeper_consensus_stream_wakes_total{trigger=\"client\"} 1"));
        assert!(text.contains(&format!(
            "logkeeper_consensus_keeper_liveness{{keeper=\"{k2}\",domain=\"zone-b\",state=\"dead\"}} 1"
        )));
        assert!(text.contains("logkeeper_consensus_retained_records_total 1000"));
        assert!(text.contains("logkeeper_consensus_retained_bytes_total 1000000"));
        assert!(text.contains("logkeeper_consensus_problem_streams{reason=\"leaderless\"} 1"));
    }
}
