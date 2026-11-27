//! Operational HTTP/mTLS admin listener: Prometheus `/metrics`, health probes
//! (`/live`, `/ready`, `/safe-to-stop`), and the problem-streams report
//! (`/problems`, `/problem-streams`).

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    io,
    sync::{Arc, atomic::Ordering},
    time::Duration,
};

use journal_contract::StreamId;
use openraft::{Instant as _, ServerState, async_runtime::WatchReceiver};
use serde::Serialize;
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::Semaphore,
    task::JoinSet,
    time::{Instant, timeout},
};
use tokio_rustls::TlsAcceptor;
use uuid::Uuid;

use super::{Engine, MAX_LOG_SUFFIX, liveness};
use crate::stream::{
    consensus::{
        RaftTypes,
        logging::{rate_limit, stream_uuid},
        metrics::{FollowerLag, ScrapeSnapshot},
        state::MAX_RETAINED_RECORDS,
    },
    transport,
};

const MAX_ADMIN_CONNECTIONS: usize = 16;
/// The whole life of one admin connection: TLS handshake, request and response.
const ADMIN_TIMEOUT: Duration = Duration::from_secs(5);
/// Request line plus headers; admin requests carry no body.
const MAX_REQUEST_BYTES: usize = 8192;
const ACCEPT_BACKOFF: Duration = Duration::from_millis(100);
/// Flag a stream as near its unpurged WAL suffix ceiling at 75% of `MAX_LOG_SUFFIX`.
pub(super) const SUFFIX_NEAR_CEILING: usize = (MAX_LOG_SUFFIX as usize * 3) / 4;
/// Flag a stream as near its retained-record ceiling at 75% of `MAX_RETAINED_RECORDS`.
pub(super) const RECORD_NEAR_CEILING: u64 = (MAX_RETAINED_RECORDS as u64 * 3) / 4;
/// Follower lag in Raft log entries above which a stream is flagged under-replicated
/// even while heartbeats are still arriving.
const UNDER_REPLICATED_LAG_ENTRIES: u64 = 64;

/// Every reason `classify_stream_problems` reports. `/metrics` exports each
/// one, at zero when no stream has it, so alerts see a series to compare.
pub(super) const PROBLEM_REASONS: [&str; 9] = [
    "quarantined",
    "leaderless",
    "under_replicated",
    "parked_with_dead_voter",
    "joint_config",
    "near_suffix_ceiling",
    "near_record_ceiling",
    "near_quota_ceiling",
    "led_outside_preferred_domain",
];

#[derive(Debug, Serialize)]
pub(super) struct LiveReport {
    pub live: bool,
    pub wal_healthy: bool,
    pub stopping: bool,
    pub keeper: Uuid,
}

#[derive(Debug, Serialize)]
pub(super) struct UnmatchedStream {
    pub stream: Uuid,
    pub reason: &'static str,
}

#[derive(Debug, Serialize)]
pub(super) struct ReadyReport {
    pub ready: bool,
    pub keeper: Uuid,
    pub wal_healthy: bool,
    pub wal_replayed: bool,
    pub liveness_populated: bool,
    pub hosted_streams: usize,
    pub parked_streams: usize,
    pub quarantined_streams: Vec<Uuid>,
    pub unmatched_streams: Vec<UnmatchedStream>,
}

#[derive(Debug, Serialize)]
pub(super) struct StopBlocker {
    pub stream: Uuid,
    pub voter: Uuid,
    pub reason: &'static str,
}

#[derive(Debug, Serialize)]
pub(super) struct SafeToStopReport {
    pub safe: bool,
    pub keeper: Uuid,
    pub liveness_populated: bool,
    pub hosted_streams: usize,
    pub blocking: Vec<StopBlocker>,
}

#[derive(Debug, Serialize)]
pub(super) struct ProblemStream {
    pub stream: Uuid,
    pub state: &'static str,
    pub reasons: Vec<&'static str>,
    pub leader: Option<Uuid>,
    pub leader_domain: Option<String>,
    pub preferred_domain: Option<String>,
    pub voters: Vec<Uuid>,
    pub dead_voters: Vec<Uuid>,
    pub unreachable_voters: Vec<Uuid>,
    pub joint: bool,
    pub suffix_len: usize,
    pub suffix_ceiling: usize,
    pub retained_records: u64,
    pub record_ceiling: u64,
    pub retained_bytes: u64,
    pub quota_bytes: u64,
}

#[derive(Debug, Serialize)]
pub(super) struct ProblemReport {
    pub keeper: Uuid,
    pub total_hosted: usize,
    pub problem_count: usize,
    pub problems: Vec<ProblemStream>,
}

struct ClosedView {
    voters: BTreeSet<Uuid>,
    joint: bool,
    records: u64,
    bytes: u64,
}

struct StreamClassificationInput<'a> {
    is_open: bool,
    is_parked: bool,
    is_quarantined: bool,
    leader: Option<Uuid>,
    leader_domain: Option<&'a str>,
    preferred_domain: Option<&'a str>,
    joint: bool,
    has_dead_voter: bool,
    has_unreachable_voter: bool,
    leader_reports_lagging: bool,
    suffix_len: usize,
    retained_records: u64,
    retained_bytes: u64,
    quota_bytes: u64,
}

fn classify_stream_problems(input: &StreamClassificationInput<'_>) -> Vec<&'static str> {
    let mut reasons = Vec::new();
    if input.is_quarantined {
        reasons.push("quarantined");
    }
    if input.is_open && input.leader.is_none() {
        reasons.push("leaderless");
    }
    if input.has_unreachable_voter || input.leader_reports_lagging {
        reasons.push("under_replicated");
    }
    if input.is_parked && input.has_dead_voter {
        reasons.push("parked_with_dead_voter");
    }
    if input.joint {
        reasons.push("joint_config");
    }
    if input.suffix_len >= SUFFIX_NEAR_CEILING {
        reasons.push("near_suffix_ceiling");
    }
    if input.retained_records >= RECORD_NEAR_CEILING {
        reasons.push("near_record_ceiling");
    }
    if input.quota_bytes > 0
        && input.retained_bytes.saturating_mul(4) >= input.quota_bytes.saturating_mul(3)
    {
        reasons.push("near_quota_ceiling");
    }
    if input.is_open
        && let (Some(leader_domain), Some(preferred)) =
            (input.leader_domain, input.preferred_domain)
        && leader_domain != preferred
    {
        reasons.push("led_outside_preferred_domain");
    }
    reasons
}

impl Engine {
    /// Serves the operational admin HTTP/1.1 listener (plain HTTP or mTLS).
    pub(super) async fn listen_admin(
        self: Arc<Self>,
        listener: TcpListener,
        acceptor: Option<TlsAcceptor>,
    ) -> io::Result<()> {
        // The admin listener is auxiliary: neither a failed accept nor a
        // panicking request may stop the keeper, so it logs and goes on.
        let mut tasks = JoinSet::new();
        let connections = Arc::new(Semaphore::new(MAX_ADMIN_CONNECTIONS));
        loop {
            tokio::select! {
                _ = self.stop.cancelled() => return Ok(()),
                result = tasks.join_next(), if !tasks.is_empty() => {
                    if let Some(Err(error)) = result
                        && error.is_panic()
                    {
                        crate::stream::consensus::logging::critical!(
                            "keeper {} admin request panicked: {error}",
                            self.id
                        );
                    }
                }
                accepted = listener.accept() => {
                    let socket = match accepted {
                        Ok((socket, _)) => socket,
                        Err(error) => {
                            if let Some(dropped) = rate_limit("admin.accept", None) {
                                tracing::warn!(
                                    keeper = %self.id,
                                    error = %error,
                                    dropped = dropped,
                                    "admin accept failed"
                                );
                            }
                            tokio::time::sleep(ACCEPT_BACKOFF).await;
                            continue;
                        }
                    };
                    // Every slot busy: shed the connection at once instead
                    // of queueing it behind slow clients.
                    let Ok(permit) = connections.clone().try_acquire_owned() else {
                        drop(socket);
                        continue;
                    };
                    let engine = self.clone();
                    let acceptor = acceptor.clone();
                    tasks.spawn(async move {
                        let _permit = permit;
                        // One deadline covers the handshake, the request and
                        // the response, so a slow client holds a slot for at
                        // most `ADMIN_TIMEOUT`.
                        let _ = timeout(ADMIN_TIMEOUT, engine.admin_connection(socket, acceptor)).await;
                    });
                }
            }
        }
    }

    async fn admin_connection(
        self: &Arc<Self>,
        socket: TcpStream,
        acceptor: Option<TlsAcceptor>,
    ) -> io::Result<()> {
        let _ = socket.set_nodelay(true);
        match acceptor {
            Some(acceptor) => {
                let mut stream = acceptor.accept(socket).await?;
                let (_, tls) = stream.get_ref();
                let authorized = transport::leaf(tls.peer_certificates())
                    .and_then(transport::client_identity)
                    .is_ok_and(|id| self.administrators.contains(id.as_str()));
                self.serve_http(&mut stream, authorized).await
            }
            None => {
                let mut stream = socket;
                self.serve_http(&mut stream, true).await
            }
        }
    }

    async fn serve_http<S: AsyncRead + AsyncWrite + Unpin>(
        &self,
        stream: &mut S,
        authorized: bool,
    ) -> io::Result<()> {
        let Ok(request) = read_http_request(stream).await else {
            return Ok(());
        };
        let Some((method, target)) = parse_request_line(&request) else {
            let body = r#"{"error":"bad request"}"#;
            return write_http_response(
                stream,
                "400 Bad Request",
                "application/json",
                body.as_bytes(),
                false,
            )
            .await;
        };
        let head_only = match method {
            "GET" => false,
            "HEAD" => true,
            _ => {
                let body = r#"{"error":"method not allowed"}"#;
                return write_http_response(
                    stream,
                    "405 Method Not Allowed",
                    "application/json",
                    body.as_bytes(),
                    false,
                )
                .await;
            }
        };
        if !authorized {
            let body = r#"{"error":"unauthorized admin client"}"#;
            return write_http_response(
                stream,
                "403 Forbidden",
                "application/json",
                body.as_bytes(),
                head_only,
            )
            .await;
        }
        let path = target.split('?').next().unwrap_or(target);
        match path {
            "/metrics" => {
                let body = self.render_metrics().await;
                write_http_response(
                    stream,
                    "200 OK",
                    "text/plain; version=0.0.4; charset=utf-8",
                    body.as_bytes(),
                    head_only,
                )
                .await
            }
            "/live" => {
                let report = self.live_report();
                let status = if report.live {
                    "200 OK"
                } else {
                    "503 Service Unavailable"
                };
                let body = serde_json::to_vec(&report).unwrap_or_default();
                write_http_response(stream, status, "application/json", &body, head_only).await
            }
            "/ready" => {
                let report = self.ready_report().await;
                let status = if report.ready {
                    "200 OK"
                } else {
                    "503 Service Unavailable"
                };
                let body = serde_json::to_vec(&report).unwrap_or_default();
                write_http_response(stream, status, "application/json", &body, head_only).await
            }
            "/safe-to-stop" => {
                let report = self.safe_to_stop_report().await;
                let status = if report.safe {
                    "200 OK"
                } else {
                    "503 Service Unavailable"
                };
                let body = serde_json::to_vec(&report).unwrap_or_default();
                write_http_response(stream, status, "application/json", &body, head_only).await
            }
            "/problems" | "/problem-streams" => {
                let report = self.problem_streams_report().await;
                let body = serde_json::to_vec(&report).unwrap_or_default();
                write_http_response(stream, "200 OK", "application/json", &body, head_only).await
            }
            _ => {
                let body = r#"{"error":"not found"}"#;
                write_http_response(
                    stream,
                    "404 Not Found",
                    "application/json",
                    body.as_bytes(),
                    head_only,
                )
                .await
            }
        }
    }

    pub(super) fn live_report(&self) -> LiveReport {
        let wal_healthy = self.disk.healthy();
        let stopping = self.stop.is_cancelled();
        LiveReport {
            live: wal_healthy && !stopping,
            wal_healthy,
            stopping,
            keeper: self.id,
        }
    }

    pub(super) async fn ready_report(&self) -> ReadyReport {
        let wal_healthy = self.disk.healthy();
        let wal_replayed = self.replayed.load(Ordering::Acquire);
        let liveness_populated = self.liveness_populated();
        let groups = self.groups.lock().await.clone();
        let parked = self.parked.read().clone();
        let deleted = self.deleted.read().clone();
        let quarantined = self.quarantined.read().clone();
        let led_since = self.led_since.lock().clone();
        let silence_limit = self.heartbeat_silence_limit();
        let matched_window = Duration::from_millis(self.raft_config.election_timeout_max * 2);

        let mut hosted_streams = 0usize;
        let mut parked_streams = 0usize;
        let mut quarantined_streams = Vec::new();
        let mut unmatched_streams = Vec::new();

        for genesis in self.disk.streams() {
            let stream = genesis.stream;
            if deleted.contains(&stream) {
                continue;
            }
            if !self
                .disk
                .ownership(stream)
                .is_some_and(|owner| owner.generation().is_some())
            {
                continue;
            }
            if let Some(group) = groups.get(&stream)
                && group.state.is_deleted()
            {
                continue;
            }
            hosted_streams += 1;
            if quarantined.contains(&stream) {
                quarantined_streams.push(stream_uuid(stream));
                continue;
            }
            if parked.contains_key(&stream) {
                parked_streams += 1;
                continue;
            }
            let Some(group) = groups.get(&stream) else {
                continue;
            };
            if !group.state.healthy() {
                quarantined_streams.push(stream_uuid(stream));
                continue;
            }
            if group
                .snapshot_receive
                .try_lock()
                .map_or(true, |incoming| incoming.is_some())
            {
                unmatched_streams.push(UnmatchedStream {
                    stream: stream_uuid(stream),
                    reason: "receiving_snapshot",
                });
                continue;
            }
            let metrics = group.raft.metrics().borrow_watched().clone();
            let applied_caught_up = metrics.last_log_index.is_some()
                && metrics.last_applied.map(|id| id.index) == metrics.last_log_index;
            match metrics.state {
                ServerState::Leader => {
                    if self.lost_quorum(stream, &metrics, &led_since, silence_limit) {
                        unmatched_streams.push(UnmatchedStream {
                            stream: stream_uuid(stream),
                            reason: "leader_without_quorum",
                        });
                    } else if !applied_caught_up {
                        unmatched_streams.push(UnmatchedStream {
                            stream: stream_uuid(stream),
                            reason: "leader_applying",
                        });
                    }
                }
                ServerState::Follower => {
                    let leader_matched = group.leader_matched.lock().is_some_and(|(term, at)| {
                        term == metrics.current_term && at.elapsed() < matched_window
                    });
                    if metrics.current_leader.is_none()
                        || metrics.current_leader == Some(self.id.as_u128())
                    {
                        unmatched_streams.push(UnmatchedStream {
                            stream: stream_uuid(stream),
                            reason: "no_leader",
                        });
                    } else if !leader_matched {
                        unmatched_streams.push(UnmatchedStream {
                            stream: stream_uuid(stream),
                            reason: "not_matched_by_leader",
                        });
                    } else if !applied_caught_up {
                        unmatched_streams.push(UnmatchedStream {
                            stream: stream_uuid(stream),
                            reason: "follower_applying",
                        });
                    }
                }
                ServerState::Candidate => {
                    unmatched_streams.push(UnmatchedStream {
                        stream: stream_uuid(stream),
                        reason: "electing",
                    });
                }
                ServerState::Learner => {
                    unmatched_streams.push(UnmatchedStream {
                        stream: stream_uuid(stream),
                        reason: "learner_catching_up",
                    });
                }
                ServerState::Shutdown => {
                    unmatched_streams.push(UnmatchedStream {
                        stream: stream_uuid(stream),
                        reason: "group_shutdown",
                    });
                }
            }
        }

        let ready = wal_healthy
            && !self.stop.is_cancelled()
            && wal_replayed
            && liveness_populated
            && quarantined_streams.is_empty()
            && unmatched_streams.is_empty();

        ReadyReport {
            ready,
            keeper: self.id,
            wal_healthy,
            wal_replayed,
            liveness_populated,
            hosted_streams,
            parked_streams,
            quarantined_streams,
            unmatched_streams,
        }
    }

    pub(super) async fn safe_to_stop_report(&self) -> SafeToStopReport {
        let liveness_populated = self.liveness_populated();
        let groups = self.groups.lock().await.clone();
        let deleted = self.deleted.read().clone();
        let closed = self.closed_views();
        let led_since = self.led_since.lock().clone();
        let silence_limit = self.heartbeat_silence_limit();
        let now = Instant::now();

        let mut hosted_streams = 0usize;
        let mut blocking = Vec::new();

        for genesis in self.disk.streams() {
            let stream = genesis.stream;
            if deleted.contains(&stream) {
                continue;
            }
            if !self
                .disk
                .ownership(stream)
                .is_some_and(|owner| owner.generation().is_some())
            {
                continue;
            }
            if let Some(group) = groups.get(&stream)
                && group.state.is_deleted()
            {
                continue;
            }
            hosted_streams += 1;

            let (voters, open_metrics) = if let Some(group) = groups.get(&stream) {
                let metrics = group.raft.metrics().borrow_watched().clone();
                // A membership change in flight needs both voter sets; a
                // stop now can stall it until this keeper returns.
                if metrics
                    .membership_config
                    .membership()
                    .get_joint_config()
                    .len()
                    > 1
                {
                    blocking.push(StopBlocker {
                        stream: stream_uuid(stream),
                        voter: self.id,
                        reason: "joint_config",
                    });
                }
                let mut voters = metrics
                    .membership_config
                    .membership()
                    .voter_ids()
                    .map(Uuid::from_u128)
                    .collect::<BTreeSet<_>>();
                if voters.is_empty() {
                    voters.extend(genesis.voters);
                }
                (voters, Some(metrics))
            } else if let Some(view) = closed.get(&stream) {
                let mut voters = view.voters.clone();
                if voters.is_empty() {
                    voters.extend(genesis.voters);
                }
                (voters, None)
            } else {
                (genesis.voters.into_iter().collect::<BTreeSet<_>>(), None)
            };

            for voter in voters {
                if voter == self.id {
                    continue;
                }
                if !self.is_peer_reachable(voter) {
                    blocking.push(StopBlocker {
                        stream: stream_uuid(stream),
                        voter,
                        reason: "voter_unreachable",
                    });
                    continue;
                }
                if let Some(metrics) = &open_metrics
                    && metrics.state == ServerState::Leader
                    && let Some(heartbeat) = &metrics.heartbeat
                {
                    let led_long_enough = led_since.get(&stream).is_some_and(|(term, since)| {
                        *term == metrics.current_term
                            && now.saturating_duration_since(*since) >= silence_limit
                    });
                    let silent = match heartbeat.get(&voter.as_u128()).copied().flatten() {
                        Some(acked) => acked.elapsed() >= silence_limit,
                        None => led_long_enough,
                    };
                    if silent {
                        blocking.push(StopBlocker {
                            stream: stream_uuid(stream),
                            voter,
                            reason: "voter_silent",
                        });
                    }
                }
            }
        }

        SafeToStopReport {
            safe: liveness_populated && blocking.is_empty(),
            keeper: self.id,
            liveness_populated,
            hosted_streams,
            blocking,
        }
    }

    pub(super) async fn problem_streams_report(&self) -> ProblemReport {
        let (report, _) = self.collect_streams_and_metrics().await;
        report
    }

    pub(super) async fn render_metrics(&self) -> String {
        let (_, scrape) = self.collect_streams_and_metrics().await;
        self.disk.metrics.render_prometheus(&scrape)
    }

    async fn collect_streams_and_metrics(&self) -> (ProblemReport, ScrapeSnapshot) {
        let groups = self.groups.lock().await.clone();
        let parked = self.parked.read().clone();
        let deleted = self.deleted.read().clone();
        let quarantined = self.quarantined.read().clone();
        let closed = self.closed_views();
        let preferred = self.preferred.lock().clone();
        let led_since = self.led_since.lock().clone();
        let repairs_in_flight = self.repairs_in_flight();
        let (repair_pending, repair_oldest, repair_backoff) = self.repair_queue();
        let (disk_available, disk_reserved) = match self.disk.space.headroom() {
            Ok((available, reserved)) => (Some(available), reserved),
            Err(_) => (None, 0),
        };
        let silence_limit = self.heartbeat_silence_limit();
        let now = Instant::now();
        let domains = self.placement.domains();

        let mut total_hosted = 0usize;
        let mut streams_open = 0usize;
        let mut streams_led = 0usize;
        let mut streams_parked = 0usize;
        let mut streams_quarantined = 0usize;
        let mut retained_records_total = 0u64;
        let mut retained_records_max = 0u64;
        let mut retained_bytes_total = 0u64;
        let mut retained_bytes_max = 0u64;
        let mut suffix_entries_max = 0u64;
        let mut follower_lags: BTreeMap<Uuid, (u64, u64, u64)> = BTreeMap::new();
        let mut problems = Vec::new();
        let mut slow_proposals = 0u64;
        let mut oldest_proposal = Duration::ZERO;
        let mut problem_counts: BTreeMap<&'static str, u64> =
            PROBLEM_REASONS.iter().map(|reason| (*reason, 0)).collect();

        for genesis in self.disk.streams() {
            let stream = genesis.stream;
            if deleted.contains(&stream) {
                continue;
            }
            if !self
                .disk
                .ownership(stream)
                .is_some_and(|owner| owner.generation().is_some())
            {
                continue;
            }
            if let Some(group) = groups.get(&stream)
                && group.state.is_deleted()
            {
                continue;
            }
            total_hosted += 1;

            let is_parked = parked.contains_key(&stream);
            let is_quarantined = quarantined.contains(&stream)
                || groups
                    .get(&stream)
                    .is_some_and(|group| !group.state.healthy());
            let suffix_len = self.disk.suffix_len(stream);
            suffix_entries_max = suffix_entries_max.max(suffix_len as u64);

            let (
                is_open,
                state_label,
                leader,
                voters,
                joint,
                leader_reports_lagging,
                retained_records,
                retained_bytes,
            ) = if let Some(group) = groups.get(&stream) {
                streams_open += 1;
                let (slow, oldest) = group.proposals.slow();
                slow_proposals += slow;
                oldest_proposal = oldest_proposal.max(oldest);
                let metrics = group.raft.metrics().borrow_watched().clone();
                let is_leader = metrics.state == ServerState::Leader;
                if is_leader {
                    streams_led += 1;
                }
                let membership = metrics.membership_config.membership();
                let joint = membership.get_joint_config().len() > 1;
                let mut voters = membership
                    .voter_ids()
                    .map(Uuid::from_u128)
                    .collect::<BTreeSet<_>>();
                if voters.is_empty() {
                    voters.extend(genesis.voters);
                }
                let mut lagging = false;
                let mut leader_lost_quorum = false;
                if is_leader {
                    let last = metrics.last_log_index.unwrap_or(0);
                    if let Some(replication) = &metrics.replication {
                        for (&node_id, matched) in replication {
                            let follower = Uuid::from_u128(node_id);
                            if follower == self.id {
                                continue;
                            }
                            let lag = match matched {
                                Some(log_id) => last.saturating_sub(log_id.index),
                                None => {
                                    lagging = true;
                                    last
                                }
                            };
                            let entry = follower_lags.entry(follower).or_insert((0, 0, 0));
                            entry.0 = entry.0.max(lag);
                            entry.1 = entry.1.saturating_add(lag);
                            if lag > 0 {
                                entry.2 += 1;
                            }
                            if lag >= UNDER_REPLICATED_LAG_ENTRIES {
                                lagging = true;
                            }
                        }
                    }
                    if let Some(heartbeat) = &metrics.heartbeat {
                        let led_long_enough =
                            led_since.get(&stream).is_some_and(|(term, since)| {
                                *term == metrics.current_term
                                    && now.saturating_duration_since(*since) >= silence_limit
                            });
                        let mut active_voters = usize::from(voters.contains(&self.id));
                        for voter in &voters {
                            if *voter == self.id {
                                continue;
                            }
                            let silent = match heartbeat.get(&voter.as_u128()).copied().flatten() {
                                Some(acked) => acked.elapsed() >= silence_limit,
                                None => led_long_enough || !self.is_peer_reachable(*voter),
                            };
                            if silent {
                                lagging = true;
                            } else {
                                active_voters += 1;
                            }
                        }
                        if active_voters * 2 <= voters.len() {
                            leader_lost_quorum = true;
                        }
                    }
                    if self.lost_quorum(stream, &metrics, &led_since, silence_limit) {
                        leader_lost_quorum = true;
                    }
                }
                let (records, bytes) = group.state.retained_stats();
                let state_label = if is_quarantined {
                    "quarantined"
                } else {
                    "open"
                };
                let effective_leader = match (metrics.state, metrics.current_leader) {
                    (ServerState::Leader, Some(id)) if !leader_lost_quorum => {
                        Some(Uuid::from_u128(id))
                    }
                    (ServerState::Follower, Some(id)) => {
                        let leader = Uuid::from_u128(id);
                        if leader == self.id
                            || (!self.is_peer_reachable(leader)
                                && group.heard.lock().elapsed() >= silence_limit)
                        {
                            None
                        } else {
                            Some(leader)
                        }
                    }
                    _ => None,
                };
                (
                    true,
                    state_label,
                    effective_leader,
                    voters.into_iter().collect::<Vec<_>>(),
                    joint,
                    lagging,
                    records,
                    bytes,
                )
            } else if is_parked {
                streams_parked += 1;
                let (voters, joint, records, bytes) = if let Some(view) = closed.get(&stream) {
                    let mut voters = view.voters.clone();
                    if voters.is_empty() {
                        voters.extend(genesis.voters);
                    }
                    (
                        voters.into_iter().collect(),
                        view.joint,
                        view.records,
                        view.bytes,
                    )
                } else {
                    (genesis.voters.to_vec(), false, 0, 0)
                };
                (
                    false,
                    if is_quarantined {
                        "quarantined"
                    } else {
                        "parked"
                    },
                    None,
                    voters,
                    joint,
                    false,
                    records,
                    bytes,
                )
            } else {
                let state_label = if is_quarantined {
                    "quarantined"
                } else {
                    "unopened"
                };
                (
                    false,
                    state_label,
                    None,
                    genesis.voters.to_vec(),
                    false,
                    false,
                    0,
                    0,
                )
            };

            if is_quarantined {
                streams_quarantined += 1;
            }
            retained_records_total = retained_records_total.saturating_add(retained_records);
            retained_records_max = retained_records_max.max(retained_records);
            retained_bytes_total = retained_bytes_total.saturating_add(retained_bytes);
            retained_bytes_max = retained_bytes_max.max(retained_bytes);

            let dead_voters = voters
                .iter()
                .copied()
                .filter(|voter| self.dead(*voter))
                .collect::<Vec<_>>();
            let unreachable_voters = voters
                .iter()
                .copied()
                .filter(|voter| *voter != self.id && !self.is_peer_reachable(*voter))
                .collect::<Vec<_>>();
            let leader_domain = leader.and_then(|id| domains.get(&id).cloned());
            let preferred_domain = preferred.get(&stream).cloned();

            let reasons = classify_stream_problems(&StreamClassificationInput {
                is_open,
                is_parked,
                is_quarantined,
                leader,
                leader_domain: leader_domain.as_deref(),
                preferred_domain: preferred_domain.as_deref(),
                joint,
                has_dead_voter: !dead_voters.is_empty(),
                has_unreachable_voter: !unreachable_voters.is_empty(),
                leader_reports_lagging,
                suffix_len,
                retained_records,
                retained_bytes,
                quota_bytes: genesis.quota_bytes,
            });
            if !reasons.is_empty() {
                for reason in &reasons {
                    *problem_counts.entry(*reason).or_insert(0) += 1;
                }
                problems.push(ProblemStream {
                    stream: stream_uuid(stream),
                    state: state_label,
                    reasons,
                    leader,
                    leader_domain,
                    preferred_domain,
                    voters,
                    dead_voters,
                    unreachable_voters,
                    joint,
                    suffix_len,
                    suffix_ceiling: MAX_LOG_SUFFIX as usize,
                    retained_records,
                    record_ceiling: MAX_RETAINED_RECORDS as u64,
                    retained_bytes,
                    quota_bytes: genesis.quota_bytes,
                });
            }
        }

        let wal_healthy = self.disk.healthy();
        let accepting = wal_healthy && self.disk.space.accepts_streams();
        let liveness = self.liveness_snapshot(accepting);
        let replication_lag = follower_lags
            .into_iter()
            .map(
                |(follower, (max_lag, total_lag, lagging_streams))| FollowerLag {
                    follower,
                    max_lag,
                    total_lag,
                    lagging_streams,
                },
            )
            .collect();

        let problem_count = problems.len();
        let report = ProblemReport {
            keeper: self.id,
            total_hosted,
            problem_count,
            problems,
        };
        let scrape = ScrapeSnapshot {
            keeper: self.id,
            domain: domains.get(&self.id).cloned().unwrap_or_default(),
            wal_healthy,
            accepting,
            streams_hosted: total_hosted,
            streams_open,
            streams_led,
            streams_parked,
            streams_quarantined,
            streams_deleted: deleted.len(),
            repairs_in_flight,
            replication_lag,
            liveness,
            retained_records_total,
            retained_records_max,
            retained_bytes_total,
            retained_bytes_max,
            suffix_entries_max,
            problem_streams: problem_counts,
            slow_proposals,
            oldest_proposal_secs: oldest_proposal.as_secs_f64(),
            disk_available,
            disk_reserved,
            repair_pending,
            repair_oldest_secs: repair_oldest.as_secs_f64(),
            repair_backoff,
        };
        (report, scrape)
    }

    /// What the admin pages need of each closed (parked or closing) replica.
    /// A closing one still holds its state machine; a pinned one keeps only
    /// its finalized configuration, so its retention reads as zero.
    fn closed_views(&self) -> std::collections::HashMap<journal_contract::StreamId, ClosedView> {
        self.closed_states
            .lock()
            .iter()
            .map(|(stream, closed)| {
                let view = match closed {
                    super::Closed::Closing(state) => {
                        let membership = state.membership();
                        let mut voters = membership
                            .membership()
                            .voter_ids()
                            .map(Uuid::from_u128)
                            .collect::<BTreeSet<_>>();
                        if voters.is_empty()
                            && let Some(configuration) = state.finalized()
                        {
                            voters.extend(configuration.voters);
                        }
                        let (records, bytes) = state.retained_stats();
                        ClosedView {
                            voters,
                            joint: membership.membership().get_joint_config().len() > 1,
                            records,
                            bytes,
                        }
                    }
                    super::Closed::Pinned(pin) => ClosedView {
                        voters: pin
                            .finalized
                            .map(|configuration| configuration.voters.into_iter().collect())
                            .unwrap_or_default(),
                        joint: false,
                        records: 0,
                        bytes: 0,
                    },
                };
                (*stream, view)
            })
            .collect()
    }

    /// Whether this keeper leads `stream` without a quorum: no quorum
    /// acknowledged it within `silence_limit`. OpenRaft 0.10.1 keeps an
    /// isolated leader in `ServerState::Leader` until
    /// `quorum_loss_probe_interval`, while its lease has long expired, so the
    /// server state alone does not show it.
    fn lost_quorum(
        &self,
        stream: StreamId,
        metrics: &openraft::RaftMetrics<RaftTypes>,
        led_since: &HashMap<StreamId, (u64, Instant)>,
        silence_limit: Duration,
    ) -> bool {
        if metrics.state != ServerState::Leader {
            return false;
        }
        match &metrics.last_quorum_acked {
            Some(acked) => acked.elapsed() >= silence_limit,
            None => led_since.get(&stream).is_some_and(|(term, since)| {
                *term == metrics.current_term && since.elapsed() >= silence_limit
            }),
        }
    }

    fn heartbeat_silence_limit(&self) -> Duration {
        (liveness::PING_INTERVAL * 3).max(Duration::from_millis(
            self.raft_config.election_timeout_max * 2,
        ))
    }
}

async fn read_http_request<S: AsyncRead + Unpin>(stream: &mut S) -> io::Result<String> {
    let mut buf = Vec::with_capacity(512);
    let mut chunk = [0u8; 512];
    loop {
        let room = MAX_REQUEST_BYTES - buf.len();
        if room == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "admin HTTP request headers exceed limit",
            ));
        }
        let n = stream.read(&mut chunk[..room.min(512)]).await?;
        if n == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "admin HTTP request ended before its headers",
            ));
        }
        // Only the new bytes and the three before them can complete the
        // blank line that ends the headers.
        let from = buf.len().saturating_sub(3);
        buf.extend_from_slice(&chunk[..n]);
        let tail = &buf[from..];
        if tail.windows(4).any(|w| w == b"\r\n\r\n") || tail.windows(2).any(|w| w == b"\n\n") {
            break;
        }
    }
    String::from_utf8(buf).map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid utf-8"))
}

fn parse_request_line(request: &str) -> Option<(&str, &str)> {
    let line = request.lines().next()?;
    let mut parts = line.split_whitespace();
    let method = parts.next()?;
    let target = parts.next()?;
    let version = parts.next()?;
    if !version.starts_with("HTTP/1.") || !target.starts_with('/') || parts.next().is_some() {
        return None;
    }
    Some((method, target))
}

async fn write_http_response<S: AsyncWrite + Unpin>(
    stream: &mut S,
    status: &str,
    content_type: &str,
    body: &[u8],
    head_only: bool,
) -> io::Result<()> {
    let header = format!(
        "HTTP/1.1 {status}\r\n\
         Content-Type: {content_type}\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes()).await?;
    if !head_only {
        stream.write_all(body).await?;
    }
    stream.flush().await?;
    stream.shutdown().await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_stream_problems_detects_all_categories() {
        let leader = Uuid::from_u128(1);
        let healthy = classify_stream_problems(&StreamClassificationInput {
            is_open: true,
            is_parked: false,
            is_quarantined: false,
            leader: Some(leader),
            leader_domain: Some("zone-a"),
            preferred_domain: Some("zone-a"),
            joint: false,
            has_dead_voter: false,
            has_unreachable_voter: false,
            leader_reports_lagging: false,
            suffix_len: 10,
            retained_records: 100,
            retained_bytes: 1024,
            quota_bytes: 1024 * 1024,
        });
        assert!(healthy.is_empty());

        let problems = classify_stream_problems(&StreamClassificationInput {
            is_open: true,
            is_parked: false,
            is_quarantined: true,
            leader: None,
            leader_domain: None,
            preferred_domain: Some("zone-b"),
            joint: true,
            has_dead_voter: true,
            has_unreachable_voter: true,
            leader_reports_lagging: true,
            suffix_len: SUFFIX_NEAR_CEILING,
            retained_records: RECORD_NEAR_CEILING,
            retained_bytes: 800,
            quota_bytes: 1000,
        });
        assert!(problems.contains(&"quarantined"));
        assert!(problems.contains(&"leaderless"));
        assert!(problems.contains(&"under_replicated"));
        assert!(problems.contains(&"joint_config"));
        assert!(problems.contains(&"near_suffix_ceiling"));
        assert!(problems.contains(&"near_record_ceiling"));
        assert!(problems.contains(&"near_quota_ceiling"));

        let preferred_mismatch = classify_stream_problems(&StreamClassificationInput {
            is_open: true,
            is_parked: false,
            is_quarantined: false,
            leader: Some(leader),
            leader_domain: Some("zone-a"),
            preferred_domain: Some("zone-b"),
            joint: false,
            has_dead_voter: false,
            has_unreachable_voter: false,
            leader_reports_lagging: false,
            suffix_len: 0,
            retained_records: 0,
            retained_bytes: 0,
            quota_bytes: 1024,
        });
        assert_eq!(preferred_mismatch, vec!["led_outside_preferred_domain"]);

        let parked_dead = classify_stream_problems(&StreamClassificationInput {
            is_open: false,
            is_parked: true,
            is_quarantined: false,
            leader: None,
            leader_domain: None,
            preferred_domain: None,
            joint: false,
            has_dead_voter: true,
            has_unreachable_voter: true,
            leader_reports_lagging: false,
            suffix_len: 0,
            retained_records: 0,
            retained_bytes: 0,
            quota_bytes: 1024,
        });
        assert!(parked_dead.contains(&"parked_with_dead_voter"));
        assert!(!parked_dead.contains(&"leaderless"));
        for reason in problems
            .iter()
            .chain(&preferred_mismatch)
            .chain(&parked_dead)
        {
            assert!(PROBLEM_REASONS.contains(reason), "{reason} is not exported");
        }
    }

    #[tokio::test]
    async fn request_reader_bounds_headers_and_needs_their_end() {
        let (mut client, mut server) = tokio::io::duplex(64 * 1024);
        client
            .write_all(b"GET /metrics HTTP/1.1\r\nHost: x\r\n\r\n")
            .await
            .unwrap();
        let request = read_http_request(&mut server).await.unwrap();
        assert_eq!(parse_request_line(&request), Some(("GET", "/metrics")));

        // Headers that never end are cut at the limit.
        let (mut client, mut server) = tokio::io::duplex(64 * 1024);
        client
            .write_all(&vec![b'a'; MAX_REQUEST_BYTES + 1])
            .await
            .unwrap();
        assert!(read_http_request(&mut server).await.is_err());

        // A request cut before its blank line is not served.
        let (mut client, mut server) = tokio::io::duplex(64 * 1024);
        client
            .write_all(b"GET /metrics HTTP/1.1\r\n")
            .await
            .unwrap();
        drop(client);
        assert!(read_http_request(&mut server).await.is_err());

        // The blank line may arrive split across reads.
        let (mut client, mut server) = tokio::io::duplex(64 * 1024);
        let reader = tokio::spawn(async move { read_http_request(&mut server).await });
        client.write_all(b"GET /live HTTP/1.1\r\n\r").await.unwrap();
        tokio::task::yield_now().await;
        client.write_all(b"\n").await.unwrap();
        assert!(reader.await.unwrap().is_ok());

        for bad in [
            "GET metrics HTTP/1.1",
            "GET /metrics HTTP/2",
            "GET /metrics HTTP/1.1 extra",
            "GET",
        ] {
            assert_eq!(parse_request_line(bad), None, "{bad}");
        }
    }
}
