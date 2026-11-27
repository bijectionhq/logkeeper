//! Operational tests: Prometheus `/metrics`, plain HTTP and mTLS admin
//! listeners, `/live`, `/ready`, `/safe-to-stop`, and `/problems`.

use super::*;
use crate::stream::consensus::AdminConfig;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

pub(super) fn free_loopback() -> SocketAddr {
    std::net::TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
}

pub(super) async fn http_get(addr: SocketAddr, path: &str) -> (u16, String, String) {
    http_request(addr, "GET", path).await
}

pub(super) async fn http_request(
    addr: SocketAddr,
    method: &str,
    path: &str,
) -> (u16, String, String) {
    let mut stream = tokio::net::TcpStream::connect(addr).await.unwrap();
    let req = format!("{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).await.unwrap();
    stream.flush().await.unwrap();
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw).await.unwrap();
    parse_http_response(&raw)
}

pub(super) async fn https_get(
    addr: SocketAddr,
    creds: &Credentials,
    path: &str,
) -> (u16, String, String) {
    let (connector, _) = creds.client_protocol(b"http/1.1").unwrap();
    let tcp = tokio::net::TcpStream::connect(addr).await.unwrap();
    let server_name = tokio_rustls::rustls::pki_types::ServerName::try_from("localhost").unwrap();
    let mut tls = connector.connect(server_name, tcp).await.unwrap();
    let req = format!("GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    tls.write_all(req.as_bytes()).await.unwrap();
    tls.flush().await.unwrap();
    let mut raw = Vec::new();
    let _ = tls.read_to_end(&mut raw).await;
    parse_http_response(&raw)
}

fn parse_http_response(raw: &[u8]) -> (u16, String, String) {
    let text = String::from_utf8(raw.to_vec()).unwrap();
    let (head, body) = text
        .split_once("\r\n\r\n")
        .expect("HTTP response has header separator");
    let status_line = head.lines().next().unwrap();
    let code: u16 = status_line
        .split_whitespace()
        .nth(1)
        .unwrap()
        .parse()
        .unwrap();
    (code, head.to_owned(), body.to_owned())
}

pub(super) async fn start_admin_cluster(mtls: bool) -> (Cluster, BTreeMap<Uuid, SocketAddr>) {
    let mut cluster = Cluster::start().await;
    cluster.stop_all().await;
    let mut addrs = BTreeMap::new();
    for (&id, config) in &mut cluster.configs {
        let addr = free_loopback();
        config.admin = Some(AdminConfig {
            listen: addr,
            mtls,
            cluster: BTreeMap::new(),
            metrics_readers: Vec::new(),
            probe_listen: None,
        });
        addrs.insert(id, addr);
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    (cluster, addrs)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn metrics_principal_and_loopback_probe_have_limited_access() {
    let (mut cluster, addresses) = start_admin_cluster(true).await;
    let keeper = cluster.ids[0];
    let probe = free_loopback();
    let admin = cluster
        .configs
        .get_mut(&keeper)
        .unwrap()
        .admin
        .as_mut()
        .unwrap();
    admin.metrics_readers = vec![OTHER.into()];
    admin.probe_listen = Some(probe);
    cluster.running.remove(&keeper).unwrap().stop().await;
    cluster.restart(keeper).await;
    let addr = addresses[&keeper];
    assert_eq!(https_get(addr, &cluster.other, "/metrics").await.0, 200);
    assert_eq!(https_get(addr, &cluster.other, "/live").await.0, 200);
    assert_eq!(https_get(addr, &cluster.other, "/status").await.0, 403);
    let mut config = super::operator::operator_config(&cluster, &addresses);
    config.tls = cluster.other.clone();
    assert!(
        crate::stream::consensus::Operator::new(config)
            .unwrap()
            .set_mode(keeper, "/drain")
            .await
            .unwrap_err()
            .to_string()
            .contains("403")
    );
    assert_eq!(http_get(probe, "/live").await.0, 200);
    assert!(matches!(http_get(probe, "/ready").await.0, 200 | 503));
    assert_eq!(http_get(probe, "/metrics").await.0, 403);
    assert_eq!(http_request(probe, "POST", "/drain").await.0, 403);
    cluster.stop_all().await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn rotating_tls_keeps_existing_connections_and_publishes_only_authorized_credentials() {
    type TlsStream = tokio_rustls::client::TlsStream<tokio::net::TcpStream>;
    async fn connect(addr: SocketAddr, credentials: &Credentials) -> (TlsStream, Vec<u8>) {
        let (tls, _) = credentials.client_protocol(b"http/1.1").unwrap();
        let name = tokio_rustls::rustls::pki_types::ServerName::try_from("logkeeper").unwrap();
        let tcp = tokio::net::TcpStream::connect(addr).await.unwrap();
        let stream = tls.connect(name, tcp).await.unwrap();
        let cert = transport::leaf(stream.get_ref().1.peer_certificates())
            .unwrap()
            .to_vec();
        (stream, cert)
    }

    let (mut cluster, addresses) = start_admin_cluster(true).await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client.create(stream, voters, 1 << 26).await.unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    let keeper = cluster.leader_after_head(&client, stream).await;
    let addr = addresses[&keeper];
    let (mut existing, old) = connect(addr, &cluster.credentials).await;
    let (first, started) = tokio::sync::oneshot::channel();
    let writing = tokio::spawn(async move {
        let payload = Bytes::from_static(b"write during rotation");
        client
            .append(stream, sealed.fence, Lsn(1), payload.clone())
            .await
            .unwrap();
        first.send(()).unwrap();
        for lsn in 2..=32 {
            client
                .append(stream, sealed.fence, Lsn(lsn), payload.clone())
                .await
                .unwrap();
            tokio::time::sleep(Duration::from_millis(15)).await;
        }
        client.head(stream).await.unwrap()
    });
    started.await.unwrap();

    let config = cluster.configs[&keeper].clone();
    let replacement = credentials_with_usages(
        cluster._dir.path(),
        "rotated",
        &format!("urn:logkeeper:keeper:{keeper}"),
        vec![ClientAuth, ServerAuth],
        &cluster.certificate_issuer,
        &config.tls.ca,
    );
    std::fs::rename(replacement.certificate, &config.tls.certificate).unwrap();
    std::fs::rename(replacement.private_key, &config.tls.private_key).unwrap();
    let tls = &cluster.running[&keeper].engine.tls;
    assert!(tls.reload(&config).is_err());
    assert_eq!(connect(addr, &cluster.credentials).await.1, old);
    provision(&config);
    tls.reload(&config).unwrap();
    assert_ne!(connect(addr, &cluster.credentials).await.1, old);
    existing
        .write_all(b"GET /live HTTP/1.1\r\nHost: localhost\r\n\r\n")
        .await
        .unwrap();
    let mut response = Vec::new();
    let _ = existing.read_to_end(&mut response).await;
    assert_eq!(parse_http_response(&response).0, 200);
    assert_eq!(writing.await.unwrap(), Lsn(32));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn admin_plain_http_metrics_health_and_validation() {
    let (mut cluster, addrs) = start_admin_cluster(false).await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());

    // Plain HTTP on a non-loopback address is rejected by config validation.
    let mut bad = cluster.configs[&voters[0]].clone();
    bad.admin = Some(AdminConfig {
        listen: "0.0.0.0:9199".parse().unwrap(),
        mtls: false,
        cluster: BTreeMap::new(),
        metrics_readers: Vec::new(),
        probe_listen: None,
    });
    assert!(bad.validate().is_err());

    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    for i in 1..=5 {
        client
            .append(stream, sealed.fence, Lsn(i), Bytes::from(vec![b'x'; 128]))
            .await
            .unwrap();
    }

    let admin_addr = addrs[&voters[0]];

    // Wait until /ready returns 200 OK on all three voters.
    for &voter in &voters {
        let addr = addrs[&voter];
        timeout(WAIT, async {
            loop {
                let (code, _, _) = http_get(addr, "/ready").await;
                if code == 200 {
                    return;
                }
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("voter becomes ready");
    }

    // /live returns 200 OK.
    let (code, _, body) = http_get(admin_addr, "/live").await;
    assert_eq!(code, 200);
    let live: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(live["live"], true);
    assert_eq!(live["wal_healthy"], true);

    // /safe-to-stop returns 200 OK once liveness pings discover all voters.
    let body = timeout(WAIT, async {
        loop {
            let (code, _, body) = http_get(admin_addr, "/safe-to-stop").await;
            if code == 200 {
                return body;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("safe-to-stop becomes 200 while all voters are up");
    let safe: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(safe["safe"], true);
    assert_eq!(safe["blocking"].as_array().unwrap().len(), 0);

    // /problems reports 0 problems on a healthy stream.
    let (code, _, body) = http_get(admin_addr, "/problems").await;
    assert_eq!(code, 200);
    let problems: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(problems["problem_count"], 0);

    // /metrics exposes Prometheus counters, histograms, liveness, retention, and build info.
    let (code, headers, metrics) = http_get(admin_addr, "/metrics").await;
    assert_eq!(code, 200);
    assert!(headers.contains("text/plain; version=0.0.4"));
    assert!(metrics.contains("logkeeper_build_info{version="));
    assert!(metrics.contains("logkeeper_consensus_refusals_total{reason=\"write.timeout\"}"));
    assert!(metrics.contains("logkeeper_consensus_wal_round_records_count "));
    assert!(metrics.contains("logkeeper_consensus_wal_round_bytes_count "));
    assert!(metrics.contains("logkeeper_consensus_wal_round_duration_seconds_count "));
    assert!(
        metrics
            .contains("logkeeper_consensus_wal_fsync_duration_seconds_count{target=\"segment\"}")
    );
    assert!(
        metrics
            .contains("logkeeper_consensus_wal_fsync_duration_seconds_count{target=\"boundary\"}")
    );
    assert!(metrics.contains("logkeeper_consensus_elections_total{outcome=\"started\"}"));
    assert!(metrics.contains("logkeeper_consensus_snapshots_sent_total{outcome=\"ok\"}"));
    assert!(metrics.contains("logkeeper_consensus_snapshots_received_total{outcome=\"ok\"}"));
    assert!(metrics.contains("logkeeper_consensus_repairs_total{kind=\"voter\",outcome=\"ok\"}"));
    assert!(metrics.contains("logkeeper_consensus_stream_parks_total "));
    assert!(metrics.contains("logkeeper_consensus_stream_wakes_total{trigger=\"client\"}"));
    assert!(metrics.contains("logkeeper_consensus_keeper_liveness{"));
    assert!(metrics.contains("logkeeper_consensus_retained_records_total 5"));
    assert!(metrics.contains("logkeeper_consensus_retained_bytes_total "));
    assert!(metrics.contains("logkeeper_consensus_slow_proposals 0"));
    assert!(metrics.contains("logkeeper_consensus_critical_total "));
    // At least one of the 3 voters led the stream and observed commit_duration_seconds_count > 0,
    // and timed each of its writes through every commit stage.
    let sample = |text: &str, series: &str| -> u64 {
        text.lines()
            .find_map(|line| line.strip_prefix(series))
            .and_then(|rest| rest.trim().parse::<u64>().ok())
            .unwrap_or(0)
    };
    let mut leader_commits = 0u64;
    let mut stages = BTreeMap::<&str, u64>::new();
    for &voter in &voters {
        let (_, _, text) = http_get(addrs[&voter], "/metrics").await;
        leader_commits += sample(&text, "logkeeper_consensus_commit_duration_seconds_count ");
        for stage in ["queue", "wal", "replication", "apply"] {
            *stages.entry(stage).or_default() += sample(
                &text,
                &format!("logkeeper_consensus_commit_stage_seconds_count{{stage=\"{stage}\"}} "),
            );
        }
    }
    assert!(
        leader_commits >= 6,
        "expected >= 6 committed writes, got {leader_commits}"
    );
    for (stage, count) in &stages {
        assert!(*count >= 6, "commit stage {stage} timed {count} writes");
    }

    // HEAD, 404, 405 behavior.
    let (code, _, body) = http_request(admin_addr, "HEAD", "/live").await;
    assert_eq!(code, 200);
    assert!(body.is_empty());
    let (code, _, _) = http_get(admin_addr, "/unknown").await;
    assert_eq!(code, 404);
    let (code, _, _) = http_request(admin_addr, "POST", "/live").await;
    assert_eq!(code, 405);

    // Stop one voter: /safe-to-stop on the remaining voters must turn 503.
    cluster.running.remove(&voters[2]).unwrap().stop().await;
    timeout(WAIT, async {
        loop {
            let (code, _, body) = http_get(admin_addr, "/safe-to-stop").await;
            if code == 503 {
                let parsed: serde_json::Value = serde_json::from_str(&body).unwrap();
                assert_eq!(parsed["safe"], false);
                let blockers = parsed["blocking"].as_array().unwrap();
                assert!(blockers.iter().any(|b| b["voter"] == voters[2].to_string()));
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("safe-to-stop reports down voter");

    // Restart the stopped voter: it catches up, becomes /ready, and /safe-to-stop returns 200.
    cluster.restart(voters[2]).await;
    timeout(WAIT, async {
        loop {
            let (r_code, _, _) = http_get(addrs[&voters[2]], "/ready").await;
            let (s_code, _, _) = http_get(admin_addr, "/safe-to-stop").await;
            if r_code == 200 && s_code == 200 {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("restarted voter becomes ready and safe-to-stop clears");

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn admin_mtls_allows_administrators_and_rejects_non_admins() {
    let (mut cluster, addrs) = start_admin_cluster(true).await;
    let addr = addrs[&cluster.ids[0]];

    // OWNER is in `administrators` -> 200 OK.
    let (code, _, body) = https_get(addr, &cluster.credentials, "/live").await;
    assert_eq!(code, 200);
    let live: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(live["live"], true);

    // OTHER is only reader/writer, not in `administrators` -> 403 Forbidden.
    let (code, _, _) = https_get(addr, &cluster.other, "/live").await;
    assert_eq!(code, 403);

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn problem_streams_report_detects_live_cluster_anomalies() {
    let (mut cluster, addrs) = start_admin_cluster(false).await;
    // Use long repair_after_secs so automatic repair doesn't replace our stopped voter mid-test.
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.repair_after_secs = 3600;
        config.park_after_secs = 3600;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }

    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    client
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"hello"))
        .await
        .unwrap();

    // Find current leader and set preferred domain to a *different* voter's domain
    // directly in memory so we can immediately observe `led_outside_preferred_domain`.
    let leader = timeout(WAIT, async {
        loop {
            for &voter in &voters {
                let engine = &cluster.running[&voter].engine;
                if let Some(group) = engine.groups.lock().await.get(&stream) {
                    if group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
                    {
                        return voter;
                    }
                }
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .expect("stream has a leader");
    let other_voter = voters.into_iter().find(|v| *v != leader).unwrap();
    cluster.running[&leader]
        .engine
        .record_preference(stream, other_voter);

    let (code, _, body) = http_get(addrs[&leader], "/problem-streams").await;
    assert_eq!(code, 200);
    let report: serde_json::Value = serde_json::from_str(&body).unwrap();
    let entry = report["problems"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["stream"] == Uuid::from_u128(stream.0).to_string())
        .expect("stream appears in problem report");
    let reasons = entry["reasons"].as_array().unwrap();
    assert!(
        reasons.iter().any(|r| r == "led_outside_preferred_domain"),
        "expected led_outside_preferred_domain, got {reasons:?}"
    );

    // Stop the other two voters so the stream loses quorum and becomes leaderless + under_replicated.
    for voter in voters.into_iter().filter(|v| *v != leader) {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    timeout(WAIT, async {
        loop {
            let (code, _, body) = http_get(addrs[&leader], "/problems").await;
            assert_eq!(code, 200);
            let report: serde_json::Value = serde_json::from_str(&body).unwrap();
            if let Some(entry) = report["problems"]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p["stream"] == Uuid::from_u128(stream.0).to_string())
            {
                let reasons = entry["reasons"].as_array().unwrap();
                if reasons.iter().any(|r| r == "leaderless")
                    && reasons.iter().any(|r| r == "under_replicated")
                {
                    return;
                }
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("leaderless and under_replicated reported after losing quorum");

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn ready_accepts_parked_streams_and_problems_detects_parked_with_dead_voter() {
    let (mut cluster, addrs) = start_admin_cluster(false).await;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
        config.repair_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }

    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    client
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"parkme"))
        .await
        .unwrap();

    // Wait for stream to park on all three voters.
    timeout(Duration::from_secs(20), async {
        loop {
            let mut all_parked = true;
            for &voter in &voters {
                let engine = &cluster.running[&voter].engine;
                if !engine.parked.read().contains_key(&stream) {
                    all_parked = false;
                }
            }
            if all_parked {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("stream parked on all voters");

    // Parked streams still satisfy /ready.
    let (code, _, body) = http_get(addrs[&voters[0]], "/ready").await;
    assert_eq!(code, 200);
    let ready: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(ready["ready"], true);
    assert_eq!(ready["parked_streams"], 1);

    // Verify /metrics reports park counter >= 1.
    let (_, _, metrics) = http_get(addrs[&voters[0]], "/metrics").await;
    assert!(metrics.contains("logkeeper_consensus_stream_parks_total 1"));

    // Stop two voters so the stream stays parked (wake_for_dead skips streams with 2 dead voters!)
    // and verify `parked_with_dead_voter` is reported once repair_after_secs elapses.
    cluster.running.remove(&voters[1]).unwrap().stop().await;
    cluster.running.remove(&voters[2]).unwrap().stop().await;
    timeout(WAIT, async {
        loop {
            let (code, _, body) = http_get(addrs[&voters[0]], "/problems").await;
            assert_eq!(code, 200);
            let report: serde_json::Value = serde_json::from_str(&body).unwrap();
            if let Some(entry) = report["problems"]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p["stream"] == Uuid::from_u128(stream.0).to_string())
            {
                let reasons = entry["reasons"].as_array().unwrap();
                if reasons.iter().any(|r| r == "parked_with_dead_voter") {
                    return;
                }
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("parked_with_dead_voter reported");

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offline_inspect_verify_and_dump_segment() {
    let mut cluster = Cluster::start().await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    let writer_id = Uuid::new_v4();

    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), writer_id).await.unwrap();
    for i in 1..=8 {
        client
            .append(
                stream,
                sealed.fence,
                Lsn(i),
                Bytes::from(format!("record-{i}")),
            )
            .await
            .unwrap();
    }
    assert_eq!(client.head(stream).await.unwrap(), Lsn(8));

    let target = voters[0];
    let config = cluster.configs[&target].clone();

    // Must refuse while the keeper is still running (LOCK held).
    assert!(config.inspect(None).is_err());
    assert!(config.verify().is_err());
    assert!(config.dump_segment(1, None).is_err());

    // Stop the keeper so offline tools can acquire the exclusive lock.
    cluster.stop_all().await;

    // 1. Inspect every field on the stopped directory.
    let report = config.inspect(Some(stream)).unwrap();
    assert_eq!(report.keeper, target);
    assert_eq!(report.streams.len(), 1);
    let info = &report.streams[0];
    assert_eq!(info.stream, Uuid::from_u128(stream.0));
    assert!(info.vote.is_some());
    assert_eq!(info.membership.voters, voters.to_vec());
    assert!(info.membership.joint_voters.is_none());
    assert!(info.log_range.last_index.is_some());
    assert!(info.applied.is_some());
    let fence = info.fence.as_ref().expect("fence present");
    assert_eq!(fence.epoch, 1);
    assert_eq!(fence.writer, writer_id);
    assert_eq!(fence.owner, OWNER);
    assert!(!fence.recovery_fence);
    assert_eq!(info.head, Some(8));
    assert_eq!(info.floor, Some(1));
    assert_eq!(info.stream_state, "live");
    assert_eq!(info.retained_records, 8);
    assert!(info.retained_bytes > 0);
    assert_eq!(info.ownership.generation, Some(0));
    assert!(info.ownership.installed);
    assert!(!info.parked);
    assert!(!info.quarantined);
    // Display and JSON both work cleanly.
    let text = report.to_string();
    assert!(text.contains(&info.stream.to_string()));
    assert!(serde_json::to_string(&report).is_ok());

    // 2. Verify clean WAL segments, frame CRCs, and hash chain against boundary slots.
    let verified = config.verify().unwrap();
    assert!(
        verified.ok,
        "unexpected verify errors: {:?}",
        verified.errors
    );
    assert!(verified.boundary_chain_verified);
    assert!(verified.segments_checked >= 1);
    assert!(verified.frames_checked >= 10);
    assert_eq!(verified.unpublished_tail_bytes, 0);
    assert!(verified.to_string().contains("verify OK"));

    // 3. Dump segment by config+id and standalone file path.
    let dump = config.dump_segment(1, None).unwrap();
    assert_eq!(dump.segment_id, 1);
    assert!(!dump.frames.is_empty());
    assert!(dump.frames.iter().all(|f| f.crc_ok));
    assert!(dump.frames.iter().any(|f| f.summary.contains("Register(")));
    assert!(dump.frames.iter().any(|f| f.summary.contains("Vote(")));
    assert!(dump.frames.iter().any(|f| f.summary.contains("Append(")));
    assert!(dump.truncated_tail_offset.is_none());

    let seg_path = config
        .data
        .join("raft-segments")
        .join("00000000000000000001.seg");
    let limited = crate::stream::consensus::dump_segment_file(&seg_path, Some(3)).unwrap();
    assert_eq!(limited.frames.len(), 3);
    assert_eq!(limited.incarnation, dump.incarnation);

    // 4. Verify tolerates an unpublished torn tail past the boundary, and dump_segment reports it.
    let original_seg = std::fs::read(&seg_path).unwrap();
    {
        let mut with_tail = original_seg.clone();
        with_tail.extend_from_slice(&[0xff, 0x00, 0x11, 0x22, 0x33]);
        std::fs::write(&seg_path, &with_tail).unwrap();
    }
    let with_tail_verify = config.verify().unwrap();
    assert!(with_tail_verify.ok, "errors: {:?}", with_tail_verify.errors);
    assert_eq!(with_tail_verify.unpublished_tail_bytes, 5);
    let tail_dump = config.dump_segment(1, None).unwrap();
    assert_eq!(
        tail_dump.truncated_tail_offset,
        Some(original_seg.len() as u64)
    );

    // 5. Corrupt a committed frame byte inside segment 1: verify must fail with CRC + chain mismatch.
    let mut corrupted = original_seg.clone();
    let flip_at = 32 + 8 + 1; // inside first frame body
    corrupted[flip_at] ^= 0x55;
    std::fs::write(&seg_path, &corrupted).unwrap();
    let bad_verify = config.verify().unwrap();
    assert!(!bad_verify.ok);
    assert!(
        bad_verify.errors.iter().any(|e| e.contains("CRC mismatch")),
        "expected CRC mismatch in {:?}",
        bad_verify.errors
    );
    assert!(
        bad_verify.errors.iter().any(|e| e.contains("hash chain")),
        "expected hash chain mismatch in {:?}",
        bad_verify.errors
    );
    let bad_dump = config.dump_segment(1, Some(1)).unwrap();
    assert!(!bad_dump.frames[0].crc_ok);

    // Restore segment 1 and corrupt the boundary file -> verify detects no intact slot.
    std::fs::write(&seg_path, &original_seg).unwrap();
    let boundary_path = config.enrollment.join(format!("{target}.boundary"));
    let original_boundary = std::fs::read(&boundary_path).unwrap();
    std::fs::write(&boundary_path, vec![0u8; original_boundary.len()]).unwrap();
    let bad_boundary = config.verify().unwrap();
    assert!(!bad_boundary.ok);
    assert!(
        bad_boundary
            .errors
            .iter()
            .any(|e| e.contains("no intact slot")),
        "expected no intact slot error in {:?}",
        bad_boundary.errors
    );

    // Restore boundary and verify clean again.
    std::fs::write(&boundary_path, &original_boundary).unwrap();
    assert!(config.verify().unwrap().ok);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offline_inspect_reports_quarantined_replica_on_missing_snapshot() {
    let mut cluster = Cluster::start().await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());

    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    for i in 1..=5 {
        client
            .append(stream, sealed.fence, Lsn(i), Bytes::from_static(b"snap"))
            .await
            .unwrap();
    }
    let target = voters[0];
    let group = cluster.group(target, stream).await;
    group.raft.trigger().snapshot().await.unwrap();
    let snap_path = timeout(WAIT, async {
        loop {
            if let Some(path) = group.state.snapshot_path() {
                return path;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .expect("snapshot built");
    drop(group);

    let config = cluster.configs[&target].clone();
    cluster.stop_all().await;

    // Delete the selected snapshot file to simulate media corruption.
    std::fs::remove_file(&snap_path).unwrap();

    let report = config.inspect(Some(stream)).unwrap();
    assert_eq!(report.streams.len(), 1);
    assert!(report.streams[0].quarantined);
    assert!(report.streams[0].quarantine_reason.is_some());
    assert_eq!(report.streams[0].stream_state, "quarantined");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offline_verify_checks_checkpoint_and_multi_segment_chain() {
    let mut cluster = Cluster::start().await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());

    client
        .create(stream, voters, 64 * 1024 * 1024)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    // In test mode, SEGMENT_BYTES and CHECKPOINT_BYTES are 256 KiB; write ~600 KiB
    // so the keeper rolls segments and publishes a WAL checkpoint.
    let payload = Bytes::from(vec![0xab; 32 * 1024]);
    for i in 1..=20 {
        client
            .append(stream, sealed.fence, Lsn(i), payload.clone())
            .await
            .unwrap();
    }
    let target = voters[0];
    let config = cluster.configs[&target].clone();
    cluster.stop_all().await;

    let report = config.verify().unwrap();
    assert!(report.ok, "unexpected verify errors: {:?}", report.errors);
    assert!(report.segments_checked >= 2);
    assert!(report.checkpoint.is_some(), "expected WAL checkpoint");
    assert!(report.checkpoint_chain_verified);
    assert!(report.boundary_chain_verified);

    // Corrupting the published checkpoint file must cause verify to fail.
    let ckpt_id = report.checkpoint.as_ref().unwrap().id;
    let ckpt_path = config
        .data
        .join("raft-checkpoints")
        .join(format!("{ckpt_id}.ckpt"));
    let original_ckpt = std::fs::read(&ckpt_path).unwrap();
    let mut corrupt_ckpt = original_ckpt.clone();
    corrupt_ckpt[10] ^= 0xff;
    std::fs::write(&ckpt_path, &corrupt_ckpt).unwrap();

    let bad = config.verify().unwrap();
    assert!(!bad.ok);
    assert!(
        bad.errors.iter().any(|e| e.contains("checkpoint")),
        "expected checkpoint error in {:?}",
        bad.errors
    );

    std::fs::write(&ckpt_path, &original_ckpt).unwrap();
    assert!(config.verify().unwrap().ok);
}

#[test]
fn in_flight_proposals_turn_slow_after_a_second() {
    let proposals = Arc::new(Proposals::default());
    let metrics = Arc::new(crate::stream::consensus::metrics::Metrics::new());
    let now = std::time::Instant::now();
    let fresh = InFlight::start(&proposals, Uuid::new_v4(), now, metrics.clone());
    let slow = InFlight::start(
        &proposals,
        Uuid::new_v4(),
        now - SLOW_PROPOSAL,
        metrics.clone(),
    );
    let (count, oldest) = proposals.slow();
    assert_eq!(count, 1);
    assert!(oldest >= SLOW_PROPOSAL);
    drop(slow);
    drop(fresh);
    assert_eq!(proposals.slow(), (0, Duration::ZERO));
    assert_eq!(metrics.slow_proposals.load(Ordering::Relaxed), 1);
}

/// The names and bodies of a debug bundle's tar entries.
fn untar(bytes: &[u8]) -> BTreeMap<String, Vec<u8>> {
    let mut entries = BTreeMap::new();
    let mut at = 0;
    while at + 512 <= bytes.len() && bytes[at] != 0 {
        let header = &bytes[at..at + 512];
        let name_end = header[..100].iter().position(|b| *b == 0).unwrap_or(100);
        let name = String::from_utf8(header[..name_end].to_vec()).unwrap();
        let size = u64::from_str_radix(std::str::from_utf8(&header[124..135]).unwrap(), 8).unwrap()
            as usize;
        entries.insert(name, bytes[at + 512..at + 512 + size].to_vec());
        at += 512 + size.div_ceil(512) * 512;
    }
    entries
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn debug_bundle_collects_every_keeper_over_mtls_and_inspects_offline() {
    let (mut cluster, addrs) = start_admin_cluster(true).await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client.create(stream, voters, 1 << 20).await.unwrap();

    let local = voters[0];
    let mut config = cluster.configs[&local].clone();
    let admin = config.admin.as_mut().unwrap();
    // The other keepers are listed by name, resolved when collecting.
    admin.cluster = addrs
        .iter()
        .filter(|(id, _)| **id != local)
        .map(|(id, at)| (*id, format!("localhost:{}", at.port()).parse().unwrap()))
        .collect();
    let raw = serde_json::json!({
        "keeper": local,
        "tls": {"certificate": "keeper.pem", "private_key": "keeper.key", "ca": "ca.pem"},
    });
    // A listener nothing answers on is recorded, not fatal.
    let silent = free_loopback();
    let bundle = config
        .debug_bundle(&raw, &[silent.into()], None)
        .await
        .unwrap();
    let entries = untar(&bundle);
    let config_json: serde_json::Value =
        serde_json::from_slice(&entries["logkeeper-debug/config.json"]).unwrap();
    assert_eq!(config_json["tls"]["private_key"], "<redacted>");
    assert_eq!(config_json["tls"]["certificate"], "keeper.pem");
    for id in addrs.keys() {
        let metrics = &entries[&format!("logkeeper-debug/keepers/{id}/metrics.txt")];
        assert!(String::from_utf8_lossy(metrics).contains("logkeeper_build_info"));
        let status: serde_json::Value =
            serde_json::from_slice(&entries[&format!("logkeeper-debug/keepers/{id}/status.json")])
                .unwrap();
        assert_eq!(status["keeper"], id.to_string());
        assert_eq!(status["status"]["keeper"], id.to_string());
        assert_eq!(status["config"]["tls"]["private_key"], "<redacted>");
        assert!(entries.contains_key(&format!("logkeeper-debug/keepers/{id}/problems.json")));
    }
    let manifest: serde_json::Value =
        serde_json::from_slice(&entries["logkeeper-debug/manifest.json"]).unwrap();
    let endpoints = manifest["endpoints"].as_array().unwrap();
    assert_eq!(endpoints.len(), addrs.len() + 1);
    let unanswered = endpoints
        .iter()
        .find(|endpoint| endpoint["address"] == silent.to_string())
        .unwrap();
    assert!(
        unanswered["answers"]["/metrics"]
            .as_str()
            .unwrap()
            .starts_with("error")
    );

    // A stopped keeper's data directory adds its offline reports.
    cluster.stop_all().await;
    let data = config.data.clone();
    config.admin = None;
    let bundle = config.debug_bundle(&raw, &[], Some(data)).await.unwrap();
    let entries = untar(&bundle);
    let inspect: serde_json::Value =
        serde_json::from_slice(&entries["logkeeper-debug/offline/inspect.json"]).unwrap();
    assert!(
        inspect["streams"]
            .as_array()
            .unwrap()
            .iter()
            .any(|info| info["stream"] == Uuid::from_u128(stream.0).to_string())
    );
    let verify: serde_json::Value =
        serde_json::from_slice(&entries["logkeeper-debug/offline/verify.json"]).unwrap();
    assert_eq!(verify["ok"], true);
}

/// Keepers listed by DNS name resolve at each connect, and the certificate,
/// not the name, says which keeper answered.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn inventory_dns_names_resolve_at_connect_and_identity_comes_from_certificates() {
    let mut cluster = Cluster::start_named().await;
    assert!(cluster.keepers.values().all(|address| address.is_name()));
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client.create(stream, voters, 1 << 26).await.unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    client
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"named"))
        .await
        .unwrap();

    // A restarted keeper binds its named peer and bulk ports on every
    // interface, and its peers find it again under the same names.
    let leader = cluster.leader_after_head(&client, stream).await;
    cluster.running.remove(&leader).unwrap().stop().await;
    cluster.restart(leader).await;
    client
        .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"again"))
        .await
        .unwrap();
    timeout(WAIT, async {
        while !client
            .keeper_status(leader, stream)
            .await
            .is_ok_and(|status| status.replica == Some(true))
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the restarted keeper serves its replica under its name");

    // A name that reaches another keeper is refused: the certificate there
    // names a different keeper than the route.
    let mut misrouted = cluster.keepers.clone();
    let wrong = misrouted[&voters[1]].clone();
    misrouted.insert(voters[0], wrong);
    let confused = Client::new(
        &cluster.credentials,
        misrouted,
        cluster.catalog,
        Duration::from_secs(2),
    )
    .unwrap();
    assert!(confused.keeper_status(voters[0], stream).await.is_err());
    cluster.stop_all().await;
}
