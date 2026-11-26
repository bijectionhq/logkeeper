//! Operational tests: Prometheus `/metrics`, plain HTTP and mTLS admin
//! listeners, `/live`, `/ready`, `/safe-to-stop`, and `/problems`.

use super::*;
use crate::stream::consensus::AdminConfig;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

fn free_loopback() -> SocketAddr {
    std::net::TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
}

async fn http_get(addr: SocketAddr, path: &str) -> (u16, String, String) {
    http_request(addr, "GET", path).await
}

async fn http_request(addr: SocketAddr, method: &str, path: &str) -> (u16, String, String) {
    let mut stream = tokio::net::TcpStream::connect(addr).await.unwrap();
    let req = format!("{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).await.unwrap();
    stream.flush().await.unwrap();
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw).await.unwrap();
    parse_http_response(&raw)
}

async fn https_get(addr: SocketAddr, creds: &Credentials, path: &str) -> (u16, String, String) {
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

async fn start_admin_cluster(mtls: bool) -> (Cluster, BTreeMap<Uuid, SocketAddr>) {
    let mut cluster = Cluster::start().await;
    cluster.stop_all().await;
    let mut addrs = BTreeMap::new();
    for (&id, config) in &mut cluster.configs {
        let addr = free_loopback();
        config.admin = Some(AdminConfig { listen: addr, mtls });
        addrs.insert(id, addr);
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    (cluster, addrs)
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

    // /safe-to-stop returns 200 OK while all voters are up.
    let (code, _, body) = http_get(admin_addr, "/safe-to-stop").await;
    assert_eq!(code, 200);
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
    // At least one of the 3 voters led the stream and observed commit_duration_seconds_count > 0.
    let mut leader_commits = 0u64;
    for &voter in &voters {
        let (_, _, text) = http_get(addrs[&voter], "/metrics").await;
        if let Some(line) = text
            .lines()
            .find(|l| l.starts_with("logkeeper_consensus_commit_duration_seconds_count "))
        {
            leader_commits += line
                .split_whitespace()
                .nth(1)
                .unwrap()
                .parse::<u64>()
                .unwrap();
        }
    }
    assert!(
        leader_commits >= 6,
        "expected >= 6 committed writes, got {leader_commits}"
    );

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
