//! Rolling upgrades: ALPN negotiation (N and N-1), N-1 codecs, feature bits,
//! typed `Unsupported`, and version-mismatch liveness without mass repair.

use super::*;
use crate::stream::consensus::{
    BUILD_VERSION, CLUSTER_VERSION_CURRENT, CLUSTER_VERSION_V1, KeeperStatus, MAX_MESSAGE,
    PREV_ALPN, PREV_CONTROL_ALPN, decode, encode, features,
    network::{self, ReplyV1},
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lanes_accept_n_and_n_minus_1_and_carry_build_version_and_features() {
    let mut cluster = Cluster::start().await;
    let [a, b, _, _] = cluster.ids;
    let client = cluster.client(&cluster.credentials);

    // Current (N) KeeperStatus carries build_version and feature bits.
    let status = client.keeper_status(a, StreamId(1)).await.unwrap();
    assert_eq!(status.keeper, a);
    assert_eq!(status.build_version, BUILD_VERSION);
    assert_eq!(status.features, features::SUPPORTED);
    assert_eq!(status.cluster_version, CLUSTER_VERSION_V1);

    // Liveness pings exchange build version and features across peers.
    timeout(WAIT, async {
        while !cluster.running[&a]
            .engine
            .peer_supports(b, features::SUPPORTED)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("peer liveness ping exchanged feature bits");

    // An N-1 client offering only PREV_ALPN negotiates N-1 and receives ReplyV1/KeeperStatusV1.
    let (v1_tls, _) = cluster.credentials.client_protocol(PREV_ALPN).unwrap();
    let (_, negotiated, mut channel) =
        transport::connect_protocols(&v1_tls, &cluster.keepers[&a].to_string(), &[PREV_ALPN])
            .await
            .unwrap();
    assert_eq!(negotiated.as_slice(), PREV_ALPN);
    network::send(
        &mut channel,
        &network::Frame::Client(Request::KeeperStatus(StreamId(1))),
    )
    .await
    .unwrap();
    let reply_v1: ReplyV1 = network::receive(&mut channel, MAX_MESSAGE).await.unwrap();
    let ReplyV1::Status(status_v1) = reply_v1 else {
        panic!("expected N-1 KeeperStatusV1 reply");
    };
    assert_eq!(status_v1.keeper, a);
    assert!(status_v1.accepting);

    // An N-1 control peer offering only PREV_CONTROL_ALPN sends Frame::Liveness
    // and receives the 5-field KeeperStatusV1.
    let v1_control = cluster.configs[&b]
        .tls
        .peer_protocol(KeeperId(b.as_u128()), PREV_CONTROL_ALPN)
        .unwrap();
    let (_, negotiated, mut control) = transport::connect_protocols(
        &v1_control,
        &cluster.configs[&a].peers[&a].to_string(),
        &[PREV_CONTROL_ALPN],
    )
    .await
    .unwrap();
    assert_eq!(negotiated.as_slice(), PREV_CONTROL_ALPN);
    let own = cluster.running[&b].engine.recognition.own();
    let mut frame = network::batch_frame();
    let ping_bytes = encode(&network::Frame::Liveness(own)).unwrap();
    frame.extend_from_slice(&42u64.to_be_bytes());
    frame.extend_from_slice(&(ping_bytes.len() as u32).to_be_bytes());
    frame.extend_from_slice(&ping_bytes);
    control
        .write_all(network::seal_frame(&mut frame))
        .await
        .unwrap();
    control.flush().await.unwrap();
    let size = network::receive_size(&mut control, MAX_MESSAGE)
        .await
        .unwrap();
    let mut body = vec![0; size];
    control.read_exact(&mut body).await.unwrap();
    assert_eq!(u64::from_be_bytes(body[..8].try_into().unwrap()), 42);
    assert_eq!(body[8], 0);
    let len = u32::from_be_bytes(body[9..13].try_into().unwrap()) as usize;
    let pong_v1: network::PongV1 = decode(&body[13..13 + len]).unwrap();
    assert_eq!(pong_v1.status.keeper, a);
    assert_eq!(pong_v1.known_as, Some(own));

    // An incompatible N-2 ALPN fails TLS handshake with NoApplicationProtocol.
    let old_alpn = b"logkeeper-consensus-control/6";
    let old_tls = cluster.configs[&b]
        .tls
        .peer_protocol(KeeperId(b.as_u128()), old_alpn)
        .unwrap();
    let err = transport::connect_protocols(
        &old_tls,
        &cluster.configs[&a].peers[&a].to_string(),
        &[old_alpn],
    )
    .await
    .unwrap_err();
    assert!(
        network::is_version_mismatch(&err),
        "expected version mismatch error, got {err:?}"
    );

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn unknown_requests_return_typed_unsupported_without_closing_the_connection() {
    let mut cluster = Cluster::start().await;
    let [a, b, _, _] = cluster.ids;

    // Application lane (Current ALPN): unknown Request discriminant -> Reply::Unsupported,
    // followed by a valid Request on the SAME connection.
    let (tls, _) = cluster
        .credentials
        .client_protocol(Lane::Application.alpn())
        .unwrap();
    let (_, _, mut channel) = transport::connect_protocols(
        &tls,
        &cluster.keepers[&a].to_string(),
        &[Lane::Application.alpn()],
    )
    .await
    .unwrap();
    // Frame::Client (tag 0) with unknown Request variant tag 999.
    let mut unknown = Vec::new();
    unknown.extend_from_slice(&0u32.to_le_bytes());
    unknown.extend_from_slice(&999u32.to_le_bytes());
    network::send_encoded(&mut channel, &unknown).await.unwrap();
    let reply: Reply = network::receive(&mut channel, MAX_MESSAGE).await.unwrap();
    assert!(
        matches!(reply, Reply::Unsupported(_)),
        "expected Reply::Unsupported"
    );
    // Connection stays alive and serves the next normal request.
    network::send(
        &mut channel,
        &network::Frame::Client(Request::KeeperStatus(StreamId(1))),
    )
    .await
    .unwrap();
    let reply: Reply = network::receive(&mut channel, MAX_MESSAGE).await.unwrap();
    assert!(matches!(reply, Reply::Status(KeeperStatus { keeper, .. }) if keeper == a));

    // Control lane (Current ALPN): unknown Frame discriminant -> status byte 2 (Unsupported),
    // while a valid Ping in the same batch still succeeds!
    let control_tls = cluster.configs[&b]
        .tls
        .peer_protocol(KeeperId(b.as_u128()), Lane::Control.alpn())
        .unwrap();
    let (_, _, mut control) = transport::connect_protocols(
        &control_tls,
        &cluster.configs[&a].peers[&a].to_string(),
        &[Lane::Control.alpn()],
    )
    .await
    .unwrap();
    let mut batch = network::batch_frame();
    // id=1: unknown frame tag 99
    let bad_frame = 99u32.to_le_bytes();
    batch.extend_from_slice(&1u64.to_be_bytes());
    batch.extend_from_slice(&(bad_frame.len() as u32).to_be_bytes());
    batch.extend_from_slice(&bad_frame);
    // id=2: valid Ping
    let good_frame = encode(&network::Frame::Ping {
        incarnation: cluster.running[&b].engine.recognition.own(),
        version: BUILD_VERSION.to_owned(),
        features: features::SUPPORTED,
    })
    .unwrap();
    batch.extend_from_slice(&2u64.to_be_bytes());
    batch.extend_from_slice(&(good_frame.len() as u32).to_be_bytes());
    batch.extend_from_slice(&good_frame);
    control
        .write_all(network::seal_frame(&mut batch))
        .await
        .unwrap();
    control.flush().await.unwrap();

    let mut seen = BTreeMap::new();
    while seen.len() < 2 {
        let size = network::receive_size(&mut control, MAX_MESSAGE)
            .await
            .unwrap();
        let mut body = vec![0; size];
        control.read_exact(&mut body).await.unwrap();
        let mut cursor = body.as_slice();
        while !cursor.is_empty() {
            let id = u64::from_be_bytes(cursor[..8].try_into().unwrap());
            let status = cursor[8];
            let len = u32::from_be_bytes(cursor[9..13].try_into().unwrap()) as usize;
            let bytes = cursor[13..13 + len].to_vec();
            cursor = &cursor[13 + len..];
            seen.insert(id, (status, bytes));
        }
    }
    assert_eq!(seen[&1].0, 2, "expected typed Unsupported status byte 2");
    assert_eq!(seen[&2].0, 0, "valid Ping in same batch must succeed");
    let pong: network::Pong = decode(&seen[&2].1).unwrap();
    assert_eq!(pong.status.keeper, a);
    assert_eq!(pong.status.build_version, BUILD_VERSION);

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn version_mismatch_counts_as_alive_and_does_not_trigger_repair() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(201);
    journal.create(stream, [a, b, c], 4096).await.unwrap();
    let initial = journal.configuration(stream).await.unwrap();

    // Stop keeper `c` and bind its control/app/bulk ports with a TLS server
    // advertising only an incompatible future ALPN (N+2).
    let c_cfg = cluster.configs[&c].clone();
    cluster.running.remove(&c).unwrap().stop().await;
    let future_alpn = b"logkeeper-consensus-control/99";
    let acceptor = c_cfg
        .tls
        .server_protocols(KeeperId(c.as_u128()), &[future_alpn])
        .unwrap();
    let control_listener = TcpListener::bind(c_cfg.peers[&c].bind_addr())
        .await
        .unwrap();
    let app_acceptor = c_cfg
        .tls
        .server_protocols(KeeperId(c.as_u128()), &[b"logkeeper-consensus/99"])
        .unwrap();
    let app_listener = TcpListener::bind(c_cfg.listen).await.unwrap();
    let stop = CancellationToken::new();
    let stop_ctrl = stop.clone();
    let ctrl_task = tokio::spawn(async move {
        loop {
            tokio::select! {
                () = stop_ctrl.cancelled() => return,
                accepted = control_listener.accept() => {
                    if let Ok((socket, _)) = accepted {
                        let acceptor = acceptor.clone();
                        tokio::spawn(async move { let _ = acceptor.accept(socket).await; });
                    }
                }
            }
        }
    });
    let stop_app = stop.clone();
    let app_task = tokio::spawn(async move {
        loop {
            tokio::select! {
                () = stop_app.cancelled() => return,
                accepted = app_listener.accept() => {
                    if let Ok((socket, _)) = accepted {
                        let acceptor = app_acceptor.clone();
                        tokio::spawn(async move { let _ = acceptor.accept(socket).await; });
                    }
                }
            }
        }
    });

    // Wait for `a` and `b` to observe `c`'s version mismatch.
    timeout(WAIT, async {
        while !cluster.running[&a].engine.version_mismatched(c)
            || !cluster.running[&b].engine.version_mismatched(c)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("peers observed version mismatch");

    // Wait well past `repair_after_secs` (2 s in tests): `c` must NOT be
    // treated as dead and must NOT be replaced by repair!
    tokio::time::sleep(Duration::from_secs(4)).await;
    assert!(!cluster.running[&a].engine.dead(c));
    assert!(!cluster.running[&b].engine.dead(c));
    let current = journal.configuration(stream).await.unwrap();
    assert_eq!(current, initial, "version mismatch must not trigger repair");

    stop.cancel();
    let _ = ctrl_task.await;
    let _ = app_task.await;
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn write_version_gate_keeps_v1_checkpoints_until_finalized_in_replicated_and_single_catalog()
{
    for replicated in [false, true] {
        let mut cluster = if replicated {
            Cluster::start_replicated().await
        } else {
            Cluster::start().await
        };
        let [a, b, c, _] = cluster.ids;
        let client = cluster.client(&cluster.credentials);
        let stream = StreamId(210 + u128::from(replicated));
        client.create(stream, [a, b, c], 4096).await.unwrap();
        let fence = client
            .seal(stream, Epoch(0), Uuid::from_u128(50))
            .await
            .unwrap()
            .fence;
        client
            .append(stream, fence, Lsn(1), Bytes::from_static(b"before"))
            .await
            .unwrap();

        // Before finalize: cluster version is V1 and checkpoints use N-1 magic LKRWAL04.
        assert_eq!(
            client.cluster_version().await,
            Ok(crate::stream::consensus::CLUSTER_VERSION_V1)
        );
        assert!(
            !cluster.running[&a]
                .engine
                .disk
                .write_version_allows(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
        );
        cluster.running[&a]
            .engine
            .disk
            .checkpoint_now()
            .await
            .unwrap();
        let ckpt_dir = cluster.configs[&a].data.join("raft-checkpoints");
        let files: Vec<_> = std::fs::read_dir(&ckpt_dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(files.len(), 1);
        assert_eq!(&std::fs::read(&files[0]).unwrap()[..8], b"LKRWAL04");

        // Finalizing to an unsupported future version is refused with Unsupported.
        assert_eq!(
            client.finalize_version(99).await,
            Err(JournalError::Unsupported)
        );

        // Finalizing while a keeper in the inventory is down is refused as
        // unavailable, and nothing is finalized.
        let stopped = cluster.ids[3];
        cluster.running.remove(&stopped).unwrap().stop().await;
        assert_eq!(
            client
                .finalize_version(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
                .await,
            Err(JournalError::Unavailable)
        );
        assert_eq!(
            client.cluster_version().await,
            Ok(crate::stream::consensus::CLUSTER_VERSION_V1)
        );
        cluster.restart(stopped).await;

        // Once every keeper answers and supports WRITE_VERSION_GATE, finalize
        // succeeds. A probe may still miss a keeper busy recording first
        // contacts, which is the retryable Unavailable.
        timeout(WAIT, async {
            loop {
                match client
                    .finalize_version(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
                    .await
                {
                    Ok(version) => break assert_eq!(version, CLUSTER_VERSION_CURRENT),
                    Err(JournalError::Unavailable) => {
                        tokio::time::sleep(Duration::from_millis(100)).await;
                    }
                    Err(error) => panic!("finalize refused: {error:?}"),
                }
            }
        })
        .await
        .expect("finalize succeeded once every keeper answered");
        // Idempotent repeat succeeds; downgrade below finalized conflicts.
        assert_eq!(
            client
                .finalize_version(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
                .await,
            Ok(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
        );
        assert!(matches!(
            client
                .finalize_version(crate::stream::consensus::CLUSTER_VERSION_V1)
                .await,
            Err(JournalError::Conflict { .. })
        ));

        // Keepers observe the finalized cluster version via liveness sync and
        // begin writing LKRWAL05 checkpoints.
        timeout(WAIT, async {
            while !cluster.running[&a]
                .engine
                .disk
                .write_version_allows(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
            {
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("keeper observed finalized cluster version");
        assert_eq!(
            client
                .keeper_status(a, stream)
                .await
                .unwrap()
                .cluster_version,
            crate::stream::consensus::CLUSTER_VERSION_CURRENT
        );
        cluster.running[&a]
            .engine
            .disk
            .checkpoint_now()
            .await
            .unwrap();
        let files: Vec<_> = std::fs::read_dir(&ckpt_dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(files.len(), 1);
        assert_eq!(&std::fs::read(&files[0]).unwrap()[..8], b"LKRWAL05");

        // Finalized version survives full cluster restart.
        cluster.stop_all().await;
        for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
            cluster.restart(id).await;
        }
        assert_eq!(
            client.cluster_version().await,
            Ok(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
        );
        assert_eq!(client.head(stream).await, Ok(Lsn(1)));
        cluster.stop_all().await;
    }
}

#[test]
fn keeper_config_warns_on_unknown_fields_while_journal_config_stays_strict() {
    let keeper_id = Uuid::from_u128(1);
    let keeper_json = serde_json::json!({
        "keeper": keeper_id,
        "listen": "127.0.0.1:7001",
        "data": "/tmp/data",
        "tls": {
            "certificate": "/tmp/cert.pem",
            "private_key": "/tmp/key.pem",
            "ca": "/tmp/ca.pem"
        },
        "keepers": { keeper_id.to_string(): "127.0.0.1:7001" },
        "peers": { keeper_id.to_string(): "127.0.0.1:7002" },
        "bulk": { keeper_id.to_string(): "127.0.0.1:7003" },
        "domains": { keeper_id.to_string(): "a" },
        "enrollment": "/tmp/reg",
        "catalog": keeper_id,
        "readers": [],
        "writers": [],
        "administrators": [],
        "future_toggle": true,
        "another_unknown": 42
    });
    let (parsed, warnings) =
        Config::from_json_slice_with_warnings(&serde_json::to_vec(&keeper_json).unwrap()).unwrap();
    assert_eq!(parsed.keeper, keeper_id);
    assert!(warnings.contains(&"future_toggle".to_owned()));
    assert!(warnings.contains(&"another_unknown".to_owned()));
    assert_eq!(warnings.len(), 2);

    // JournalConfig stays strict and refuses unknown fields.
    let journal_json = serde_json::json!({
        "keepers": { keeper_id.to_string(): "127.0.0.1:7001" },
        "catalog": keeper_id,
        "voters": [keeper_id, keeper_id, keeper_id],
        "quota_bytes": 4096,
        "future_toggle": true
    });
    let err = serde_json::from_slice::<crate::stream::consensus::JournalConfig>(
        &serde_json::to_vec(&journal_json).unwrap(),
    )
    .unwrap_err();
    assert!(err.to_string().contains("unknown field"), "{err}");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn checksum_failure_quarantines_durably_survives_restart_triggers_repair_and_clears() {
    use std::io::{Read, Seek, SeekFrom, Write};

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(220);
    client.create(stream, [a, b, c], 4096).await.unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(61))
        .await
        .unwrap()
        .fence;
    client
        .append(stream, fence, Lsn(1), Bytes::from_static(b"corrupt-me"))
        .await
        .unwrap();

    // Pick a follower so the other two voters keep quorum for repair.
    let leader = cluster.leader(stream).await;
    let victim = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let group = cluster.group(victim, stream).await;
    group
        .raft
        .wait(Some(WAIT))
        .metrics(|_| group.state.head() == Ok(Lsn(1)), "victim applied LSN 1")
        .await
        .unwrap();

    // Flip one byte in the retained segment slice on `victim`.
    let (payload_file, last_byte) = group.state.payload_path().unwrap();
    let flip = || {
        let mut file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&payload_file)
            .unwrap();
        file.seek(SeekFrom::Start(last_byte)).unwrap();
        let mut byte = [0];
        file.read_exact(&mut byte).unwrap();
        file.seek(SeekFrom::Start(last_byte)).unwrap();
        file.write_all(&[byte[0] ^ 0xff]).unwrap();
        file.sync_all().unwrap();
    };
    flip();

    // Reading from `victim` hits checksum mismatch, returns typed Corrupted,
    // writes a durable quarantine marker in the registry, and reports unhealthy.
    let identity = Identity::Client(journal_contract::Identity::from(OWNER));
    let read_req = Request::Read {
        stream,
        from: Lsn(1),
        limit: 1,
        wait_ms: 0,
    };
    assert!(matches!(
        cluster.running[&victim]
            .engine
            .request(&identity, read_req.clone())
            .await,
        Ok(Reply::Decision(Outcome::Refused(JournalError::Corrupted)))
    ));
    let marker = cluster.configs[&victim]
        .enrollment
        .join(format!("{victim}.quarantine.json"));
    assert!(
        marker.exists(),
        "durable quarantine marker must exist in registry"
    );
    let status = client.keeper_status(victim, stream).await.unwrap();
    assert_eq!(status.replica, Some(false));

    // Even if the byte is restored and `victim` restarts, durable quarantine
    // survives restart until explicitly cleared!
    cluster.running.remove(&victim).unwrap().stop().await;
    flip();
    cluster.restart(victim).await;
    assert_eq!(
        client.keeper_status(victim, stream).await.unwrap().replica,
        Some(false)
    );
    assert!(matches!(
        cluster.running[&victim]
            .engine
            .request(&identity, read_req.clone())
            .await,
        Ok(Reply::Decision(Outcome::Refused(JournalError::Corrupted)))
    ));

    // Meanwhile the stream's leader sees `victim` unhealthy and replaces it.
    let initial_voters = [a, b, c];
    let repaired = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(cfg) = client.configuration(stream).await
                && cfg.voters != initial_voters
                && !cfg.voters.contains(&victim)
            {
                return cfg;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("repair replaced quarantined replica");
    assert!(!repaired.voters.contains(&victim));
    // The replaced copy then retires on its own: the victim detaches it on
    // the new placement and clears its marker, with no operator action.
    timeout(Duration::from_secs(30), async {
        while marker.exists() || cluster.running[&victim].engine.is_quarantined(stream) {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the replaced quarantined copy retired and cleared its marker");
    assert!(
        cluster.running[&victim]
            .engine
            .disk
            .ownership(stream)
            .is_some_and(|book| book.generation().is_none()),
        "the copy is detached"
    );
    // Reads from the healthy quorum still return the intact record.
    let page = client
        .read(stream, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        vec![(Lsn(1), Bytes::from_static(b"corrupt-me"))]
    );

    // Online admin command clears the quarantine marker.
    client.clear_quarantine(victim, stream).await.unwrap();
    assert!(
        !cluster.running[&victim].engine.is_quarantined(stream),
        "online clear_quarantine must clear in-memory and durable markers"
    );
    assert!(!marker.exists(), "empty quarantine file removed on clear");

    // A copy that fails to open for another reason than its data is taken
    // out of service only until the keeper restarts.
    cluster.running[&victim]
        .engine
        .quarantine(stream, &io::Error::other("transient open failure"));
    assert!(cluster.running[&victim].engine.is_quarantined(stream));
    assert!(!marker.exists(), "only corrupt data is quarantined durably");

    // Offline operator command also clears a durable marker on a stopped keeper.
    cluster.running[&victim].engine.quarantine(
        stream,
        &io::Error::new(io::ErrorKind::InvalidData, "manual test quarantine"),
    );
    assert!(marker.exists());
    cluster.running.remove(&victim).unwrap().stop().await;
    assert!(cluster.configs[&victim].clear_quarantine(stream).unwrap());
    assert!(!marker.exists());
    assert!(!cluster.configs[&victim].clear_quarantine(stream).unwrap());
    cluster.restart(victim).await;
    assert!(!cluster.running[&victim].engine.is_quarantined(stream));

    cluster.stop_all().await;
}

/// Damage in a segment that lies wholly before the checkpoint costs only
/// the streams whose payload slices it holds: the checkpoint names them, and
/// every vote and ownership change is in the checkpoint itself.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn salvage_of_a_checkpointed_segment_quarantines_only_the_streams_it_holds() {
    use std::io::{Seek, SeekFrom, Write};

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let client = cluster.client(&cluster.credentials);
    let (lost, kept) = (StreamId(234), StreamId(235));
    // `lost` fills the first 256 KiB test segment before `kept` exists, so
    // segment 1 holds entries of `lost` only.
    let chunk = Bytes::from(vec![b'L'; 64 * 1024]);
    let mut last = BTreeMap::new();
    let mut victim = None;
    for (stream, writer) in [(lost, 81), (kept, 82)] {
        client
            .create(stream, [a, b, c], 4 * 1024 * 1024)
            .await
            .unwrap();
        if victim.is_none() {
            let leader = cluster.leader(lost).await;
            victim = [a, b, c].into_iter().find(|id| *id != leader);
        }
        let fence = client
            .seal(stream, Epoch(0), Uuid::from_u128(writer))
            .await
            .unwrap()
            .fence;
        for lsn in 1..=5 {
            client
                .append(stream, fence, Lsn(lsn), chunk.clone())
                .await
                .unwrap();
        }
        last.insert(stream, fence);
    }
    let victim = victim.unwrap();
    for stream in [lost, kept] {
        let group = cluster.group(victim, stream).await;
        group
            .raft
            .wait(Some(WAIT))
            .metrics(|_| group.state.head() == Ok(Lsn(5)), "victim applied LSN 5")
            .await
            .unwrap();
    }
    let disk = cluster.running[&victim].engine.disk.clone();
    disk.checkpoint_now().await.unwrap();
    cluster.running.remove(&victim).unwrap().stop().await;
    drop(disk);

    let seg1 = cluster.configs[&victim]
        .data
        .join("raft-segments")
        .join("00000000000000000001.seg");
    {
        let mut file = std::fs::OpenOptions::new().write(true).open(&seg1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        file.write_all(b"CORRUPT!").unwrap();
        file.sync_all().unwrap();
    }
    let report = cluster.configs[&victim].salvage().unwrap();
    assert!(report.salvaged);
    assert!(report.damaged_segments.contains(&1));
    assert!(report.quarantined.contains(&lost));
    assert!(!report.quarantined.contains(&kept), "{report}");
    assert!(report.preserved.contains(&kept));

    cluster.restart(victim).await;
    assert_eq!(
        client.keeper_status(victim, lost).await.unwrap().replica,
        Some(false)
    );
    assert_eq!(
        client.keeper_status(victim, kept).await.unwrap().replica,
        Some(true)
    );
    // `kept` still serves from the salvaged keeper's own copy.
    let group = cluster.group(victim, kept).await;
    group
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| group.state.head() == Ok(Lsn(5)),
            "kept reopened at LSN 5",
        )
        .await
        .unwrap();
    let page = group.state.page(Lsn(1), 5).await.unwrap();
    assert_eq!(page.records.len(), 5);
    assert_eq!(page.records[4], (Lsn(5), chunk.clone()));
    // Repair replaces the quarantined copy of `lost` without an operator.
    timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = client.configuration(lost).await
                && !configuration.voters.contains(&victim)
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("repair replaced the salvaged quarantined replica");
    let fence = last[&lost];
    client
        .append(lost, fence, Lsn(6), Bytes::from_static(b"after"))
        .await
        .unwrap();
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offline_salvage_boots_past_damaged_wal_quarantines_affected_streams_and_serves_rest() {
    use std::io::{Read, Seek, SeekFrom, Write};

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let client = cluster.client(&cluster.credentials);

    // Create two streams on voters [a, b, c]. Write `healthy` into segment 1
    // and checkpoint it, then write enough data to `damaged` to roll into
    // segment >= 2 so the two streams hold slices in distinct segments.
    let healthy = StreamId(231);
    let damaged = StreamId(232);
    client
        .create(healthy, [a, b, c], 4 * 1024 * 1024)
        .await
        .unwrap();
    client
        .create(damaged, [a, b, c], 4 * 1024 * 1024)
        .await
        .unwrap();

    // Pick a follower of `damaged` so the other two voters keep quorum for repair.
    let leader_d = cluster.leader(damaged).await;
    let victim = [a, b, c].into_iter().find(|id| *id != leader_d).unwrap();

    let healthy_payload = Bytes::from(vec![b'H'; 4096]);
    let fence_h = client
        .seal(healthy, Epoch(0), Uuid::from_u128(71))
        .await
        .unwrap()
        .fence;
    client
        .append(healthy, fence_h, Lsn(1), healthy_payload.clone())
        .await
        .unwrap();

    // Wait for `victim` to apply healthy LSN 1, then checkpoint it so its
    // slices are recorded in checkpoint.segments under segment 1.
    let group_h = cluster.group(victim, healthy).await;
    group_h
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| group_h.state.head() == Ok(Lsn(1)),
            "victim applied healthy LSN 1",
        )
        .await
        .unwrap();
    cluster.running[&victim]
        .engine
        .disk
        .checkpoint_now()
        .await
        .unwrap();

    // Write ~384 KiB to `damaged` (exceeding test SEGMENT_BYTES = 256 KiB)
    // so `damaged` rolls into segment >= 2.
    let fence_d = client
        .seal(damaged, Epoch(0), Uuid::from_u128(72))
        .await
        .unwrap()
        .fence;
    let chunk = Bytes::from(vec![b'D'; 64 * 1024]);
    for i in 1..=6u64 {
        client
            .append(damaged, fence_d, Lsn(i), chunk.clone())
            .await
            .unwrap();
    }
    let group_d = cluster.group(victim, damaged).await;
    group_d
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| group_d.state.head() == Ok(Lsn(6)),
            "victim applied damaged LSN 6",
        )
        .await
        .unwrap();

    // Stop `victim` cleanly. Running salvage on a healthy WAL must be a no-op.
    cluster.running.remove(&victim).unwrap().stop().await;
    let noop = cluster.configs[&victim].salvage().unwrap();
    assert!(!noop.salvaged);
    assert!(noop.damaged_segments.is_empty());
    assert!(noop.quarantined.is_empty());
    assert!(noop.preserved.contains(&healthy));
    assert!(noop.preserved.contains(&damaged));

    // Corrupt the newest WAL segment (which holds `damaged` frames, not
    // `healthy` slices) in its frame payload to simulate a damaged WAL span.
    let seg_dir = cluster.configs[&victim].data.join("raft-segments");
    let mut seg_files: Vec<(u64, std::path::PathBuf)> = std::fs::read_dir(&seg_dir)
        .unwrap()
        .filter_map(|e| {
            let entry = e.ok()?;
            let name = entry.file_name().into_string().ok()?;
            let num = name.strip_suffix(".seg")?.parse::<u64>().ok()?;
            Some((num, entry.path()))
        })
        .collect();
    seg_files.sort_by_key(|(id, _)| *id);
    assert!(
        seg_files.len() >= 2,
        "expected segment rollover, found {:?}",
        seg_files
    );
    let (bad_seg_id, bad_seg_path) = seg_files.last().unwrap().clone();
    {
        let mut file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&bad_seg_path)
            .unwrap();
        let len = file.metadata().unwrap().len();
        assert!(len > 64);
        let pos = len / 2;
        file.seek(SeekFrom::Start(pos)).unwrap();
        let mut byte = [0u8; 1];
        file.read_exact(&mut byte).unwrap();
        file.seek(SeekFrom::Start(pos)).unwrap();
        file.write_all(&[byte[0] ^ 0xff]).unwrap();
        file.sync_all().unwrap();
    }

    // Strict default startup MUST still refuse to boot on the damaged WAL.
    let strict_boot = cluster.configs[&victim]
        .clone()
        .prepare(CancellationToken::new())
        .await;
    assert!(
        strict_boot.is_err(),
        "strict boot must fail on a damaged WAL span before salvage"
    );

    // Offline salvage walks past the damaged frame. The frame lies past the
    // checkpoint and fails its checksum, so it could have been any stream's
    // vote, trim or deletion: salvage quarantines every stream on `victim`
    // rather than serve one without a record it lost, and writes a clean
    // checkpoint so strict boot works.
    let report = cluster.configs[&victim].salvage().unwrap();
    assert!(report.salvaged);
    assert!(report.damaged_segments.contains(&bad_seg_id));
    assert!(report.quarantined.contains(&damaged));
    assert!(report.quarantined.contains(&healthy));
    assert!(report.preserved.is_empty());

    // Victim now boots strictly.
    cluster.restart(victim).await;

    // Both copies on `victim` return typed Corrupted and report unhealthy,
    // so repair replaces them.
    let identity = Identity::Client(journal_contract::Identity::from(OWNER));
    let read_damaged = Request::Read {
        stream: damaged,
        from: Lsn(1),
        limit: 1,
        wait_ms: 0,
    };
    assert!(matches!(
        cluster.running[&victim]
            .engine
            .request(&identity, read_damaged)
            .await,
        Ok(Reply::Decision(Outcome::Refused(JournalError::Corrupted)))
    ));
    for stream in [damaged, healthy] {
        assert_eq!(
            client.keeper_status(victim, stream).await.unwrap().replica,
            Some(false)
        );
    }

    // Repair replaces `victim` on `damaged`, while `healthy` keeps working.
    let repaired = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(cfg) = client.configuration(damaged).await
                && !cfg.voters.contains(&victim)
            {
                return cfg;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("repair replaced salvaged quarantined replica");
    assert!(!repaired.voters.contains(&victim));

    // Appending to `healthy` still succeeds across the cluster.
    client
        .append(
            healthy,
            fence_h,
            Lsn(2),
            Bytes::from_static(b"after-salvage"),
        )
        .await
        .unwrap();
    let page = client
        .read(healthy, Lsn(1), 2, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 2);

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn placement_change_does_not_quarantine_and_repair_rebalances_violation() {
    use crate::stream::consensus::storage::{Authority, Provision, hex, sha256};

    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(240);
    client.create(stream, [a, b, c], 4096).await.unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(81))
        .await
        .unwrap()
        .fence;
    client
        .append(
            stream,
            fence,
            Lsn(1),
            Bytes::from_static(b"before-domain-change"),
        )
        .await
        .unwrap();

    // Stop all keepers and reassign `b` from domain "b" to domain "a", so the
    // existing voters [a, b, c] now violate distinct failure domains.
    cluster.stop_all().await;
    let enrollment = cluster.configs[&a].enrollment.clone();
    let mut updated_domains = cluster.configs[&a].domains.clone();
    updated_domains.insert(b, "a".into());
    std::fs::write(
        enrollment.join("placement.json"),
        serde_json::to_vec(&Authority {
            catalog: cluster.catalog,
            domains: updated_domains.clone(),
            retired: Default::default(),
        })
        .unwrap(),
    )
    .unwrap();
    for config in cluster.configs.values_mut() {
        config.domains = updated_domains.clone();
    }
    // Re-issue `b`'s enrollment provision for its new domain.
    let b_cfg = &cluster.configs[&b];
    std::fs::write(
        enrollment.join(format!("{b}.provision.json")),
        serde_json::to_vec(&Provision {
            keeper: b,
            data: b_cfg.data.canonicalize().unwrap(),
            domain: "a".into(),
            certificate_sha256: hex(
                &sha256(std::fs::File::open(&b_cfg.tls.certificate).unwrap()).unwrap(),
            ),
        })
        .unwrap(),
    )
    .unwrap();

    let all_ids: Vec<Uuid> = cluster.configs.keys().copied().collect();
    for id in all_ids {
        cluster.restart(id).await;
    }

    // Placement change MUST NOT quarantine any replica of the existing stream.
    for voter in [a, b, c] {
        assert!(
            !cluster.running[&voter].engine.is_quarantined(stream),
            "domain change must not quarantine voter {voter}"
        );
    }

    // Strict placement is STILL enforced on new geneses and stage targets.
    let bad_stream = StreamId(241);
    assert!(
        client.create(bad_stream, [a, b, c], 4096).await.is_err(),
        "new genesis violating updated placement must be rejected"
    );

    // Existing stream continues serving reads and writes while repair
    // rebalances one of the colliding voters to a free domain.
    assert_eq!(client.head(stream).await, Ok(Lsn(1)));
    let page = client
        .read(stream, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        vec![(Lsn(1), Bytes::from_static(b"before-domain-change"))]
    );
    client
        .append(
            stream,
            fence,
            Lsn(2),
            Bytes::from_static(b"during-domain-change"),
        )
        .await
        .unwrap();

    // Repair detects the placement violation and moves the stream to a valid
    // three-distinct-domain roster.
    let rebalanced = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(cfg) = client.configuration(stream).await
                && cluster.running[&d].engine.placement.roster(&cfg.voters)
            {
                return cfg;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("repair rebalanced placement violation");
    assert!(
        cluster.running[&d]
            .engine
            .placement
            .roster(&rebalanced.voters)
    );
    assert!(
        cluster
            .running
            .values()
            .map(|running| {
                running
                    .engine
                    .disk
                    .metrics
                    .placement_violation
                    .load(std::sync::atomic::Ordering::Relaxed)
            })
            .sum::<u64>()
            > 0,
        "placement violation counter must be incremented"
    );

    // Stage targeting a colliding roster must still be rejected.
    assert!(matches!(
        client.replace(stream, rebalanced.revision, [a, b, c]).await,
        Err(JournalError::Conflict { .. })
    ));

    // All records survive rebalancing.
    let page = client
        .read(stream, Lsn(1), 2, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 2);

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn retired_keepers_do_not_quarantine_and_repair_moves_streams_off_them() {
    use std::collections::BTreeSet;

    use crate::stream::consensus::storage::Authority;

    let mut cluster = Cluster::start().await;
    let [a, b, c, _d] = cluster.ids;
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(242);
    client.create(stream, [a, b, c], 4096).await.unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(82))
        .await
        .unwrap()
        .fence;
    client
        .append(stream, fence, Lsn(1), Bytes::from_static(b"before-retire"))
        .await
        .unwrap();

    // Phase 1: mark `c` retired while still present in the inventory (draining).
    cluster.stop_all().await;
    let enrollment = cluster.configs[&a].enrollment.clone();
    let retired = BTreeSet::from([c]);
    std::fs::write(
        enrollment.join("placement.json"),
        serde_json::to_vec(&Authority {
            catalog: cluster.catalog,
            domains: cluster.configs[&a].domains.clone(),
            retired: retired.clone(),
        })
        .unwrap(),
    )
    .unwrap();
    for config in cluster.configs.values_mut() {
        config.retired = retired.clone();
    }
    let all_ids: Vec<Uuid> = cluster.configs.keys().copied().collect();
    for id in all_ids {
        cluster.restart(id).await;
    }

    // No replica is quarantined, and new streams cannot be placed on `c`.
    for voter in [a, b, c] {
        assert!(!cluster.running[&voter].engine.is_quarantined(stream));
    }
    assert!(
        client.create(StreamId(243), [a, b, c], 4096).await.is_err(),
        "new genesis naming a retired keeper must be rejected"
    );

    // Repair automatically moves `stream` off retired keeper `c`.
    let moved = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(cfg) = client.configuration(stream).await
                && !cfg.voters.contains(&c)
            {
                return cfg;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("repair moved stream off retired keeper");
    assert!(!moved.voters.contains(&c));

    // Phase 2: decommission `c` completely from `keepers`/`peers`/`bulk`/`domains`,
    // keeping only its UUID in `retired`. The remaining cluster still boots
    // without quarantining `stream` even though its historical genesis names `c`.
    cluster.stop_all().await;
    cluster.configs.remove(&c);
    cluster.keepers.remove(&c);
    let remaining_domains = {
        let mut d = cluster.configs[&a].domains.clone();
        d.remove(&c);
        d
    };
    std::fs::write(
        enrollment.join("placement.json"),
        serde_json::to_vec(&Authority {
            catalog: cluster.catalog,
            domains: remaining_domains.clone(),
            retired: retired.clone(),
        })
        .unwrap(),
    )
    .unwrap();
    for config in cluster.configs.values_mut() {
        config.keepers.remove(&c);
        config.peers.remove(&c);
        config.bulk.remove(&c);
        config.domains = remaining_domains.clone();
        config.retired = retired.clone();
    }
    let remaining_ids: Vec<Uuid> = cluster.configs.keys().copied().collect();
    for id in remaining_ids {
        cluster.restart(id).await;
    }
    for voter in moved.voters {
        assert!(!cluster.running[&voter].engine.is_quarantined(stream));
    }

    // Client configured with `retired` reads and appends seamlessly.
    let updated_client = Client::new(
        &cluster.credentials,
        cluster.keepers.clone(),
        cluster.catalog,
        Duration::from_secs(10),
    )
    .unwrap()
    .with_retired(retired);
    assert_eq!(updated_client.head(stream).await, Ok(Lsn(1)));
    let page = updated_client
        .read(stream, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        vec![(Lsn(1), Bytes::from_static(b"before-retire"))]
    );
    updated_client
        .append(stream, fence, Lsn(2), Bytes::from_static(b"after-retire"))
        .await
        .unwrap();
    assert_eq!(updated_client.head(stream).await, Ok(Lsn(2)));

    cluster.stop_all().await;
}
