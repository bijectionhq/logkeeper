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
    let control_listener = TcpListener::bind(c_cfg.peers[&c]).await.unwrap();
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
