//! Rolling upgrades: ALPN negotiation (N and N-1), N-1 codecs, feature bits,
//! typed `Unsupported`, and version-mismatch liveness without mass repair.

use super::*;
use crate::stream::consensus::{
    BUILD_VERSION, CLUSTER_VERSION_V1, KeeperStatus, MAX_MESSAGE, PREV_ALPN, PREV_CONTROL_ALPN,
    decode, encode, features,
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
