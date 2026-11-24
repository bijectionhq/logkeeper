use std::fs;

use bytes::Bytes;
use rcgen::{CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair, SanType};

use super::*;

const CLIENT: &str = "urn:logkeeper:client:writer";
const READ_ONLY: &str = "urn:logkeeper:client:reader";

fn ca(path: &Path) -> Issuer<'static, KeyPair> {
    let mut params = CertificateParams::default();
    params.is_ca = IsCa::Ca(rcgen::BasicConstraints::Unconstrained);
    let name = path.file_stem().unwrap().to_str().unwrap();
    params.distinguished_name.push(DnType::CommonName, name);
    let key = KeyPair::generate().unwrap();
    fs::write(path, params.self_signed(&key).unwrap().pem()).unwrap();
    Issuer::new(params, key)
}

fn credentials(
    dir: &Path,
    name: &str,
    uri: &str,
    purpose: ExtendedKeyUsagePurpose,
    issuer: &Issuer<KeyPair>,
    roots: &Path,
) -> Credentials {
    let key = KeyPair::generate().unwrap();
    let mut params = CertificateParams::default();
    params.subject_alt_names = vec![SanType::URI(uri.try_into().unwrap())];
    params.extended_key_usages = vec![purpose];
    let cert = params.signed_by(&key, issuer).unwrap();
    let certificate = dir.join(format!("{name}.pem"));
    let private_key = dir.join(format!("{name}.key"));
    fs::write(&certificate, cert.pem()).unwrap();
    fs::write(&private_key, key.serialize_pem()).unwrap();
    Credentials {
        certificate,
        private_key,
        ca: roots.to_owned(),
    }
}

#[tokio::test]
async fn loopback_mtls_checks_certificate_authority_uri_and_route() {
    let temp = tempfile::tempdir().unwrap();
    let dir = temp.path();
    let roots = dir.join("ca.pem");
    let other_roots = dir.join("other-ca.pem");
    let root = ca(&roots);
    let other = ca(&other_roots);
    let keeper = uuid::Uuid::from_u128(1);
    let id = KeeperId(keeper.as_u128());
    let server = credentials(
        dir,
        "keeper",
        &format!("{KEEPER_URI}{keeper}"),
        ExtendedKeyUsagePurpose::ServerAuth,
        &root,
        &roots,
    );
    let writer = credentials(
        dir,
        "writer",
        CLIENT,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let refused = credentials(
        dir,
        "refused",
        "urn:logkeeper:client:refused",
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let reader = credentials(
        dir,
        "reader",
        READ_ONLY,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let untrusted = credentials(
        dir,
        "untrusted",
        CLIENT,
        ExtendedKeyUsagePurpose::ClientAuth,
        &other,
        &roots,
    );
    assert!(
        server.server(KeeperId(9)).is_err(),
        "daemon accepted wrong keeper certificate"
    );
    assert!(
        writer.server(id).is_err(),
        "daemon accepted a client URI for a keeper"
    );

    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    let path = dir.join("keeper.json");
    fs::write(&path, serde_json::to_vec(&serde_json::json!({
        "keeper": keeper, "listen": address, "data": dir.join("data"), "zone": "test-zone",
        "tls": { "certificate": server.certificate, "private_key": server.private_key, "ca": server.ca },
        "clients": [CLIENT, READ_ONLY],
        "writers": [CLIENT],
        "limits": { "stream_quota_bytes": 1024, "max_record_bytes": 128, "round_bytes_per_stream": 256, "round_requests": 64 }
    })).unwrap()).unwrap();
    let config = Config::read(&path).unwrap();
    assert_eq!(config.listen, address);
    let stop = CancellationToken::new();
    let mut task = tokio::spawn(config.serve(listener, stop.clone()));

    let deadline = Duration::MAX;
    let address = address.to_string();
    let transport = TcpTransport::new(&writer, [(id, address.clone())], deadline).unwrap();
    let stream = StreamId(11);
    let epoch = Epoch(1);
    let ensemble = [id, KeeperId(2), KeeperId(3)];
    let create = transport.call(id, Request::Create { stream, ensemble });
    let created = tokio::select! {
        reply = create => reply.unwrap(),
        server = &mut task => panic!("keeper stopped before serving create: {server:?}"),
    };
    assert_eq!(created, Reply::Created);
    let seal = Request::Seal {
        stream,
        epoch,
        proposal: 1,
        ensemble,
    };
    let Reply::Sealed(view) = transport.call(id, seal).await.unwrap() else {
        panic!("TLS writer did not seal");
    };
    assert_eq!(
        view.promised,
        Some((epoch, Identity::from(CLIENT), 1)),
        "the promise must contain the authenticated certificate URI"
    );
    assert_eq!(
        transport
            .call(
                id,
                Request::Sync {
                    stream,
                    epoch,
                    floor: Lsn(1),
                    from: Lsn(1),
                    records: vec![],
                    runs: vec![],
                    head: Lsn(0),
                    complete: true,
                }
            )
            .await
            .unwrap(),
        Reply::Synced { tail: Lsn(0) }
    );
    assert_eq!(
        transport
            .call(
                id,
                Request::Append {
                    stream,
                    epoch,
                    at: Lsn(1),
                    records: vec![Bytes::from_static(b"record")],
                    head: Lsn(1),
                }
            )
            .await
            .unwrap(),
        Reply::Appended { tail: Lsn(1) }
    );
    let read = Request::Read {
        stream,
        from: Lsn(1),
        max: 1,
        wait_ms: 0,
    };
    let reader = TcpTransport::new(&reader, [(id, address.clone())], deadline).unwrap();
    assert!(matches!(
        reader.call(id, read.clone()).await.unwrap(),
        Reply::Records { .. }
    ));
    for request in [
        Request::Create { stream, ensemble },
        Request::Seal {
            stream,
            epoch: Epoch(2),
            proposal: 1,
            ensemble,
        },
        Request::Delete { stream, ensemble },
    ] {
        assert_eq!(
            reader.call(id, request).await.unwrap(),
            Reply::Refused(Refusal::Unauthorized),
            "reader reached a writer verb"
        );
    }
    assert_eq!(
        transport.call(id, read.clone()).await.unwrap(),
        Reply::Records {
            floor: Lsn(1),
            records: vec![(Lsn(1), Bytes::from_static(b"record"))],
            head: Lsn(1),
        }
    );
    let wrong_roots = Credentials {
        ca: other_roots,
        ..writer.clone()
    };
    for (credentials, label) in [
        (refused, "unauthorized URI"),
        (untrusted, "untrusted client authority"),
        (wrong_roots, "untrusted keeper authority"),
    ] {
        let denied = TcpTransport::new(&credentials, [(id, address.clone())], deadline).unwrap();
        assert!(
            matches!(
                denied.call(id, read.clone()).await,
                Err(TransportError::Protocol(_) | TransportError::Unreachable)
            ),
            "accepted {label}"
        );
    }
    let wrong = KeeperId(9);
    let wrongly_routed = TcpTransport::new(&writer, [(wrong, address)], deadline).unwrap();
    assert_eq!(
        wrongly_routed.call(wrong, read).await,
        Err(TransportError::Protocol(
            "keeper URI does not match route".into()
        ))
    );
    stop.cancel();
    task.await.unwrap().unwrap();
}

#[tokio::test]
async fn writer_round_trips_through_three_tls_keepers() {
    use journal_contract::{Journal, JournalError};

    use crate::stream::writer::Writer;

    let temp = tempfile::tempdir().unwrap();
    let dir = temp.path();
    let roots = dir.join("ca.pem");
    let root = ca(&roots);
    let writer_credentials = credentials(
        dir,
        "writer",
        CLIENT,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let successor_uri = "urn:logkeeper:client:successor";
    let successor_credentials = credentials(
        dir,
        "successor",
        successor_uri,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let reader_credentials = credentials(
        dir,
        "reader",
        READ_ONLY,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let stop = CancellationToken::new();
    let mut routes = Vec::new();
    let mut tasks = Vec::new();
    for zone in 0..3 {
        let keeper = uuid::Uuid::from_u128(zone + 1);
        let name = format!("keeper-{zone}");
        let tls = credentials(
            dir,
            &name,
            &format!("{KEEPER_URI}{keeper}"),
            ExtendedKeyUsagePurpose::ServerAuth,
            &root,
            &roots,
        );
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let listen = listener.local_addr().unwrap();
        let config = Config {
            keeper,
            listen,
            data: dir.join(name),
            zone: format!("test-zone-{zone}"),
            tls,
            clients: vec![CLIENT.into(), successor_uri.into(), READ_ONLY.into()],
            writers: vec![CLIENT.into(), successor_uri.into()],
            limits: Limits::default(),
        };
        tasks.push(tokio::spawn(config.serve(listener, stop.clone())));
        routes.push(listen.to_string());
    }

    let url = format!("logkeeper+tls://{}", routes.join(","));
    let open = async |credentials: &Credentials| {
        let (transport, ensemble) = TcpTransport::discover(&url, credentials, Duration::MAX)
            .await
            .unwrap();
        Writer::new(Arc::new(transport), ensemble).unwrap()
    };
    let writer = open(&writer_credentials).await;
    let successor = open(&successor_credentials).await;
    let reader = open(&reader_credentials).await;
    let stream = StreamId(12);
    writer.create(stream).await.unwrap();
    assert_eq!(writer.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
    let payload = Bytes::from_static(b"over TLS");
    assert_eq!(
        writer
            .append(stream, Epoch(1), Lsn(1), payload.clone())
            .await,
        Ok(Lsn(1))
    );
    assert_eq!(
        successor.seal(stream, Epoch(1)).await,
        Err(JournalError::Fenced { current: Epoch(1) }),
        "a different certificate identity must be fenced at the same epoch"
    );
    assert_eq!(writer.clone().seal(stream, Epoch(1)).await, Ok(Lsn(1)));
    let restarted = open(&writer_credentials).await;
    assert_eq!(
        restarted.seal(stream, Epoch(1)).await,
        Err(JournalError::Fenced { current: Epoch(1) })
    );
    assert_eq!(successor.seal(stream, Epoch(2)).await, Ok(Lsn(1)));
    assert_eq!(reader.head(stream).await, Ok(Lsn(1)));
    assert_eq!(
        reader
            .read(stream, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        [(Lsn(1), payload)]
    );
    assert_eq!(
        reader.seal(stream, Epoch(3)).await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        writer.append(stream, Epoch(1), Lsn(2), Bytes::new()).await,
        Err(JournalError::Fenced { current: Epoch(2) })
    );
    successor.trim(stream, Epoch(2), Lsn(1)).await.unwrap();
    assert_eq!(
        reader.read(stream, Lsn(1), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(2) })
    );
    successor.delete(stream).await.unwrap();
    assert_eq!(reader.head(stream).await, Err(JournalError::Deleted));

    stop.cancel();
    for task in tasks {
        task.await.unwrap().unwrap();
    }
}

/// Forward TCP connections to `target` and count them.
async fn counting_proxy(target: SocketAddr) -> (SocketAddr, Arc<std::sync::atomic::AtomicUsize>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    let accepted = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let count = accepted.clone();
    tokio::spawn(async move {
        while let Ok((mut client, _)) = listener.accept().await {
            count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            tokio::spawn(async move {
                let mut server = TcpStream::connect(target).await?;
                tokio::io::copy_bidirectional(&mut client, &mut server).await
            });
        }
    });
    (address, accepted)
}

#[tokio::test]
async fn concurrent_calls_share_one_connection_and_batches_authorize_each_request() {
    use std::sync::atomic::Ordering::Relaxed;

    const CALLS: usize = 256;
    let temp = tempfile::tempdir().unwrap();
    let dir = temp.path();
    let roots = dir.join("ca.pem");
    let root = ca(&roots);
    let keeper = uuid::Uuid::from_u128(7);
    let id = KeeperId(keeper.as_u128());
    let tls = credentials(
        dir,
        "keeper",
        &format!("{KEEPER_URI}{keeper}"),
        ExtendedKeyUsagePurpose::ServerAuth,
        &root,
        &roots,
    );
    let writer = credentials(
        dir,
        "writer",
        CLIENT,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let reader = credentials(
        dir,
        "reader",
        READ_ONLY,
        ExtendedKeyUsagePurpose::ClientAuth,
        &root,
        &roots,
    );
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let listen = listener.local_addr().unwrap();
    let limits = Limits {
        max_record_bytes: 4 * 1024 * 1024,
        ..Limits::default()
    };
    let config = Config {
        keeper,
        listen,
        data: dir.join("data"),
        zone: "test-zone".into(),
        tls,
        clients: vec![CLIENT.into(), READ_ONLY.into()],
        writers: vec![CLIENT.into()],
        limits,
    };
    let stop = CancellationToken::new();
    let task = tokio::spawn(config.serve(listener, stop.clone()));
    let (proxy, accepted) = counting_proxy(listen).await;
    let deadline = Duration::from_secs(30);
    let transport = TcpTransport::new(&writer, [(id, proxy.to_string())], deadline).unwrap();
    let ensemble = [id, KeeperId(2), KeeperId(3)];

    let replies = futures::future::join_all((0..CALLS).map(|n| {
        let stream = StreamId(1000 + n as u128);
        transport.call(id, Request::Create { stream, ensemble })
    }))
    .await;
    assert!(replies.iter().all(|reply| reply == &Ok(Reply::Created)));
    assert_eq!(
        accepted.load(Relaxed),
        1,
        "{CALLS} concurrent calls must share one keeper connection"
    );

    // Negative control: requests over the shared-connection size use exclusive channels.
    let large = Bytes::from(vec![0; SHARED_REQUEST_BYTES]);
    let before = accepted.load(Relaxed);
    let replies = futures::future::join_all((0..8).map(|n| {
        transport.call(
            id,
            Request::Append {
                stream: StreamId(1000 + n),
                epoch: Epoch(1),
                at: Lsn(1),
                records: vec![large.clone()],
                head: Lsn(0),
            },
        )
    }))
    .await;
    assert!(replies.iter().all(Result::is_ok));
    assert!(
        accepted.load(Relaxed) - before > 1,
        "concurrent exclusive calls should have opened several connections"
    );

    let stream = StreamId(1000);
    let observer = TcpTransport::new(&reader, [(id, proxy.to_string())], deadline).unwrap();
    assert_eq!(
        observer
            .call(
                id,
                Request::Batch(vec![
                    Request::Check {
                        stream,
                        epoch: Epoch(0)
                    },
                    Request::Seal {
                        stream,
                        ensemble,
                        epoch: Epoch(1),
                        proposal: 1,
                    },
                    Request::Read {
                        stream,
                        from: Lsn(1),
                        max: 1,
                        wait_ms: 0
                    },
                ])
            )
            .await
            .unwrap(),
        Reply::Batch(vec![
            Reply::Checked(StreamView {
                promised: None,
                synced: None,
                tail: Lsn(0),
                head: Lsn(0),
                floor: Lsn(1),
                runs: Vec::new(),
                ensemble,
                learner: false,
            }),
            Reply::Refused(Refusal::Unauthorized),
            Reply::Records {
                floor: Lsn(1),
                records: Vec::new(),
                head: Lsn(0)
            },
        ]),
        "a read-only identity must be refused per request inside a batch"
    );
    stop.cancel();
    task.await.unwrap().unwrap();
}
