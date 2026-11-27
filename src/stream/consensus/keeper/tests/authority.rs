//! The configuration authority: liveness leases from the catalog gate
//! campaigning, leading and serving, and an operator recovery waits out the
//! lost voters' leases before the recovered configuration serves.

use super::*;
use crate::stream::consensus::{Configuration, Stage, keeper::Recovery, network::RpcFault};

/// The tests' lease (2 s) plus its drift margin (200 ms).
const LEASE_WAIT: Duration = Duration::from_millis(2_200);

/// Waits until every running keeper enforces leases and holds one.
async fn leased(cluster: &Cluster) {
    timeout(WAIT, async {
        while !cluster
            .running
            .values()
            .all(|running| running.engine.lease.enforced() && running.engine.lease.valid())
        {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("every keeper holds an enforced lease");
}

/// Cuts `island` off from every other keeper, the catalog included, while
/// its members still reach each other. Clients still reach every keeper.
fn partition(cluster: &Cluster, island: &[Uuid]) {
    let island = island.to_vec();
    for running in cluster.running.values() {
        let inside = island.contains(&running.engine.id);
        let island = island.clone();
        running
            .engine
            .set_transport_filter(Some(Arc::new(move |_, target, _| {
                if island.contains(&target) == inside {
                    RpcFault::Allow
                } else {
                    RpcFault::Drop(Duration::ZERO)
                }
            })));
    }
}

fn heal(cluster: &Cluster) {
    for running in cluster.running.values() {
        running.engine.set_transport_filter(None);
    }
}

/// A client channel that asks one keeper directly, without leader hints.
fn direct(cluster: &Cluster) -> Rpc {
    let app = cluster
        .credentials
        .client_protocol(Lane::Application.alpn())
        .unwrap()
        .0;
    Rpc::new(app, cluster.keepers.clone(), Lane::Application)
}

/// The page `keeper` serves of `stream` from its applied state, if it serves.
async fn read_from(rpc: &Rpc, keeper: Uuid, stream: StreamId) -> Option<Vec<(Lsn, Bytes)>> {
    match rpc
        .call::<Reply>(
            keeper,
            Frame::Client(Request::Read {
                stream,
                from: Lsn(1),
                limit: 100,
                wait_ms: 0,
            }),
            Duration::from_millis(500),
        )
        .await
    {
        Ok(Reply::Decision(Outcome::Page(page))) => Some(page.records),
        _ => None,
    }
}

async fn append_to(rpc: &Rpc, keeper: Uuid, stream: StreamId, fence: Fence, at: Lsn) -> Reply {
    rpc.call::<Reply>(
        keeper,
        Frame::Client(Request::Append {
            stream,
            fence,
            at,
            payload: Bytes::from(format!("lost-{}", at.0)),
        }),
        Duration::from_millis(1_000),
    )
    .await
    .unwrap_or_else(|_| failure(JournalError::Unavailable))
}

async fn leads(cluster: &Cluster, keeper: Uuid, stream: StreamId) -> bool {
    cluster.running[&keeper]
        .engine
        .groups
        .lock()
        .await
        .get(&stream)
        .is_some_and(|group| {
            group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
        })
}

async fn configured(journal: &Client, stream: StreamId, voters: Voters) -> Configuration {
    timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && configuration.voters == voters
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the recovered stream elected a leader with the new membership")
}

/// CE-4 with running lost voters: two voters of `[a, b, c]` keep running,
/// cut off from the survivor and the catalog, before, during and after the
/// survivor's recovery. They keep a quorum of the old configuration between
/// them, so nothing inside the stream can depose them. Their leases do:
/// within the lease plus the margin of the recovery's commit neither leads
/// nor serves, and no reader sees the old suffix after the recovered
/// configuration first served.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn running_lost_voters_stop_serving_before_the_recovered_configuration_does() {
    let mut cluster = Cluster::start_replicated().await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(0xA1);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 1 << 20)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    for at in 1..=3 {
        journal
            .append(
                stream,
                sealed.fence,
                Lsn(at),
                Bytes::from(format!("record-{at}")),
            )
            .await
            .unwrap();
    }
    let survivor = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while survivor.state.head() != Ok(Lsn(3)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(survivor);

    let rpc = direct(&cluster);
    // A reader keeps asking the lost voters directly, and records what
    // they served and when.
    let stop = Arc::new(AtomicBool::new(false));
    let served = Arc::new(parking_lot::Mutex::new(Vec::new()));
    let reader = {
        let (rpc, stop, served) = (rpc.clone(), stop.clone(), served.clone());
        tokio::spawn(async move {
            while !stop.load(Ordering::Acquire) {
                for keeper in [b, c] {
                    if let Some(records) = read_from(&rpc, keeper, stream).await {
                        served.lock().push((tokio::time::Instant::now(), records));
                    }
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
    };
    // b and c run on, cut off from everyone else; the survivor stops.
    partition(&cluster, &[b, c]);
    cluster.running.remove(&a).unwrap().stop().await;
    // The lost pair elects a leader of the old configuration and accepts a
    // record the survivor never sees, while their leases last.
    let mut lost_suffix = false;
    let until = tokio::time::Instant::now() + Duration::from_millis(1_500);
    while !lost_suffix && tokio::time::Instant::now() < until {
        for keeper in [b, c] {
            if matches!(
                append_to(&rpc, keeper, stream, sealed.fence, Lsn(4)).await,
                Reply::Decision(Outcome::At(Lsn(4)))
            ) {
                lost_suffix = true;
            }
        }
    }

    let report = cluster.configs[&a]
        .recover_stream(
            stream,
            Recovery {
                acknowledge_data_loss: true,
                unreachable: vec![b, c],
                ..Recovery::default()
            },
        )
        .await
        .unwrap();
    let recovered = tokio::time::Instant::now();
    assert!(report.written);
    let mut fenced = report.fenced.clone();
    fenced.sort_unstable();
    assert_eq!(fenced, [b, c]);
    assert!(report.waited >= LEASE_WAIT, "{:?}", report.waited);

    // By the time the recovered configuration may serve, neither lost voter
    // serves a read or accepts a write, and neither holds a lease.
    for keeper in [b, c] {
        assert_eq!(read_from(&rpc, keeper, stream).await, None);
        assert!(!matches!(
            append_to(&rpc, keeper, stream, sealed.fence, Lsn(5)).await,
            Reply::Decision(Outcome::At(_))
        ));
        assert!(!cluster.running[&keeper].engine.lease.valid());
    }
    // A leader without authority commits nothing and steps down once its
    // quorum check fails.
    timeout(Duration::from_secs(5), async {
        while leads(&cluster, b, stream).await || leads(&cluster, c, stream).await {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .unwrap_or_else(|_| {
        for keeper in [b, c] {
            let engine = &cluster.running[&keeper].engine;
            if let Ok(groups) = engine.groups.try_lock()
                && let Some(group) = groups.get(&stream)
            {
                let metrics = group.raft.metrics().borrow_watched().clone();
                eprintln!(
                    "{keeper}: {:?} term {} lease valid {} enforced {} lapses {}",
                    metrics.state,
                    metrics.current_term,
                    engine.lease.valid(),
                    engine.lease.enforced(),
                    engine.lease.lapses.load(Ordering::Relaxed),
                );
            }
        }
        panic!("the lost voters stopped leading")
    });

    // The recovered configuration serves and goes on.
    cluster.restart(a).await;
    configured(&journal, stream, report.voters).await;
    journal.acknowledge_recovery(stream).await.unwrap();
    let resealed = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    assert_eq!(resealed.head, Lsn(3));
    journal
        .append(stream, resealed.fence, Lsn(4), Bytes::from_static(b"new-4"))
        .await
        .unwrap();
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    let first_served = tokio::time::Instant::now();
    assert_eq!(
        page.records.last(),
        Some(&(Lsn(4), Bytes::from_static(b"new-4")))
    );
    // Still cut off, the lost voters serve nothing; the reader saw them
    // serve only before the recovery finished.
    tokio::time::sleep(Duration::from_millis(500)).await;
    stop.store(true, Ordering::Release);
    reader.await.unwrap();
    let served = served.lock().clone();
    assert!(
        !served.is_empty(),
        "the lost voters served before the recovery"
    );
    for (at, records) in &served {
        assert!(
            *at < recovered && *at < first_served,
            "a lost voter served late"
        );
        assert!(records.iter().all(|(_, payload)| payload != "new-4"));
    }
    eprintln!(
        "lost voters served {} reads, the last {:?} before the recovery finished; lost suffix \
         written: {lost_suffix}",
        served.len(),
        recovered - served.last().unwrap().0,
    );

    // Healed, the lost voters rejoin under their leases and stay fenced:
    // the stream's readers see the recovered history only.
    heal(&cluster);
    for keeper in [b, c] {
        timeout(WAIT, async {
            while !cluster.running[&keeper].engine.lease.valid() {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .unwrap();
        assert_eq!(read_from(&rpc, keeper, stream).await, None);
    }
    for _ in 0..5 {
        let page = journal
            .read(stream, Lsn(4), 1, Duration::ZERO)
            .await
            .unwrap();
        assert_eq!(page.records, [(Lsn(4), Bytes::from_static(b"new-4"))]);
    }
    cluster.stop_all().await;
}

/// Without a catalog majority, leadership lapses after the lease, and it
/// comes back when the catalog does.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn leadership_lapses_in_a_catalog_outage_and_returns_with_the_catalog() {
    let mut cluster = Cluster::start_replicated().await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(0xA2);
    let journal = cluster.client_within(&cluster.credentials, Duration::from_millis(800));
    journal
        .create(stream, Voters::from([a, b, c]), 1 << 20)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    journal
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();

    let catalog = cluster.catalog_voters.unwrap();
    for voter in catalog {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    let outage = tokio::time::Instant::now();
    // Within the lease every voter loses its authority.
    timeout(LEASE_WAIT + Duration::from_secs(1), async {
        while [a, b, c]
            .iter()
            .any(|keeper| cluster.running[keeper].engine.lease.valid())
        {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("every lease lapsed");
    eprintln!("every lease lapsed {:?} after the outage", outage.elapsed());
    let rpc = direct(&cluster);
    for keeper in [a, b, c] {
        assert_eq!(read_from(&rpc, keeper, stream).await, None);
    }
    assert!(
        journal
            .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"two"))
            .await
            .is_err()
    );
    timeout(Duration::from_secs(5), async {
        while leads(&cluster, a, stream).await
            || leads(&cluster, b, stream).await
            || leads(&cluster, c, stream).await
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the leader stepped down");

    for voter in catalog {
        cluster.restart(voter).await;
    }
    let journal = cluster.client(&cluster.credentials);
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"two"))
            .await,
        Ok(Lsn(2))
    );
    assert!(
        read_from(&rpc, cluster.leader(stream).await, stream)
            .await
            .is_some()
    );
    cluster.stop_all().await;
}

/// Before the cluster finalizes leases they are advisory: a catalog outage
/// longer than the lease leaves the stream serving, as before.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_unfinalized_cluster_keeps_serving_through_a_catalog_outage() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(0xA3);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 1 << 20)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    // The catalog answers renewals before finalization, advisory ones.
    timeout(WAIT, async {
        while !cluster.running[&a].engine.lease.valid() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap();
    assert!(!cluster.running[&a].engine.lease.enforced());
    for voter in cluster.catalog_voters.unwrap() {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    tokio::time::sleep(LEASE_WAIT + Duration::from_millis(500)).await;
    assert!(!cluster.running[&a].engine.lease.valid());
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
            .await,
        Ok(Lsn(1))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
    cluster.stop_all().await;
}

/// A lease that lapses while a write is in flight: the leader does not
/// acknowledge it, and once the lease returns the stream serves on, with
/// the write either wholly present or absent.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_lease_lapse_mid_write_acknowledges_nothing() {
    let mut cluster = Cluster::start_replicated().await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(0xA4);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 1 << 20)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let engine = cluster.running[&leader].engine.clone();
    // The leader's WAL write takes long enough to lapse the lease under it.
    engine.disk.set_wal_delay(Duration::from_millis(400));
    let rpc = direct(&cluster);
    let write = {
        let rpc = rpc.clone();
        tokio::spawn(async move {
            rpc.call::<Reply>(
                leader,
                Frame::Client(Request::Append {
                    stream,
                    fence: sealed.fence,
                    at: Lsn(1),
                    payload: Bytes::from_static(b"in flight"),
                }),
                Duration::from_secs(5),
            )
            .await
        })
    };
    tokio::time::sleep(Duration::from_millis(100)).await;
    engine.lease.suspended.store(true, Ordering::Release);
    engine.lease.expire();
    let reply = write.await.unwrap();
    assert!(
        !matches!(reply, Ok(Reply::Decision(Outcome::At(_)))),
        "a write was acknowledged after the lease lapsed"
    );
    assert_eq!(read_from(&rpc, leader, stream).await, None);
    assert!(engine.lease.gated.load(Ordering::Relaxed) > 0);
    engine.disk.set_wal_delay(Duration::ZERO);
    engine.lease.suspended.store(false, Ordering::Release);
    // The stream serves again, and the write is all there or not at all.
    let head = journal.head(stream).await.unwrap();
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    match head {
        Lsn(0) => assert!(page.records.is_empty()),
        Lsn(1) => assert_eq!(page.records, [(Lsn(1), Bytes::from_static(b"in flight"))]),
        other => panic!("unexpected head {other:?}"),
    }
    cluster.stop_all().await;
}

/// An operator fence bumps a keeper's epoch: its lease ends, its
/// certifications are dropped, and it rejoins under the new epoch.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_operator_fence_ends_the_lease_and_the_keeper_rejoins() {
    let mut cluster = Cluster::start_replicated().await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, ..] = cluster.ids;
    let engine = cluster.running[&a].engine.clone();
    let epoch = engine.lease.epoch();
    assert!(epoch >= 1);
    let journal = cluster.client(&cluster.credentials);
    journal.fence_keeper(a).await.unwrap();
    timeout(WAIT, async {
        while engine.lease.epoch() != epoch + 1 || !engine.lease.valid() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the fenced keeper rejoined under its new epoch");
    assert!(engine.lease.refusals.load(Ordering::Relaxed) >= 1);
    // A writer cannot fence; neither can a keeper fence another.
    let other = cluster.client(&cluster.other);
    assert!(other.fence_keeper(a).await.is_err());
    cluster.stop_all().await;
}

/// The authority's requests and replies never reach an N-1 peer: they are
/// refused locally on an N-1 connection, and an N keeper that predates them
/// answers their tags with a typed `Unsupported`.
#[test]
fn authority_requests_and_replies_stay_off_n_minus_1() {
    use crate::stream::consensus::network::{DecodedFrame, ReplyV1, WireVersion, decode_frame};
    let keeper = Uuid::from_u128(1);
    let stage = Stage {
        stream: StreamId(9),
        source: 1,
        old: Voters::from([1, 2, 3].map(Uuid::from_u128)),
        target: Voters::from([1, 4, 5].map(Uuid::from_u128)),
    };
    for request in [
        Request::RenewLease {
            keeper,
            incarnation: keeper,
            epoch: 1,
        },
        Request::FenceKeeper(keeper),
        Request::RecoverStream {
            stage,
            dead: vec![],
            record: crate::stream::consensus::authority::RecoveryRecord {
                stream: StreamId(9),
                epoch: 2,
                loss_point: Lsn(0),
                source: crate::stream::consensus::authority::RecoverySource::Survivor,
                time_unix_ms: 0,
            },
        },
    ] {
        let frame = Frame::Client(request);
        assert_eq!(
            frame.encode_for(WireVersion::Previous).unwrap_err().kind(),
            io::ErrorKind::Unsupported
        );
        let bytes = frame.encode_for(WireVersion::Current).unwrap();
        assert!(matches!(
            decode_frame(&bytes, WireVersion::Current).unwrap(),
            DecodedFrame::Frame(_)
        ));
        assert!(decode_frame(&bytes, WireVersion::Previous).is_err());
    }
    let grant = crate::stream::consensus::Grant {
        granted: true,
        enforced: true,
        epoch: 1,
        fenced: Default::default(),
        reused: false,
        duration_ms: 30_000,
        margin_ms: 3_000,
    };
    assert!(ReplyV1::from_reply(Reply::Lease(grant)).is_err());
}
