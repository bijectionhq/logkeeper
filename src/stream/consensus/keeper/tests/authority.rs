//! The configuration authority: liveness leases from the catalog gate
//! campaigning, leading and serving, and an operator recovery waits out the
//! lost voters' leases before the recovered configuration serves.

use super::*;
use crate::stream::consensus::{
    Configuration, Stage, decisions, keeper::Recovery, network, network::RpcFault,
};

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
        Ok(Reply::Decision(Outcome::Page(page) | Outcome::RecoveryPage(page))) => {
            Some(page.records)
        }
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
    // The acknowledgement returns the last record kept and writes the
    // recovery's typed entry right after it, the first of the new epoch.
    assert_eq!(journal.acknowledge_recovery(stream).await, Ok(Lsn(3)));
    let resealed = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    assert_eq!(resealed.head, Lsn(4));
    journal
        .append(stream, resealed.fence, Lsn(5), Bytes::from_static(b"new-4"))
        .await
        .unwrap();
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    let first_served = tokio::time::Instant::now();
    assert_eq!(
        page.records.last(),
        Some(&(Lsn(5), Bytes::from_static(b"new-4")))
    );
    let entry = page.recovery(Lsn(4)).expect("the recovery's typed entry");
    assert_eq!(page.recoveries.len(), 1);
    assert_eq!(entry.fence.head, Lsn(3));
    assert_eq!(entry.loss_point, Lsn(3));
    assert_eq!(entry.configuration_epoch, report.revision);
    assert_eq!(entry.marker, None);
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
            .read(stream, Lsn(5), 1, Duration::ZERO)
            .await
            .unwrap();
        assert_eq!(page.records, [(Lsn(5), Bytes::from_static(b"new-4"))]);
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

/// The first bytes of the snapshot `group` would send a follower.
async fn wire_magic(group: &Group) -> [u8; 8] {
    use tokio::io::AsyncReadExt;
    let mut wire = group.raft.get_snapshot().await.unwrap().unwrap().snapshot;
    let mut magic = [0; 8];
    wire.read_exact(&mut magic).await.unwrap();
    magic
}

/// Snapshots `keeper`'s copy of `stream` and waits for it to be selected.
async fn snapshot(cluster: &Cluster, keeper: Uuid, stream: StreamId) -> Arc<Group> {
    let group = cluster.group(keeper, stream).await;
    let index = group.state.applied().unwrap();
    group.raft.trigger().snapshot().await.unwrap();
    timeout(WAIT, group.state.wait_for_snapshot(index))
        .await
        .unwrap()
        .unwrap();
    group
}

/// At the finalized level a recovery leaves one typed entry in the stream,
/// right after the last record kept, as the first entry of the recovered
/// epoch: written when the fence clears, with the consumer's marker inside
/// it, the catalog's record of the recovery, and a kind no append can
/// produce. The recorded recovery and the entry's kind survive snapshots
/// and restarts.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_recovery_leaves_one_typed_entry_that_no_append_can_forge() {
    use journal_contract::{Journal, RecoveryEntry, RecoveryFence, RecoverySource};

    let mut cluster = Cluster::start_replicated().await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(0xA7);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 1 << 20)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    // A writer appends the exact bytes of a recovery entry: they stay
    // client data, whatever they say.
    let forged = RecoveryEntry {
        fence: RecoveryFence {
            epoch: Epoch(2),
            head: Lsn(2),
        },
        configuration_epoch: 1,
        loss_point: Lsn(2),
        exact: true,
        source: RecoverySource::Survivor,
        time_unix_ms: 1,
        marker: Some(Bytes::from_static(b"forged")),
    };
    for (at, payload) in [
        Bytes::from_static(b"record-1"),
        Bytes::from_static(b"record-2"),
        forged.encode(),
    ]
    .into_iter()
    .enumerate()
    {
        journal
            .append(stream, sealed.fence, Lsn(at as u64 + 1), payload)
            .await
            .unwrap();
    }
    // No client seals as the recovery writer to stand in its fence.
    assert!(
        journal
            .seal(
                stream,
                Epoch(1),
                crate::stream::consensus::state::RECOVERY_WRITER
            )
            .await
            .is_err()
    );
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records[2], (Lsn(3), forged.encode()));
    assert!(page.recoveries.is_empty());
    let survivor = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while survivor.state.head() != Ok(Lsn(3)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(survivor);

    for keeper in [a, b, c] {
        cluster.running.remove(&keeper).unwrap().stop().await;
    }
    let report = cluster.configs[&a]
        .recover_stream(
            stream,
            Recovery {
                acknowledge_data_loss: true,
                lost: Some(vec![b, c]),
                unreachable: vec![b, c],
                ..Recovery::default()
            },
        )
        .await
        .unwrap();
    assert!(report.written);
    assert_eq!(report.head, Lsn(3));
    cluster.restart(a).await;
    configured(&journal, stream, report.voters).await;
    assert_eq!(
        journal
            .seal(stream, Epoch(3), Uuid::from_u128(100))
            .await
            .err(),
        Some(JournalError::Recovered { head: Lsn(3) })
    );

    // The recorded recovery waits in the snapshot formats that carry it,
    // and a restart from the snapshot keeps it.
    let group = snapshot(&cluster, a, stream).await;
    let active = group.state.recorded_recovery().unwrap().unwrap().0;
    assert_eq!(
        active,
        RecoveryFence {
            epoch: report.epoch,
            head: Lsn(3),
        }
    );
    assert!(
        std::fs::read(group.state.snapshot_path().unwrap())
            .unwrap()
            .starts_with(b"LKRIDX04")
    );
    assert_eq!(&wire_magic(&group).await, b"LKRIMG06");
    drop(group);
    cluster.running.remove(&a).unwrap().stop().await;
    cluster.restart(a).await;
    let group = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while !group
            .state
            .recorded_recovery()
            .is_ok_and(|recorded| recorded.is_some_and(|(fence, _)| fence == active))
        {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("the restarted survivor kept the recorded recovery");
    drop(group);
    configured(&journal, stream, report.voters).await;

    // The writer's acknowledgement writes the entry with its marker inside
    // and clears exactly that fence.
    let contract = super::recovery::contract_journal(&cluster, &cluster.credentials, report.voters);
    let generic: &dyn Journal = &contract;
    assert_eq!(generic.recovery_fence(stream).await, Ok(Some(active)));
    let stale = RecoveryFence {
        epoch: Epoch(active.epoch.0 - 1),
        ..active
    };
    let marker = Bytes::from_static(b"consumer marker");
    assert_eq!(
        generic
            .acknowledge_recovery_with_marker(stream, stale, marker.clone())
            .await,
        Err(JournalError::Conflict { head: Lsn(3) })
    );
    assert_eq!(
        generic
            .acknowledge_recovery_with_marker(stream, active, marker.clone())
            .await,
        Ok(Lsn(4))
    );
    assert_eq!(
        generic
            .acknowledge_recovery_with_marker(stream, active, marker.clone())
            .await,
        Ok(Lsn(4))
    );
    assert_eq!(
        generic
            .acknowledge_recovery_with_marker(stream, active, Bytes::from_static(b"other"))
            .await,
        Err(JournalError::Conflict { head: Lsn(4) })
    );
    assert_eq!(generic.recovery_fence(stream).await, Ok(None));

    // Readers see the entry's kind and the catalog's record in it.
    let page = generic
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.head, Lsn(4));
    let [(at, entry)] = page.recoveries.as_slice() else {
        panic!("one recovery entry: {:?}", page.recoveries);
    };
    assert_eq!(*at, Lsn(4));
    assert_eq!(entry.fence, active);
    assert_eq!(entry.configuration_epoch, report.revision);
    assert_eq!(entry.loss_point, Lsn(3));
    assert!(entry.exact);
    assert_eq!(entry.source, RecoverySource::Survivor);
    assert!(entry.time_unix_ms > 0);
    assert_eq!(entry.marker.as_ref(), Some(&marker));
    assert_eq!(page.records[3], (Lsn(4), entry.encode()));
    assert_eq!(page.recovery(Lsn(3)), None);
    let entry = entry.clone();

    // Writers resume after it, and their copy of its bytes is client data.
    assert_eq!(generic.seal(stream, Epoch(3)).await, Ok(Lsn(4)));
    assert_eq!(
        generic
            .append(stream, Epoch(3), Lsn(5), entry.encode())
            .await,
        Ok(Lsn(5))
    );
    // The kind survives a snapshot and a restart from it.
    let survivor = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while survivor.state.head() != Ok(Lsn(5)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(survivor);
    let group = snapshot(&cluster, a, stream).await;
    assert_eq!(&wire_magic(&group).await, b"LKRIMG04");
    drop(group);
    cluster.running.remove(&a).unwrap().stop().await;
    cluster.restart(a).await;
    leased(&cluster).await;
    timeout(WAIT, async {
        loop {
            if let Ok(page) = generic.read(stream, Lsn(1), 10, Duration::ZERO).await
                && page.head == Lsn(5)
            {
                assert_eq!(page.recoveries, vec![(Lsn(4), entry.clone())]);
                assert_eq!(page.records[4], (Lsn(5), entry.encode()));
                break;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .unwrap();
    let survivor = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while survivor.state.head() != Ok(Lsn(5)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    let local = survivor.state.page(Lsn(4), 2).await.unwrap();
    assert_eq!(local.recoveries, vec![(Lsn(4), entry)]);
    drop(survivor);
    cluster.stop_all().await;
}

/// `records` without the typed recovery entry at `at`, the first entry of
/// the recovered epoch.
fn without_entry(records: Option<Vec<(Lsn, Bytes)>>, at: Lsn) -> Option<Vec<(Lsn, Bytes)>> {
    records.map(|records| records.into_iter().filter(|(lsn, _)| *lsn != at).collect())
}

/// Whether `keeper` refuses a vote and an append from `sender` at `term`
/// for `stream` by identity, before Raft sees them.
async fn refuses_by_identity(
    cluster: &Cluster,
    keeper: Uuid,
    sender: Uuid,
    stream: StreamId,
    term: u64,
) -> bool {
    let engine = &cluster.running[&keeper].engine;
    let genesis = cluster.group(keeper, stream).await.genesis.clone();
    let vote = crate::stream::consensus::Vote::new(term, sender.as_u128());
    let requests = [
        PeerRequest::Vote(openraft::raft::VoteRequest::new(vote, None)),
        PeerRequest::Append(AppendEntriesRequest {
            vote,
            prev_log_id: None,
            entries: Vec::new(),
            leader_commit: None,
        }),
    ];
    for request in requests {
        match engine
            .peer(sender.as_u128(), genesis.clone(), request, None)
            .await
        {
            Err(error) if error.to_string().contains(network::EXCLUDED) => (),
            _ => return false,
        }
    }
    true
}

/// Model finding 4, with five voters: three lost voters, a quorum of the old
/// configuration, keep running cut off from the survivors and the catalog,
/// and their leader keeps leading on its last lease after the catalog
/// commits the recovery. The second survivor keeps running through the
/// wait-out and may follow that leader there. The catalog fences it below
/// the recovered revision, so it never campaigns, leads or serves the old
/// configuration again; it catches up from the survivor that wrote the
/// recovery, whose history it then holds. Every copy that holds the
/// recovery refuses the lost voters by identity at any term, and no reader
/// sees a lost record after the recovered configuration served.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_lost_leader_of_five_never_overwrites_the_recovered_history() {
    // Voters 1, 2, 3, 4 and 6; spares 5 (the catalog), 7, 8 and 9.
    let mut cluster = Cluster::start_wide(2).await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [writer, other, x, y] = cluster.ids;
    let lost = [x, y, Uuid::from_u128(6)];
    let voters = Voters::sorted(&[writer, other, x, y, lost[2]]).unwrap();
    let stream = StreamId(0xA5);
    let journal = cluster.client(&cluster.credentials);
    journal.create(stream, voters, 1 << 20).await.unwrap();
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
    for id in voters {
        let group = cluster.group(id, stream).await;
        timeout(WAIT, async {
            while group.state.head() != Ok(Lsn(3)) {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap();
    }

    let tip_before = cluster.running[&other]
        .engine
        .disk
        .recovery_point(stream)
        .tip;
    // The second survivor takes nothing from the lost voters until the
    // catalog committed the recovery, so both survivors report the same
    // last entry and the lower keeper ID writes the recovery.
    let gate = Arc::new(AtomicBool::new(true));
    {
        let gate = gate.clone();
        *cluster.running[&other].engine.reject_append.write() =
            Some(Box::new(move |group, sender, _| {
                group == stream
                    && gate.load(Ordering::Acquire)
                    && lost.iter().any(|id| id.as_u128() == sender)
            }));
    }
    // The lost voters reach each other, the catalog and the second
    // survivor; nothing else reaches them.
    let catalog = cluster.catalog;
    for running in cluster.running.values() {
        let inside = lost.contains(&running.engine.id);
        running
            .engine
            .set_transport_filter(Some(Arc::new(move |_, target, _| {
                let allowed = if inside {
                    lost.contains(&target) || target == catalog || target == other
                } else {
                    !lost.contains(&target)
                };
                if allowed {
                    RpcFault::Allow
                } else {
                    RpcFault::Drop(Duration::ZERO)
                }
            })));
    }
    cluster.running.remove(&writer).unwrap().stop().await;

    // The lost quorum commits a record neither survivor holds.
    let rpc = direct(&cluster);
    let lost_append = |at: u64| {
        let rpc = rpc.clone();
        async move {
            for keeper in lost {
                if matches!(
                    append_to(&rpc, keeper, stream, sealed.fence, Lsn(at)).await,
                    Reply::Decision(Outcome::At(_))
                ) {
                    return true;
                }
            }
            false
        }
    };
    timeout(WAIT, async {
        while !lost_append(4).await {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the lost quorum led the old configuration");

    // A reader asks every keeper directly and records what each served;
    // a watcher records whether the second survivor led the stream while
    // the catalog fenced its copy.
    let stop = Arc::new(AtomicBool::new(false));
    let served = Arc::new(parking_lot::Mutex::new(Vec::new()));
    let reader = {
        let (rpc, stop, served) = (rpc.clone(), stop.clone(), served.clone());
        let keepers = cluster.keepers.keys().copied().collect::<Vec<_>>();
        tokio::spawn(async move {
            while !stop.load(Ordering::Acquire) {
                for keeper in &keepers {
                    if let Some(records) = read_from(&rpc, *keeper, stream).await {
                        served
                            .lock()
                            .push((tokio::time::Instant::now(), *keeper, records));
                    }
                }
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
    };
    let fenced_lead = Arc::new(AtomicBool::new(false));
    let watcher = {
        let (stop, fenced_lead) = (stop.clone(), fenced_lead.clone());
        let engine = cluster.running[&other].engine.clone();
        tokio::spawn(async move {
            while !stop.load(Ordering::Acquire) {
                if let Some(group) = engine.groups.lock().await.get(&stream).cloned() {
                    let leading = group.raft.metrics().borrow_watched().state
                        == openraft::ServerState::Leader;
                    let revision = group.state.finalized().map_or(0, |c| c.revision);
                    if leading
                        && decisions::copy_fenced(engine.lease.fenced_below(stream), revision)
                        && engine.lease.valid()
                    {
                        fenced_lead.store(true, Ordering::Release);
                    }
                }
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
    };

    // Once the catalog commits, the lost voters stop renewing: their leader
    // keeps leading on the lease it already holds, and the second survivor
    // takes its appends, as a running survivor may during the wait-out.
    let recovery = {
        let config = cluster.configs[&writer].clone();
        tokio::spawn(async move {
            config
                .recover_stream(
                    stream,
                    Recovery {
                        acknowledge_data_loss: true,
                        unreachable: lost.to_vec(),
                        ..Recovery::default()
                    },
                )
                .await
        })
    };
    let catalog_rpc = direct(&cluster);
    timeout(WAIT, async {
        loop {
            if let Ok(Reply::Staged(stage)) = catalog_rpc
                .call::<Reply>(
                    catalog,
                    Frame::Client(Request::Staging(stream)),
                    Duration::from_millis(500),
                )
                .await
                && stage.recovery()
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(2)).await;
        }
    })
    .await
    .expect("the catalog committed the recovery");
    for id in lost {
        cluster.running[&id]
            .engine
            .lease
            .suspended
            .store(true, Ordering::Release);
    }
    gate.store(false, Ordering::Release);
    let overwritten = lost_append(5).await;
    let report = recovery.await.unwrap().unwrap();
    let recovered = tokio::time::Instant::now();
    assert!(report.written);
    let mut fenced = report.fenced.clone();
    fenced.sort_unstable();
    let mut expected = vec![other];
    expected.extend(lost);
    expected.sort_unstable();
    assert_eq!(fenced, expected, "every voter but the writer is fenced");
    assert!(report.waited >= LEASE_WAIT, "{:?}", report.waited);
    assert!(report.voters.contains(&writer) && report.voters.contains(&other));
    let engine = cluster.running[&other].engine.clone();
    assert_eq!(engine.lease.fenced_below(stream), Some(report.revision));
    // The second survivor refused the lost leader from before its last
    // entry was read: it holds nothing the recovery does not keep.
    assert_eq!(cluster.group(other, stream).await.state.head(), Ok(Lsn(3)));
    assert_eq!(
        engine.disk.recovery_point(stream).tip,
        tip_before,
        "the second survivor took the lost leader's entries"
    );
    for id in lost {
        assert!(!cluster.running[&id].engine.lease.valid());
    }

    // The recovered configuration serves: the writer leads, the second
    // survivor catches up from it, finalizes the recovered revision and is
    // no longer fenced.
    cluster.restart(writer).await;
    configured(&journal, stream, report.voters).await;
    journal.acknowledge_recovery(stream).await.unwrap();
    let resealed = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    // Record 3 is the last kept; the typed recovery entry follows it.
    assert_eq!(resealed.head, Lsn(4));
    journal
        .append(stream, resealed.fence, Lsn(5), Bytes::from_static(b"new-5"))
        .await
        .unwrap();
    let first_served = tokio::time::Instant::now();
    let expected = (1..=3)
        .map(|at| (Lsn(at), Bytes::from(format!("record-{at}"))))
        .chain([(Lsn(5), Bytes::from_static(b"new-5"))])
        .collect::<Vec<_>>();
    for id in report.voters {
        timeout(WAIT, async {
            while without_entry(read_from(&rpc, id, stream).await, Lsn(4)).as_ref()
                != Some(&expected)
            {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .unwrap_or_else(|_| panic!("{id} serves the recovered history"));
    }
    let survivor = cluster.group(other, stream).await;
    assert_eq!(
        survivor.state.finalized().map(|c| c.revision),
        Some(report.revision)
    );
    assert!(engine.lease.permits(stream, || report.revision));

    // Every copy that holds the recovery refuses the lost voters by
    // identity at any term, and still answers its members.
    let term = survivor.raft.metrics().borrow_watched().current_term + 1_000;
    for keeper in report.voters {
        for sender in lost {
            assert!(
                refuses_by_identity(&cluster, keeper, sender, stream, term).await,
                "{keeper} refused {sender}"
            );
        }
    }
    let genesis = survivor.genesis.clone();
    let prevote = PeerRequest::PreVote(openraft::raft::VoteRequest::new(
        crate::stream::consensus::Vote::new(term, other.as_u128()),
        None,
    ));
    assert!(
        cluster.running[&writer]
            .engine
            .peer(other.as_u128(), genesis, prevote, None)
            .await
            .is_ok()
    );

    // Healed, the lost voters stay out, and readers see only the recovered
    // history.
    heal(&cluster);
    for id in lost {
        cluster.running[&id]
            .engine
            .lease
            .suspended
            .store(false, Ordering::Release);
    }
    tokio::time::sleep(LEASE_WAIT).await;
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(without_entry(Some(page.records), Lsn(4)), Some(expected));
    stop.store(true, Ordering::Release);
    reader.await.unwrap();
    watcher.await.unwrap();
    assert!(
        !fenced_lead.load(Ordering::Acquire),
        "the fenced second survivor led the stream"
    );
    let served = served.lock().clone();
    for (at, keeper, records) in &served {
        let lost_record = records
            .iter()
            .any(|(_, payload)| payload.starts_with(b"lost-"));
        assert!(
            !(lost_record && *at >= first_served),
            "{keeper} served a lost record after the recovered history"
        );
        if lost_record {
            assert!(*at < recovered, "{keeper} served a lost record late");
        }
    }
    eprintln!(
        "{} reads served; the lost leader committed during the wait-out: \
         {overwritten}",
        served.len()
    );
    cluster.stop_all().await;
}

/// With five voters and two survivors, the recovery runs on the survivor
/// that knows the later commit even when the other holds the later last
/// entry, and the recovered history keeps every record the first applied.
/// The leader commits record 4 with two voters that then never learn it was
/// committed; one of them leads next and hands record 4 and its own entry to
/// the other survivor under the older commit. Ranked by last entry alone,
/// that survivor would recover without record 4, which the first survivor
/// applied.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_survivor_that_knows_the_later_commit_recovers_over_a_longer_log() {
    // Voters 1, 2, 3, 4 and 6; spares 5 (the catalog), 7, 8 and 9.
    let mut cluster = Cluster::start_wide(2).await;
    cluster.finalize().await;
    leased(&cluster).await;
    let [a, b, c, d] = cluster.ids;
    let voters = Voters::sorted(&[a, b, c, d, Uuid::from_u128(6)]).unwrap();
    let stream = StreamId(0xA6);
    let journal = cluster.client(&cluster.credentials);
    journal.create(stream, voters, 1 << 20).await.unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    let record = |at: u64| Bytes::from(format!("record-{at}"));
    for at in 1..=3 {
        journal
            .append(stream, sealed.fence, Lsn(at), record(at))
            .await
            .unwrap();
    }
    for id in voters {
        let group = cluster.group(id, stream).await;
        timeout(WAIT, async {
            while group.state.head() != Ok(Lsn(3)) {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap();
    }
    let committer = timeout(WAIT, async {
        loop {
            for id in voters {
                if leads(&cluster, id, stream).await {
                    return id;
                }
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the stream has a leader");
    let others = voters
        .iter()
        .copied()
        .filter(|id| *id != committer)
        .collect::<Vec<_>>();
    let (longer, lost) = (others[0], [others[1], others[2], others[3]]);
    cluster.running.remove(&lost[2]).unwrap().stop().await;

    // Record 4 lands at index `k`. The other survivor takes nothing from
    // the leader; the two running lost voters take record 4 but never the
    // commit that covers it.
    let k = cluster
        .group(committer, stream)
        .await
        .raft
        .metrics()
        .borrow_watched()
        .last_log_index
        .unwrap()
        + 1;
    // Nor does it learn a commit that covers record 4 from anyone.
    *cluster.running[&longer].engine.reject_append.write() =
        Some(Box::new(move |group, sender, request| {
            group == stream
                && (sender == committer.as_u128()
                    || request
                        .leader_commit
                        .is_some_and(|commit| commit.index >= k))
        }));
    for id in [lost[0], lost[1]] {
        *cluster.running[&id].engine.reject_append.write() =
            Some(Box::new(move |group, sender, request| {
                group == stream
                    && sender == committer.as_u128()
                    && request
                        .leader_commit
                        .is_some_and(|commit| commit.index >= k)
            }));
    }
    journal
        .append(stream, sealed.fence, Lsn(4), record(4))
        .await
        .unwrap();
    let applied = cluster.group(committer, stream).await;
    timeout(WAIT, async {
        while applied.state.head() != Ok(Lsn(4)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(applied);
    cluster.running.remove(&committer).unwrap().stop().await;

    // A lost voter leads and hands record 4 and its own entry to the other
    // survivor under the commit it knows, below record 4.
    for id in [lost[0], lost[1]] {
        *cluster.running[&id].engine.reject_append.write() = None;
    }
    timeout(WAIT, async {
        while cluster.running[&longer]
            .engine
            .disk
            .recovery_point(stream)
            .tip
            .is_none_or(|tip| tip.index <= k)
        {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("a lost voter led and replicated past record 4");
    let point = cluster.running[&longer].engine.disk.recovery_point(stream);
    assert!(
        point.committed.is_none_or(|committed| committed.index < k),
        "k {k}: tip {:?} committed {:?}",
        point.tip,
        point.committed
    );
    for id in [lost[0], lost[1]] {
        cluster.running.remove(&id).unwrap().stop().await;
    }
    cluster.restart(committer).await;
    let ahead = cluster.running[&committer]
        .engine
        .disk
        .recovery_point(stream);
    assert!(
        ahead
            .committed
            .is_some_and(|committed| committed.index >= k)
    );
    assert!(ahead.tip < point.tip, "{:?} {:?}", ahead.tip, point.tip);

    // The survivor with the longer log refuses and names the other.
    let recovery = || Recovery {
        acknowledge_data_loss: true,
        ..Recovery::default()
    };
    cluster.running.remove(&longer).unwrap().stop().await;
    let refused = cluster.configs[&longer]
        .recover_stream(stream, recovery())
        .await
        .unwrap_err();
    assert!(
        refused.to_string().contains(&committer.to_string()),
        "{refused}"
    );
    cluster.restart(longer).await;
    cluster.running.remove(&committer).unwrap().stop().await;
    let report = cluster.configs[&committer]
        .recover_stream(stream, recovery())
        .await
        .unwrap();
    assert!(report.written);
    assert_eq!(report.head, Lsn(4));
    cluster.restart(committer).await;
    configured(&journal, stream, report.voters).await;
    journal.acknowledge_recovery(stream).await.unwrap();
    let resealed = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    // Record 4 is the last kept; the typed recovery entry follows it.
    assert_eq!(resealed.head, Lsn(5));
    journal
        .append(stream, resealed.fence, Lsn(6), record(6))
        .await
        .unwrap();
    let expected = (1..=4)
        .chain([6])
        .map(|at| (Lsn(at), record(at)))
        .collect::<Vec<_>>();
    let rpc = direct(&cluster);
    for id in report.voters {
        timeout(WAIT, async {
            while without_entry(read_from(&rpc, id, stream).await, Lsn(5)).as_ref()
                != Some(&expected)
            {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .unwrap_or_else(|_| panic!("{id} serves the recovered history"));
    }
    cluster.stop_all().await;
}
