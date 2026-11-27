//! Keepers whose media was installed again under their old ID.

use super::*;
use crate::stream::consensus::Sealed;
use crate::stream::consensus::Voters;

/// Waits until every running keeper but `id` has recorded `id`'s current
/// media incarnation.
async fn known_by_all(cluster: &Cluster, id: Uuid) {
    let incarnation = cluster.running[&id].engine.disk.incarnation;
    timeout(WAIT, async {
        'wait: loop {
            for (peer, server) in &cluster.running {
                if *peer != id && server.engine.recognition.recorded(id).await != Some(incarnation)
                {
                    tokio::time::sleep(Duration::from_millis(20)).await;
                    continue 'wait;
                }
            }
            return;
        }
    })
    .await
    .unwrap();
}

/// Stops `id`, deletes its data volume and its registry records except the
/// operator's provision, installs it again under the same ID and restarts
/// it.
async fn wipe(cluster: &mut Cluster, id: Uuid) {
    let previous = cluster.running[&id].engine.disk.incarnation;
    cluster.running.remove(&id).unwrap().stop().await;
    let config = cluster.configs[&id].clone();
    std::fs::remove_dir_all(&config.data).unwrap();
    for suffix in ["enrolled", "wal", "boundary", "incarnations.json"] {
        let _ = std::fs::remove_file(config.enrollment.join(format!("{id}.{suffix}")));
    }
    config.initialize().unwrap();
    cluster.restart(id).await;
    assert_ne!(cluster.running[&id].engine.disk.incarnation, previous);
}

async fn reused(cluster: &Cluster, id: Uuid) {
    let engine = &cluster.running[&id].engine;
    timeout(WAIT, async {
        while !engine.recognition.reused() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("a peer reported the keeper's old incarnation");
}

async fn holds(cluster: &Cluster, id: Uuid, stream: StreamId) -> bool {
    let engine = &cluster.running[&id].engine;
    engine.disk.genesis(stream).is_some() || engine.groups.lock().await.contains_key(&stream)
}

struct Wiped {
    cluster: Cluster,
    journal: Client,
    stream: StreamId,
    sealed: Sealed,
    leader: Uuid,
    witness: Uuid,
}

/// Commits entry 2 on the leader and one witness while the third voter
/// lags at entry 1, stops the leader, and wipes the witness, which comes
/// back under its old ID. The laggard and the wiped witness form a majority
/// of the voters.
async fn wiped_witness(stream: StreamId) -> Wiped {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap();
    journal
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let others = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>();
    let (witness, laggard) = (others[0], others[1]);
    known_by_all(&cluster, witness).await;
    // The laggard misses the next entry; it commits on the leader and the
    // witness.
    *cluster.running[&laggard].engine.reject_append.write() =
        Some(Box::new(move |group, _, request| {
            group == stream && !request.entries.is_empty()
        }));
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"two"))
            .await,
        Ok(Lsn(2))
    );
    cluster.running.remove(&leader).unwrap().stop().await;
    *cluster.running[&laggard].engine.reject_append.write() = None;
    wipe(&mut cluster, witness).await;
    Wiped {
        cluster,
        journal,
        stream,
        sealed,
        leader,
        witness,
    }
}

/// A keeper that lost both its data and registry volumes and was installed
/// again under the same ID must not act as a voter with an empty log. If it
/// did, the lagging voter and the wiped one could elect a leader that lacks
/// an entry committed on the lost copy, and the stream's head would go back.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_wiped_keeper_under_its_old_id_cannot_erase_committed_entries() {
    let Wiped {
        mut cluster,
        stream,
        witness,
        ..
    } = wiped_witness(StreamId(60)).await;
    reused(&cluster, witness).await;
    let impatient = cluster.client_within(&cluster.credentials, Duration::from_millis(500));
    let deadline = tokio::time::Instant::now() + Duration::from_secs(5);
    while tokio::time::Instant::now() < deadline {
        let head = impatient.head(stream).await;
        assert!(
            head.is_err(),
            "the laggard and the wiped witness elected a leader: head {head:?}"
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    // The wiped keeper registered nothing it was not staged.
    assert!(!holds(&cluster, witness, stream).await);
    assert!(!cluster.running[&witness].engine.recognition.confirmed());
    cluster.stop_all().await;
}

/// With the old leader back, the stream elects it again, keeps entry 2,
/// and its leader replaces the wiped voter, which reports no replica.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_old_leader_restores_a_stream_beside_a_wiped_voter() {
    let Wiped {
        mut cluster,
        journal,
        stream,
        sealed,
        leader,
        witness,
    } = wiped_witness(StreamId(61)).await;
    reused(&cluster, witness).await;
    cluster.restart(leader).await;
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    let page = journal
        .read(stream, Lsn(2), 1, Duration::from_secs(1))
        .await
        .unwrap();
    assert_eq!(page.records, [(Lsn(2), Bytes::from_static(b"two"))]);
    let repaired = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && !configuration.voters.contains(&witness)
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the leader replaced the wiped voter");
    assert!(repaired.voters.contains(&leader));
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(3), Bytes::from_static(b"three"))
            .await,
        Ok(Lsn(3))
    );
    assert!(!holds(&cluster, witness, stream).await);
    cluster.stop_all().await;
}

/// A voter that was down when its stream was created registers it from
/// its peers' traffic once a peer confirmed its identity, and catches up.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_voter_down_at_create_registers_from_peer_traffic() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(62);
    cluster.running.remove(&c).unwrap().stop().await;
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap();
    journal
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();
    assert!(cluster.running[&a].engine.disk.genesis(stream).is_some());
    cluster.restart(c).await;
    let group = cluster.group(c, stream).await;
    timeout(WAIT, async {
        while group.state.head() != Ok(Lsn(1)) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the late voter caught up");
    let recognition = &cluster.running[&c].engine.recognition;
    assert!(recognition.confirmed() && !recognition.reused());
    cluster.stop_all().await;
}

/// Each keeper's record of its peers' incarnations, and the marks of reuse,
/// survive restarts.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn peer_incarnations_survive_restarts() {
    let mut cluster = Cluster::start().await;
    let [a, b, ..] = cluster.ids;
    known_by_all(&cluster, b).await;
    let first = cluster.running[&b].engine.disk.incarnation;
    let path = storage::Incarnations::path(&cluster.configs[&a].enrollment, a);
    cluster.running.remove(&a).unwrap().stop().await;
    let stored = storage::Incarnations::load(&path).unwrap();
    assert_eq!(stored.peers.get(&b), Some(&first));
    assert!(stored.reincarnated.is_empty() && !stored.reused);
    // A restart loads the record before any ping, and a peer's own restart
    // keeps its incarnation.
    cluster.restart(a).await;
    let recognition = &cluster.running[&a].engine.recognition;
    assert_eq!(recognition.recorded(b).await, Some(first));
    cluster.running.remove(&b).unwrap().stop().await;
    cluster.restart(b).await;
    assert_eq!(cluster.running[&b].engine.disk.incarnation, first);
    timeout(WAIT, async {
        while !cluster.running[&b].engine.recognition.confirmed() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap();
    assert!(
        cluster.running[&a]
            .engine
            .recognition
            .reincarnated_peers()
            .read()
            .is_empty()
    );
    // Wiped under its old ID, the peer is marked by the others and marks
    // itself, and both marks outlive restarts.
    known_by_all(&cluster, b).await;
    wipe(&mut cluster, b).await;
    reused(&cluster, b).await;
    let marked = |cluster: &Cluster| {
        cluster.running[&a]
            .engine
            .recognition
            .reincarnated_peers()
            .read()
            .contains(&b.as_u128())
    };
    timeout(WAIT, async {
        while !marked(&cluster) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap();
    for id in [a, b] {
        cluster.running.remove(&id).unwrap().stop().await;
        cluster.restart(id).await;
    }
    assert!(marked(&cluster));
    let recognition = &cluster.running[&b].engine.recognition;
    assert!(recognition.reused() && !recognition.registers(true));
    assert_eq!(
        recognition.recorded(a).await,
        Some(cluster.running[&a].engine.disk.incarnation)
    );
    cluster.stop_all().await;
}

/// A keeper whose ID was reused still takes a replica its stream's leader
/// stages on it, and serves it.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_reused_keeper_takes_and_serves_a_staged_replica() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    known_by_all(&cluster, d).await;
    wipe(&mut cluster, d).await;
    reused(&cluster, d).await;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(63);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap();
    journal
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();
    let current = journal.configuration(stream).await.unwrap();
    let placed = journal
        .replace(stream, current.revision, Voters::from([a, b, d]))
        .await
        .unwrap();
    assert_eq!(placed.voters, [a, b, d]);
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"two"))
            .await,
        Ok(Lsn(2))
    );
    let group = cluster.group(d, stream).await;
    timeout(WAIT, async {
        while group.state.head() != Ok(Lsn(2)) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the staged replica caught up");
    let engine = &cluster.running[&d].engine;
    let before = engine.scoped_reads.load(Ordering::Relaxed);
    let local = cluster
        .client(&cluster.credentials)
        .with_local_keepers([d].into_iter().collect());
    let page = local
        .read(stream, Lsn(1), 2, Duration::from_secs(1))
        .await
        .unwrap();
    assert_eq!(
        page.records,
        [
            (Lsn(1), Bytes::from_static(b"one")),
            (Lsn(2), Bytes::from_static(b"two"))
        ]
    );
    assert!(engine.scoped_reads.load(Ordering::Relaxed) > before);
    cluster.stop_all().await;
}
