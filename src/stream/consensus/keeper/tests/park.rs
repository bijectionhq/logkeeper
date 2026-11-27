//! Parking races: a park against repair, a concurrent wake, a reopen of
//! the same generation, and a park that only some followers accepted.

use super::*;
use crate::stream::consensus::Voters;

async fn parking_cluster(repair_after_secs: Option<u64>) -> Cluster {
    let mut cluster = Cluster::start().await;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
        if let Some(secs) = repair_after_secs {
            config.repair_after_secs = secs;
        }
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    cluster
}

/// A leader does not park a stream whose membership a repair holds.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn park_idle_leaves_a_stream_under_repair_open() {
    let mut cluster = parking_cluster(Some(2)).await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(207);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal.prefer_leader(stream, a).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, a).await);

    let engine_a = cluster.running[&a].engine.clone();
    engine_a.fail_repairs.write().insert(stream);
    cluster.running.remove(&c).unwrap().stop().await;
    timeout(WAIT, async {
        while !engine_a.dead(c) {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("leader marked the stopped follower dead");

    // A replacement in flight holds the membership lock.
    let group_a = cluster.group(a, stream).await;
    let repairing = group_a.membership.lock().await;
    tokio::time::sleep(Duration::from_millis(2500)).await;
    engine_a.park_idle().await;
    assert!(
        !group_a.stop.is_cancelled() && group_a.state.healthy(),
        "park_idle must not close a group whose membership a repair holds"
    );
    drop(repairing);
    cluster.stop_all().await;
}

/// A wake racing a park leaves the stream either open or parked, never
/// neither.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_wake_during_park_never_orphans_the_stream() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(208);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let _ = cluster.group(a, stream).await;

    let engine = cluster.running[&a].engine.clone();
    // Both the park and the wake queue on the groups lock.
    let groups = engine.groups.lock().await;
    let parking = tokio::spawn({
        let engine = engine.clone();
        async move { engine.park(stream).await }
    });
    tokio::time::sleep(Duration::from_millis(100)).await;
    let waking = tokio::spawn({
        let engine = engine.clone();
        async move { engine.unpark(stream).await.is_some() }
    });
    tokio::time::sleep(Duration::from_millis(100)).await;
    drop(groups);
    parking.await.unwrap();
    waking.await.unwrap();

    let open = engine.groups.lock().await.contains_key(&stream);
    let parked = engine.parked.read().contains_key(&stream);
    assert!(
        open != parked,
        "the stream is open ({open}) or parked ({parked}), exactly one"
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

/// Parking returns only after the closed group's Raft has stopped, so a
/// reopen of the same generation never runs beside it.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn parking_stops_the_closed_group_before_it_returns() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(213);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let engine = cluster.running[&a].engine.clone();
    let group = cluster.group(a, stream).await;
    engine.park(stream).await;
    assert!(
        group.raft.metrics().borrow_watched().running_state.is_err(),
        "the parked group's Raft core has shut down"
    );
    let reopened = engine.unpark(stream).await.expect("the stream reopens");
    assert!(!Arc::ptr_eq(&reopened, &group));
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

/// A follower that parked while another declined does not refuse its
/// leader's heartbeats for long: it reopens.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_follower_parked_by_a_declined_park_reopens() {
    // A leader parks past a follower it counts dead. Under machine load a
    // 2 s repair delay can count the declining follower dead, so this test
    // keeps every keeper alive for a minute.
    let mut cluster = parking_cluster(Some(60)).await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(209);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal.prefer_leader(stream, a).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, a).await);

    let engine_a = cluster.running[&a].engine.clone();
    let engine_b = cluster.running[&b].engine.clone();
    let group_c = cluster.group(c, stream).await;
    // `c` keeps serving a client from the start, so every park round,
    // whether this test's or the repair loop's, finds `b` idle and `c` not.
    let busy = CancellationToken::new();
    tokio::spawn({
        let busy = busy.clone();
        async move {
            while !busy.is_cancelled() {
                *group_c.used.lock() = Instant::now();
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        }
    });
    timeout(WAIT, async {
        while !engine_b.parked.read().contains_key(&stream) {
            engine_a.park_idle().await;
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("b accepted a park that c declined");
    assert!(engine_a.groups.lock().await.contains_key(&stream));

    timeout(WAIT, async {
        while engine_b.parked.read().contains_key(&stream)
            || !engine_b.groups.lock().await.contains_key(&stream)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the follower left parked by a declined park reopened");
    assert!(engine_a.groups.lock().await.contains_key(&stream));
    busy.cancel();
    cluster.stop_all().await;
}
