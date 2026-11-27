//! Parking races: a park against repair, a concurrent wake, a reopen of
//! the same generation, and a park that only some followers accepted.

use super::*;

/// A wake racing a park leaves the stream either open or parked, never
/// neither.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_wake_during_park_never_orphans_the_stream() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(208);
    journal.create(stream, [a, b, c], 4096).await.unwrap();
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
    let parked = engine.parked.read().contains(&stream);
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
    journal.create(stream, [a, b, c], 4096).await.unwrap();
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
