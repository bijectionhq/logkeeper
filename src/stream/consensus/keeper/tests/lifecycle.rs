//! Stream copies that are not open: past the stream limit at startup,
//! retired while parked, and deleted.

use super::*;

/// A keeper restarted past its stream limit skips a stream, and the reaper
/// must not delete the snapshot objects and segments only that stream's
/// unopened replica references.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_stream_past_the_limit_at_startup_keeps_its_snapshot_objects() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let record = |at: u64| Bytes::from(vec![(at % 251) as u8; 2048]);
    // With max_streams = 1 at restart, `a` opens `first` and skips `second`.
    let (first, second) = (StreamId(200), StreamId(201));
    let mut fences = Vec::new();
    for stream in [first, second] {
        journal.create(stream, [a, b, c], 1 << 30).await.unwrap();
        let sealed = journal
            .seal(stream, Epoch(0), Uuid::from_u128(9))
            .await
            .unwrap();
        fences.push(sealed.fence);
    }
    // Past a snapshot interval, `second`'s records are held only by its
    // snapshot objects and early WAL segments once its log is purged.
    for at in 1..=200 {
        journal
            .append(second, fences[1], Lsn(at), record(at))
            .await
            .unwrap();
    }
    let second_group = cluster.group(a, second).await;
    let second_genesis = second_group.genesis.clone();
    timeout(WAIT, async {
        while second_group.state.covered().is_none() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("second stream published a snapshot");
    // Roll and checkpoint the WAL past `second`'s early segments.
    for at in 1..=200 {
        journal
            .append(first, fences[0], Lsn(at), record(at))
            .await
            .unwrap();
    }
    drop(second_group);

    cluster.running.remove(&a).unwrap().stop().await;
    cluster.configs.get_mut(&a).unwrap().max_streams = 1;
    cluster.restart(a).await;
    let engine = cluster.running[&a].engine.clone();
    timeout(WAIT, async {
        while !engine.groups.lock().await.contains_key(&first) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("first stream opened at startup");
    assert!(!engine.groups.lock().await.contains_key(&second));

    tokio::time::sleep(Duration::from_millis(500)).await;
    for _ in 0..8 {
        engine.disk.reap_objects().await.unwrap();
    }

    // Free the slot, then open `second`.
    engine.park(first).await;
    let reopened = engine.group(second_genesis).await;
    assert!(
        reopened.is_ok(),
        "a stream skipped past the limit must open with its snapshot objects: {:?}",
        reopened.err()
    );
    let page = reopened
        .unwrap()
        .state
        .page(Lsn(1), 1)
        .await
        .expect("retained record 1 is still readable");
    assert_eq!(page.records, [(Lsn(1), record(1))]);
    cluster.stop_all().await;
}

/// A stream skipped past the stream limit at startup opens on a client's
/// request once a slot frees.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_client_request_opens_a_stream_past_the_limit_at_startup() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let (first, second) = (StreamId(202), StreamId(203));
    for stream in [first, second] {
        journal.create(stream, [a, b, c], 4096).await.unwrap();
        assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    }
    cluster.stop_all().await;
    for id in [a, b, c] {
        let config = cluster.configs.get_mut(&id).unwrap();
        config.max_streams = 1;
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    // `first` opens, then parks on every voter, freeing every voter's slot.
    timeout(Duration::from_secs(20), async {
        loop {
            let mut all_parked = true;
            for id in [a, b, c] {
                let engine = &cluster.running[&id].engine;
                if !engine.parked.read().contains(&first) || !engine.groups.lock().await.is_empty()
                {
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
    .expect("first stream parked on every voter");

    let client = cluster.client_within(&cluster.credentials, Duration::from_secs(4));
    assert_eq!(
        client.head(second).await,
        Ok(Lsn(0)),
        "a client request opens a stream skipped past the limit at startup"
    );
    cluster.stop_all().await;
}

/// Retiring a parked copy drops the state machine that pinned its objects
/// and segments, and its park mark.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn retiring_a_parked_copy_drops_its_closed_state_and_park_mark() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(211);
    journal.create(stream, [a, b, c], 4096).await.unwrap();
    let generation = journal.replica_generation(stream, c).await.unwrap();

    cluster.running.remove(&c).unwrap().stop().await;
    let current = journal.configuration(stream).await.unwrap();
    let moved = journal
        .replace(stream, current.revision, [a, b, d])
        .await
        .unwrap();
    assert_eq!(moved.voters, [a, b, d]);

    cluster.restart(c).await;
    let engine_c = cluster.running[&c].engine.clone();
    let _ = cluster.group(c, stream).await;
    engine_c.park(stream).await;
    assert!(engine_c.parked.read().contains(&stream));
    assert!(engine_c.closed_states.lock().contains_key(&stream));
    let pin = engine_c.closed_states.lock()[&stream].lifetime();

    let leader = cluster.leader(stream).await;
    journal
        .retire_copy(stream, c, leader, moved.revision, generation)
        .await
        .unwrap();

    assert!(!engine_c.parked.read().contains(&stream));
    assert!(!engine_c.closed_states.lock().contains_key(&stream));
    assert_eq!(
        pin.strong_count(),
        0,
        "the retired copy's objects and segments are no longer pinned"
    );
    cluster.stop_all().await;
}

/// Closing a deleted stream forgets its writer's leader preference.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn deleting_a_stream_forgets_its_preferred_leader() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(212);
    journal.create(stream, [a, b, c], 4096).await.unwrap();
    journal.prefer_leader(stream, b).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, b).await);
    assert!(
        cluster.running[&b]
            .engine
            .preferred
            .lock()
            .contains_key(&stream)
    );

    journal.delete(stream).await.unwrap();
    timeout(WAIT, async {
        while !cluster.running[&b].engine.deleted.read().contains(&stream) {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("deleted stream closed on b");
    assert!(
        !cluster.running[&b]
            .engine
            .preferred
            .lock()
            .contains_key(&stream)
    );
    cluster.stop_all().await;
}
