//! Stream copies that are not open: past the stream limit at startup,
//! retired while parked, and deleted.

use super::*;

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_restarted_voter_learns_deletion_from_closed_tombstones() {
    let mut cluster = Cluster::start().await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let stream = StreamId(223);
    let client = cluster.client(&cluster.credentials);
    client.create(stream, voters, 4096).await.unwrap();
    let leader = cluster.leader_after_head(&client, stream).await;
    let victim = voters.into_iter().find(|id| *id != leader).unwrap();
    let follower = cluster.group(victim, stream).await;
    assert!(follower.state.covered().is_none());
    follower.state.pause_snapshots(true);
    client.delete(stream).await.unwrap();
    timeout(WAIT, async {
        while !voters
            .iter()
            .filter(|&&id| id != victim)
            .all(|id| cluster.running[id].engine.deleted.read().contains(&stream))
        {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the other voters retain terminal snapshots and close");
    let stopped = cluster.running.remove(&victim).unwrap();
    stopped.engine.crash.store(true, Ordering::Release);
    drop(follower);
    stopped.stop().await;

    cluster.restart(victim).await;
    timeout(WAIT, async {
        let engine = &cluster.running[&victim].engine;
        loop {
            if engine.deleted.read().contains(&stream)
                || engine
                    .groups
                    .lock()
                    .await
                    .get(&stream)
                    .is_some_and(|group| group.state.is_deleted())
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the restarted voter learns the committed deletion");
    assert_eq!(client.head(stream).await, Err(JournalError::Deleted));
    cluster.stop_all().await;
}

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
                if !engine.parked.read().contains_key(&first)
                    || !engine.groups.lock().await.is_empty()
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
    assert!(engine_c.parked.read().contains_key(&stream));
    assert!(engine_c.closed_states.lock().contains_key(&stream));
    let pin = engine_c.closed_states.lock()[&stream].lifetime();

    let leader = cluster.leader(stream).await;
    journal
        .retire_copy(stream, c, leader, moved.revision, generation)
        .await
        .unwrap();

    assert!(!engine_c.parked.read().contains_key(&stream));
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
    let engine = &cluster.running[&b].engine;
    timeout(WAIT, async {
        while !engine.deleted.read().contains(&stream)
            || engine.preferred.lock().contains_key(&stream)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("deleted stream closed and released its leader preference on b");
    cluster.stop_all().await;
}

async fn parked_everywhere(cluster: &Cluster, stream: StreamId, voters: &[Uuid]) -> bool {
    for id in voters {
        let engine = &cluster.running[id].engine;
        if !engine.parked.read().contains_key(&stream)
            || engine.groups.lock().await.contains_key(&stream)
        {
            return false;
        }
    }
    true
}

/// A parked stream stays parked across a restart of every voter, with only
/// the pins its durable mark names, and reopens with its records on the
/// first request. A mark left from before a later snapshot is ignored.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_parked_stream_stays_parked_across_a_restart_and_opens_lazily() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    // Park marks are a format N-1 cannot read.
    cluster.finalize().await;
    let journal = cluster.client(&cluster.credentials);
    let record = |at: u64| Bytes::from(vec![(at % 251) as u8; 2048]);
    let (parked, busy) = (StreamId(220), StreamId(221));
    let mut fences = Vec::new();
    for stream in [parked, busy] {
        journal.create(stream, [a, b, c], 1 << 30).await.unwrap();
        let sealed = journal
            .seal(stream, Epoch(0), Uuid::from_u128(9))
            .await
            .unwrap();
        fences.push(sealed.fence);
    }
    for at in 1..=200 {
        journal
            .append(parked, fences[0], Lsn(at), record(at))
            .await
            .unwrap();
    }
    timeout(Duration::from_secs(40), async {
        while !parked_everywhere(&cluster, parked, &[a, b, c]).await {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the idle stream parked on every voter");
    let generation = cluster.running[&a]
        .engine
        .disk
        .current_generation(parked)
        .unwrap();
    let directory = |id: Uuid| {
        crate::stream::consensus::ownership::directory(
            &cluster.running[&id].engine.disk.path,
            parked,
            generation,
        )
    };
    let mark = directory(a).join("parked");
    assert!(mark.exists(), "parking wrote a durable mark");
    let early = std::fs::read(&mark).unwrap();

    for id in [a, b, c] {
        cluster.running.remove(&id).unwrap().stop().await;
        let inspection = cluster.configs[&id].inspect(Some(parked)).unwrap();
        assert!(inspection.streams[0].parked);
        cluster.restart(id).await;
    }
    // Roll and checkpoint segments while the parked copies stay closed and
    // the reaper runs.
    for at in 1..=200 {
        let _ = journal.append(busy, fences[1], Lsn(at), record(at)).await;
    }
    for id in [a, b, c] {
        let engine = cluster.running[&id].engine.clone();
        assert!(engine.parked.read().contains_key(&parked), "still parked");
        assert!(!engine.groups.lock().await.contains_key(&parked));
        assert!(matches!(
            engine.closed_states.lock().get(&parked),
            Some(super::Closed::Pinned(pin)) if pin.segments().count() > 0
        ));
        for _ in 0..8 {
            engine.disk.reap_objects().await.unwrap();
        }
    }
    let page = timeout(WAIT, async {
        loop {
            match journal.read(parked, Lsn(1), 1, Duration::ZERO).await {
                Ok(page) => return page,
                Err(_) => tokio::time::sleep(Duration::from_millis(50)).await,
            }
        }
    })
    .await
    .unwrap();
    assert_eq!(page.records, [(Lsn(1), record(1))]);
    timeout(WAIT, async {
        while mark.exists() {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("reopening removed the mark");

    // A newer snapshot makes the early mark stale, as if a crash had kept
    // it: the restarted keeper ignores it and opens the stream.
    for at in 201..=400 {
        journal
            .append(parked, fences[0], Lsn(at), record(at))
            .await
            .unwrap();
    }
    let group = cluster.group(a, parked).await;
    timeout(WAIT, async {
        while group
            .state
            .covered()
            .is_none_or(|covered| covered.index < 300)
        {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("a later snapshot was published");
    drop(group);
    cluster.running.remove(&a).unwrap().stop().await;
    std::fs::write(&mark, early).unwrap();
    cluster.restart(a).await;
    let _ = cluster.group(a, parked).await;
    let engine = cluster.running[&a].engine.clone();
    assert!(!engine.parked.read().contains_key(&parked));
    assert!(
        !mark.exists(),
        "the stale mark was removed when the copy opened"
    );
    cluster.stop_all().await;
}

/// At its stream limit a keeper closes its least recently used idle copy
/// to open another, instead of refusing it.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_keeper_at_its_limit_evicts_its_least_recently_used_idle_copy() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 600;
    }
    cluster.configs.get_mut(&a).unwrap().max_streams = 2;
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    let streams = [StreamId(222), StreamId(223), StreamId(224)];
    for stream in &streams[..2] {
        journal.create(*stream, [a, b, c], 4096).await.unwrap();
        assert_eq!(journal.head(*stream).await, Ok(Lsn(0)));
    }
    // `a` follows the first and leads the second, which looks idle longer:
    // a followed copy goes first even when it was used more recently.
    // Leadership is placed rather than read as found, so it cannot move
    // between the check and the eviction.
    journal.prefer_leader(streams[0], b).await.unwrap();
    journal.prefer_leader(streams[1], a).await.unwrap();
    assert!(wait_for_leader(&cluster, streams[0], b).await);
    assert!(wait_for_leader(&cluster, streams[1], a).await);
    let engine = cluster.running[&a].engine.clone();
    let first = cluster.group(a, streams[0]).await;
    let second = cluster.group(a, streams[1]).await;
    // Both look idle for longer than the eviction delay, the second longer.
    for (group, idle) in [(&first, 31), (&second, 32)] {
        let since = Instant::now() - Duration::from_secs(idle);
        *group.used.lock() = since;
        if let Some(entry) = engine.activity.lock().get_mut(&group.genesis.stream) {
            entry.1 = since;
        }
    }
    let expected = streams[0];
    drop((first, second));
    journal.create(streams[2], [a, b, c], 4096).await.unwrap();
    assert_eq!(journal.head(streams[2]).await, Ok(Lsn(0)));
    let open = engine
        .groups
        .lock()
        .await
        .keys()
        .copied()
        .collect::<Vec<_>>();
    assert!(open.contains(&streams[2]), "{open:?}");
    assert!(!open.contains(&expected), "{open:?} kept {expected:?}");
    // A peer can start reopening the evicted copy after the group snapshot
    // above. The counter records the eviction even if its park mark changes.
    assert!(engine.disk.metrics.evicted.load(Ordering::Relaxed) > 0);
    // The evicted copy still serves: a request reopens it, evicting again.
    assert_eq!(journal.head(expected).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}
