//! Keeper liveness, the repair queue, waking parked streams and keeping the
//! writer's leader preference.

use super::*;
use crate::stream::consensus::Configuration;
use crate::stream::consensus::Voters;

/// A cluster whose streams park after 2 s idle.
async fn parking_cluster() -> Cluster {
    let mut cluster = Cluster::start().await;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    cluster
}

async fn parked_on(cluster: &Cluster, stream: StreamId, voters: &[Uuid]) -> bool {
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

async fn wait_parked(cluster: &Cluster, stream: StreamId, voters: &[Uuid]) {
    timeout(Duration::from_secs(20), async {
        while !parked_on(cluster, stream, voters).await {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("every voter parked the idle stream");
}

/// The configuration `keeper`'s copy of `stream` holds, open or parked,
/// read without a request that would reopen it.
async fn local_configuration(
    cluster: &Cluster,
    keeper: Uuid,
    stream: StreamId,
) -> Option<Configuration> {
    let engine = &cluster.running[&keeper].engine;
    if let Some(group) = engine.groups.lock().await.get(&stream) {
        return group.state.finalized();
    }
    engine
        .closed_states
        .lock()
        .get(&stream)
        .and_then(|closed| closed.finalized())
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_parked_stream_that_names_a_dead_keeper_wakes_and_is_repaired() {
    let mut cluster = parking_cluster().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let (lost, healthy) = (StreamId(120), StreamId(121));
    journal
        .create(lost, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal
        .create(healthy, Voters::from([a, b, d]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(lost).await.unwrap();
    assert_eq!(
        journal.configuration(healthy).await.unwrap().voters,
        [a, b, d]
    );
    wait_parked(&cluster, lost, &[a, b, c]).await;
    wait_parked(&cluster, healthy, &[a, b, d]).await;
    // One voter's keeper stops for good. No client touches either stream.
    cluster.running.remove(&c).unwrap().stop().await;
    let repaired = timeout(Duration::from_secs(30), async {
        loop {
            for id in [a, b] {
                if let Some(configuration) = local_configuration(&cluster, id, lost).await
                    && configuration.revision > initial.revision
                    && !configuration.voters.contains(&c)
                {
                    return configuration;
                }
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the parked stream woke and its leader replaced the dead voter");
    assert!(repaired.voters.contains(&a) && repaired.voters.contains(&b));
    // A parked stream whose voters all live stays parked.
    assert!(parked_on(&cluster, healthy, &[a, b, d]).await);
    assert_eq!(journal.head(lost).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn one_pass_repairs_many_streams_and_a_failing_repair_blocks_none() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let streams = (130..136).map(StreamId).collect::<Vec<_>>();
    for stream in &streams {
        journal
            .create(*stream, Voters::from([a, b, c]), 4096)
            .await
            .unwrap();
        assert_eq!(journal.head(*stream).await, Ok(Lsn(0)));
    }
    let initial = journal.configuration(streams[0]).await.unwrap().revision;
    // The first stream's repair fails on whichever keeper leads it.
    let stuck = streams[0];
    for id in [a, b] {
        cluster.running[&id]
            .engine
            .fail_repairs
            .write()
            .insert(stuck);
    }
    let started = Instant::now();
    cluster.running.remove(&c).unwrap().stop().await;
    let remaining = timeout(Duration::from_secs(30), async {
        loop {
            let mut remaining = Vec::new();
            for stream in &streams[1..] {
                match journal.configuration(*stream).await {
                    Ok(configuration)
                        if configuration.revision > initial
                            && !configuration.voters.contains(&c) => {}
                    _ => remaining.push(*stream),
                }
            }
            if remaining.is_empty() {
                return started.elapsed();
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("every stream but the stuck one was repaired");
    eprintln!("five streams repaired {remaining:?} after their voter stopped");
    // The voter is silent for 2 s before repair starts. Four repairs then
    // run at once and the fifth starts in the next 500 ms pass; one repair
    // per pass would need at least five passes behind one another.
    assert!(remaining < Duration::from_secs(12), "{remaining:?}");
    assert!(
        journal
            .configuration(stuck)
            .await
            .unwrap()
            .voters
            .contains(&c)
    );
    // The stuck stream is retried, but backs off instead of every pass.
    tokio::time::sleep(Duration::from_secs(3)).await;
    let attempts = [a, b]
        .map(|id| {
            cluster.running[&id]
                .engine
                .repair_attempts
                .lock()
                .get(&stuck)
                .copied()
                .unwrap_or(0)
        })
        .iter()
        .sum::<u32>();
    let passes = (started.elapsed().as_millis() / 500) as u32;
    assert!(
        (1..passes / 2).contains(&attempts),
        "{attempts} of {passes}"
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn leadership_returns_to_the_preferred_voter_after_it_restarts() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(140);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let target = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    journal.prefer_leader(stream, target).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, target).await);
    // Every voter keeps the writer's domain.
    let domain = cluster.configs[&target].domains[&target].clone();
    for id in [a, b, c] {
        assert_eq!(
            cluster.running[&id].engine.preferred.lock().get(&stream),
            Some(&domain)
        );
    }
    // The preferred keeper restarts: a graceful stop hands leadership to
    // another voter, and the leader pass hands it back after the hold-down
    // without a new preference or seal.
    cluster.running.remove(&target).unwrap().stop().await;
    let away = timeout(WAIT, async {
        loop {
            for id in [a, b, c].into_iter().filter(|id| *id != target) {
                if let Some(group) = cluster.running[&id].engine.groups.lock().await.get(&stream)
                    && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
                {
                    return id;
                }
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap();
    assert_ne!(away, target);
    cluster.restart(target).await;
    assert!(wait_for_leader(&cluster, stream, target).await);
    // An election on another voter also comes back.
    let other = [a, b, c].into_iter().find(|id| *id != target).unwrap();
    tokio::time::sleep(LEADER_HOLD_DOWN).await;
    let group = cluster.group(target, stream).await;
    let _ = group.raft.trigger().transfer_leader(other.as_u128()).await;
    assert!(wait_for_leader(&cluster, stream, other).await);
    assert!(wait_for_leader(&cluster, stream, target).await);
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_parked_stream_answers_within_an_election_timeout_and_parks_past_a_dead_follower() {
    let mut cluster = parking_cluster().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(150);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();
    let mut slowest = Duration::ZERO;
    for _ in 0..3 {
        let leader = cluster.leader(stream).await;
        let term = cluster
            .group(leader, stream)
            .await
            .raft
            .metrics()
            .borrow_watched()
            .current_term;
        let metrics = cluster.running[&leader].engine.disk.metrics.clone();
        let campaigns = metrics.wake_campaigns.load(Ordering::Relaxed);
        wait_parked(&cluster, stream, &[a, b, c]).await;
        // The voter that led before parking campaigns as soon as it
        // reopens, so the first request does not wait out an election
        // timeout (450 to 900 ms). Checked as steps, not time, so a loaded
        // machine cannot fail it: the former leader started a wake campaign
        // and the stream is led again after exactly one election, by it.
        let started = Instant::now();
        assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
        slowest = slowest.max(started.elapsed());
        assert_eq!(
            metrics.wake_campaigns.load(Ordering::Relaxed),
            campaigns + 1,
            "the former leader campaigned on waking"
        );
        let led = cluster
            .group(leader, stream)
            .await
            .raft
            .metrics()
            .borrow_watched()
            .clone();
        assert_eq!(led.current_leader, Some(leader.as_u128()));
        assert_eq!(led.current_term, term + 1, "one election woke the stream");
    }
    eprintln!("slowest first head on a parked stream: {slowest:?}");

    // A stream whose follower's keeper is dead still parks. Its repair is
    // made to fail so it stays on the dead keeper.
    let lonely = StreamId(151);
    journal
        .create(lonely, Voters::from([a, b, d]), 4096)
        .await
        .unwrap();
    journal.prefer_leader(lonely, a).await.unwrap();
    assert!(wait_for_leader(&cluster, lonely, a).await);
    for id in [a, b] {
        cluster.running[&id]
            .engine
            .fail_repairs
            .write()
            .insert(lonely);
    }
    cluster.running.remove(&d).unwrap().stop().await;
    wait_parked(&cluster, lonely, &[a, b]).await;
    cluster.stop_all().await;
}
