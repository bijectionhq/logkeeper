//! The replicated catalog: outages, races, compaction and migration.

use super::*;
use crate::stream::consensus::Voters;
use crate::stream::consensus::keeper::catalog_stream::{COMPACT_AFTER, STREAM};

/// What `keeper`'s catalog replica answers for `stream` once it has applied
/// the stream's entry.
async fn located(cluster: &Cluster, keeper: Uuid, stream: StreamId) -> (Genesis, Vec<Uuid>) {
    let engine = &cluster.running[&keeper].engine;
    timeout(WAIT, async {
        loop {
            if let Ok(Reply::Catalog(genesis, contacts)) =
                engine.serve_catalog_stream(Request::Locate(stream)).await
            {
                return (genesis, contacts);
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap()
}

/// Claims `genesis` on whichever running catalog voter leads.
async fn claim(cluster: &Cluster, genesis: &Genesis) -> Reply {
    timeout(WAIT, async {
        loop {
            for voter in cluster.catalog_voters.unwrap() {
                let Some(running) = cluster.running.get(&voter) else {
                    continue;
                };
                match running
                    .engine
                    .serve_catalog_stream(Request::Claim(genesis.clone()))
                    .await
                {
                    Ok(Reply::Leader(_))
                    | Ok(Reply::Decision(Outcome::Refused(JournalError::Unavailable)))
                    | Err(_) => (),
                    Ok(reply) => return reply,
                }
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap()
}

/// Waits until every catalog voter trimmed the catalog's first record.
async fn trimmed(cluster: &Cluster) {
    for voter in cluster.catalog_voters.unwrap() {
        let group = cluster.group(voter, STREAM).await;
        timeout(WAIT, async {
            while !matches!(
                group.state.page(Lsn(1), 1).await,
                Err(JournalError::Trimmed { .. })
            ) {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .expect("the catalog trimmed before its checkpoint");
    }
}

async fn check(cluster: &Cluster, claimed: &[Genesis]) {
    for voter in cluster.catalog_voters.unwrap() {
        for genesis in claimed {
            assert_eq!(&located(cluster, voter, genesis.stream).await.0, genesis);
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn without_a_catalog_quorum_creates_fail_and_existing_streams_serve() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let voters = cluster.catalog_voters.unwrap();
    let (second, third) = (voters[1], voters[2]);
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(81);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    let record = Bytes::from_static(b"record");
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(1), record.clone())
            .await,
        Ok(Lsn(1))
    );
    cluster.running.remove(&second).unwrap().stop().await;
    cluster.running.remove(&third).unwrap().stop().await;
    let quick = cluster.client_within(&cluster.credentials, Duration::from_secs(2));
    assert_eq!(
        quick
            .create(StreamId(82), Voters::from([a, b, d]), 4096)
            .await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(2), record.clone())
            .await,
        Ok(Lsn(2))
    );
    // A cold client finds the stream in the remaining voter's fold.
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(
        cold.claimed_voters(stream).await,
        Ok(Some(Voters::from([a, b, c])))
    );
    assert_eq!(cold.head(stream).await, Ok(Lsn(2)));
    cluster.restart(second).await;
    cluster.restart(third).await;
    journal
        .create(StreamId(82), Voters::from([a, b, d]), 4096)
        .await
        .unwrap();
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_live_catalog_grows_through_joint_consensus_and_reopens() {
    let initial = Voters::from([5, 6, 7].map(Uuid::from_u128));
    let expanded = Voters::from([5, 6, 7, 8, 9].map(Uuid::from_u128));
    let mut cluster = Cluster::start_addressed(["a", "b", "c", "d"], Some(initial), false, 2).await;
    let [a, b, c, _] = cluster.ids;
    let data = Voters::from([a, b, c]);
    let before = StreamId(123);
    let client = cluster.client(&cluster.credentials);
    client.create(before, data, 4096).await.unwrap();
    let original = client.configuration(STREAM).await.unwrap();
    assert_eq!(original.voters, initial);
    // Each keeper reports the catalog's live membership
    // (`logkeeper_consensus_catalog_voters`): three until it grows.
    assert_eq!(cluster.running[&a].engine.catalog_voter_count().await, 3);
    assert_eq!(
        client.replace(STREAM, original.revision, expanded).await,
        Err(JournalError::Unsupported),
    );
    cluster.finalize().await;
    let current = client
        .replace(STREAM, original.revision, expanded)
        .await
        .unwrap();
    assert_eq!(current.voters, expanded);
    for voter in expanded {
        let engine = &cluster.running[&voter].engine;
        timeout(WAIT, async {
            while engine.catalog_voter_count().await != 5 {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .expect("a grown catalog reports five voters, though configs name three");
    }
    assert_eq!(
        client.replace(STREAM, original.revision, expanded).await,
        Ok(current),
    );

    // Shut down two original voters and reopen the two added voters with the
    // original genesis configuration before admitting a new catalog write.
    for voter in [initial[0], initial[1], expanded[3], expanded[4]] {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    cluster.restart(expanded[3]).await;
    cluster.restart(expanded[4]).await;
    let cold = cluster.client(&cluster.credentials);
    let after = StreamId(124);
    cold.create(after, data, 4096).await.unwrap();
    assert_eq!(cold.claimed_voters(before).await, Ok(Some(data)));
    assert_eq!(cold.configuration(STREAM).await, Ok(current));
    assert_eq!(cold.claimed_voters(after).await, Ok(Some(data)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn five_voter_catalog_grants_leases_and_creates_after_two_voters_stop() {
    let voters = Voters::from([5, 6, 7, 8, 9].map(Uuid::from_u128));
    let mut cluster = Cluster::start_addressed(["a", "b", "c", "d"], Some(voters), false, 2).await;
    let data = Voters::from([cluster.ids[0], cluster.ids[1], cluster.ids[2]]);
    let existing = StreamId(120);
    let client = cluster.client(&cluster.credentials);
    client.create(existing, data, 4096).await.unwrap();
    cluster.finalize().await;
    for voter in voters {
        assert_eq!(located(&cluster, voter, existing).await.0.voters, data);
        let group = cluster.group(voter, STREAM).await;
        assert_eq!(group.genesis.voters, voters);
        assert_eq!(
            group
                .raft
                .metrics()
                .borrow_watched()
                .membership_config
                .membership()
                .voter_ids()
                .collect::<BTreeSet<_>>(),
            voters.into_iter().map(|id| id.as_u128()).collect(),
        );
    }

    // The original seeder need not be present after bootstrap.
    for voter in [cluster.catalog, voters[1]] {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    let fresh = StreamId(121);
    let cold = cluster.client(&cluster.credentials);
    cold.create(fresh, data, 4096).await.unwrap();
    assert_eq!(cold.claimed_voters(fresh).await, Ok(Some(data)));

    // The prior leases have now expired. The catalog must grant new ones
    // before these data voters can serve or accept writes again.
    let lease = Duration::from_millis(cluster.configs[&data[0]].lease_millis);
    tokio::time::sleep(lease).await;
    let sealed = cold
        .seal(fresh, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    assert_eq!(
        cold.append(fresh, sealed.fence, Lsn(1), Bytes::from_static(b"record"))
            .await,
        Ok(Lsn(1))
    );
    assert_eq!(cold.head(fresh).await, Ok(Lsn(1)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn five_voter_catalog_cannot_reseed_an_existing_replicated_catalog() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, _] = cluster.ids;
    let client = cluster.client(&cluster.credentials);
    client
        .create(StreamId(122), Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let changed = Voters::from([1, 2, 5, 6, 7].map(Uuid::from_u128));
    let genesis = Genesis {
        voters: changed,
        ..cluster.group(cluster.catalog, STREAM).await.genesis.clone()
    };
    let replica = &cluster.running[&a].engine;
    assert!(replica.disk.genesis(STREAM).is_none());
    let error = replica.group(genesis).await.err().unwrap();
    assert_eq!(
        error.to_string(),
        "catalog genesis does not match configuration"
    );
    assert!(replica.disk.genesis(STREAM).is_none());

    cluster.stop_all().await;
    let mut config = cluster.configs[&cluster.catalog].clone();
    config.catalog_voters = Some(changed);
    let error = config
        .prepare(CancellationToken::new())
        .await
        .err()
        .unwrap();
    assert_eq!(
        error.to_string(),
        "catalog configuration differs from durable genesis"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn one_lost_catalog_voter_leaves_creates_and_repair_and_is_replaced() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let second = cluster.catalog_voters.unwrap()[1];
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(StreamId(83), Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    cluster.running.remove(&second).unwrap().stop().await;
    let stream = StreamId(84);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let current = journal.configuration(stream).await.unwrap();
    let placed = journal
        .replace(stream, current.revision, Voters::from([a, b, d]))
        .await
        .unwrap();
    assert_eq!(placed.voters, [a, b, d]);
    assert_eq!(
        located(&cluster, cluster.catalog, stream).await.1[..3],
        [a, b, d]
    );
    // The catalog's own leader replaces the silent voter, as for any stream.
    let moved = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = journal.configuration(STREAM).await
                && !configuration.voters.contains(&second)
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the catalog leader replaced its silent voter");
    assert!(moved.revision > 0);
    journal
        .create(StreamId(85), Voters::from([b, c, d]), 4096)
        .await
        .unwrap();
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(
        cold.claimed_voters(StreamId(85)).await,
        Ok(Some(Voters::from([b, c, d])))
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_claims_of_one_stream_resolve_to_one_genesis() {
    let cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let first = cluster.client(&cluster.credentials);
    let second = cluster.client(&cluster.credentials);
    first
        .create(StreamId(86), Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let stream = StreamId(87);
    let (left, right) = tokio::join!(
        first.create(stream, Voters::from([a, b, c]), 4096),
        second.create(stream, Voters::from([a, b, d]), 4096)
    );
    let winner = match (left, right) {
        (Ok(()), Err(JournalError::Conflict { .. })) => [a, b, c],
        (Err(JournalError::Conflict { .. }), Ok(())) => [a, b, d],
        other => panic!("claims did not resolve to one genesis: {other:?}"),
    };
    for voter in cluster.catalog_voters.unwrap() {
        assert_eq!(located(&cluster, voter, stream).await.0.voters, winner);
    }
    assert_eq!(
        first.claimed_voters(stream).await,
        Ok(Some(winner)).map(|voters| voters.map(Voters::from))
    );
    assert_eq!(
        second.claimed_voters(stream).await,
        Ok(Some(winner)).map(|voters| voters.map(Voters::from))
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn compaction_keeps_lookups_across_a_checkpoint_trim_and_restart() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(StreamId(88), Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let rosters = [[a, b, c], [a, b, d], [a, c, d], [b, c, d]];
    let claimed = (0..3 * COMPACT_AFTER as u128)
        .map(|index| Genesis {
            stream: StreamId(1000 + index),
            voters: Voters::from(rosters[index as usize % 4]),
            quota_bytes: 4096,
            immutable: false,
        })
        .collect::<Vec<_>>();
    for genesis in &claimed {
        assert!(
            matches!(claim(&cluster, genesis).await, Reply::Catalog(found, _) if &found == genesis)
        );
    }
    trimmed(&cluster).await;
    check(&cluster, &claimed).await;
    let unknown = StreamId(5000);
    assert_eq!(journal.claimed_voters(unknown).await, Ok(None));

    cluster.stop_all().await;
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    trimmed(&cluster).await;
    check(&cluster, &claimed).await;
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(cold.claimed_voters(unknown).await, Ok(None));
    assert!(matches!(
        cold.create(claimed[0].stream, Voters::from([b, c, d]), 4096)
            .await,
        Err(JournalError::Conflict { .. })
    ));
    cold.create(claimed[0].stream, claimed[0].voters, 4096)
        .await
        .unwrap();
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_populated_single_catalog_migrates_into_the_replicated_catalog() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let (kept, moved, created) = (StreamId(90), StreamId(91), StreamId(92));
    journal
        .create(kept, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal
        .create(moved, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let current = journal.configuration(moved).await.unwrap();
    journal
        .replace(moved, current.revision, Voters::from([a, b, d]))
        .await
        .unwrap();
    cluster.stop_all().await;

    let voters = Voters::from([5, 6, 7].map(Uuid::from_u128));
    for config in cluster.configs.values_mut() {
        config.catalog_voters = Some(voters);
    }
    cluster.catalog_voters = Some(voters);
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(
        cold.claimed_voters(kept).await,
        Ok(Some(Voters::from([a, b, c])))
    );
    assert_eq!(
        cold.claimed_voters(moved).await,
        Ok(Some(Voters::from([a, b, c])))
    );
    assert_eq!(cold.head(moved).await, Ok(Lsn(0)));
    assert!(matches!(
        cold.create(kept, Voters::from([a, b, d]), 4096).await,
        Err(JournalError::Conflict { .. })
    ));
    cold.create(kept, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    cold.create(created, Voters::from([b, c, d]), 4096)
        .await
        .unwrap();
    for voter in voters {
        assert_eq!(located(&cluster, voter, kept).await.0.voters, [a, b, c]);
        // The imported stage still orders the moved stream's contacts.
        assert_eq!(located(&cluster, voter, moved).await.1[..3], [a, b, d]);
        assert_eq!(located(&cluster, voter, created).await.0.voters, [b, c, d]);
    }
    // The single-keeper catalog is only read, once.
    let legacy = &cluster.running[&cluster.catalog].engine.disk;
    assert!(legacy.catalog(kept).is_some());
    assert!(legacy.catalog(created).is_none());
    cluster.stop_all().await;
}

/// Clients and keepers find the replicated catalog after every one of its
/// configured voters was replaced.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_replicated_catalog_stays_reachable_after_its_voters_are_replaced() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let voters = cluster.catalog_voters.unwrap();
    let (c1, c2, c3) = (voters[0], voters[1], voters[2]);
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(210);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();

    // Replace all three original catalog voters one by one:
    // [5, 6, 7] -> [1, 6, 7] -> [1, 2, 7] -> [1, 2, 3].
    let mut current = journal.configuration(STREAM).await.unwrap();
    for next in [[a, c2, c3], [a, b, c3], [a, b, c]] {
        current = journal
            .replace(STREAM, current.revision, Voters::from(next))
            .await
            .unwrap();
    }
    assert_eq!(current.voters, [a, b, c]);

    // Retire the removed catalog copies on the three original catalog_voters.
    let authority = cluster
        .authority(STREAM, Voters::from([a, b, c]), current.revision)
        .await;
    for old in [c1, c2, c3] {
        if let Ok(generation) = journal.replica_generation(STREAM, old).await {
            journal
                .retire_copy(STREAM, old, authority, current.revision, generation)
                .await
                .unwrap();
        }
    }

    // A fresh client and a non-catalog keeper `d` can no longer reach the
    // healthy catalog quorum on [a, b, c].
    let cold = cluster.client_within(&cluster.credentials, Duration::from_secs(3));
    assert_eq!(
        cold.claimed_voters(stream).await,
        Ok(Some(Voters::from([a, b, c]))),
        "a cold client must still reach the replicated catalog after its original voters were replaced"
    );
    let reply = cluster.running[&d]
        .engine
        .ask_catalog_stream(Request::Locate(stream))
        .await
        .unwrap();
    assert!(
        matches!(reply, Reply::Catalog(genesis, _) if genesis.stream == stream),
        "non-catalog keeper must still reach the replicated catalog after voter replacement"
    );
    cluster.stop_all().await;
}
