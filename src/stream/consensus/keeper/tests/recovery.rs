//! Operator recovery of a stream that lost two of its three voters.

use super::*;
use crate::stream::consensus::{Configuration, ConsensusJournal, JournalConfig, keeper::Recovery};

const RECOVERY_WAIT: Duration = Duration::from_secs(30);

/// Creates `stream` on `voters`, seals it and appends `records` records,
/// then waits until `survivor` has applied all of them.
async fn written_stream(
    cluster: &Cluster,
    stream: StreamId,
    voters: [Uuid; 3],
    survivor: Uuid,
    records: u64,
) -> Fence {
    let journal = cluster.client(&cluster.credentials);
    journal.create(stream, voters, 1 << 20).await.unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    for at in 1..=records {
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
    let group = cluster.group(survivor, stream).await;
    timeout(WAIT, async {
        while group.state.head() != Ok(Lsn(records)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("the survivor applied every record");
    sealed.fence
}

fn acknowledged() -> Recovery {
    Recovery {
        acknowledge_data_loss: true,
        ..Recovery::default()
    }
}

fn contract_journal(
    cluster: &Cluster,
    credentials: &Credentials,
    voters: [Uuid; 3],
) -> ConsensusJournal {
    ConsensusJournal::new(
        credentials,
        &JournalConfig {
            keepers: cluster.keepers.clone(),
            catalog: cluster.catalog,
            catalog_voters: None,
            voters: Some(voters),
            placement: None,
            draining: Default::default(),
            quota_bytes: 1 << 20,
            max_record_bytes: 1024,
            deadline_ms: 10_000,
            domain: None,
        },
    )
    .unwrap()
}

/// Waits until the stream's leader reports `voters` as its configuration.
async fn configured(journal: &Client, stream: StreamId, voters: [Uuid; 3]) -> Configuration {
    timeout(RECOVERY_WAIT, async {
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_survivor_recovers_its_stream_and_the_lost_voters_retire() {
    use journal_contract::Journal;

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(81);
    let old_fence = written_stream(&cluster, stream, [a, b, c], a, 5).await;
    let journal = cluster.client(&cluster.credentials);
    let generation = journal.replica_generation(stream, b).await.unwrap();
    for lost in [b, c] {
        cluster.running.remove(&lost).unwrap().stop().await;
    }
    cluster.running.remove(&a).unwrap().stop().await;

    // Without the acknowledgement nothing is written.
    let refused = cluster.configs[&a]
        .recover_stream(stream, Recovery::default())
        .await
        .unwrap_err();
    assert!(
        refused.to_string().contains("--acknowledge-data-loss"),
        "{refused}"
    );
    let report = cluster.configs[&a]
        .recover_stream(stream, acknowledged())
        .await
        .unwrap();
    assert!(report.written);
    assert_eq!(report.head, Lsn(5));
    assert_eq!(report.epoch, Epoch(2));
    assert!(report.voters.contains(&a));
    assert!(!report.voters.contains(&b) && !report.voters.contains(&c));
    let mut lost = [b, c];
    lost.sort_unstable();
    assert_eq!(report.lost, lost);
    // A second run finds the recovery already written.
    let again = cluster.configs[&a]
        .recover_stream(stream, acknowledged())
        .await
        .unwrap();
    assert!(!again.written);
    assert_eq!(again.voters, report.voters);

    cluster.restart(a).await;
    let configuration = configured(&journal, stream, report.voters).await;
    assert_eq!(configuration.revision, report.revision);
    assert_eq!(journal.head(stream).await, Ok(Lsn(5)));
    let page = journal
        .read(stream, Lsn(1), 10, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        (1..=5)
            .map(|at| (Lsn(at), Bytes::from(format!("record-{at}"))))
            .collect::<Vec<_>>()
    );

    // The recovery fence refuses the old writer and every ordinary seal.
    assert_eq!(
        journal
            .append(stream, old_fence, Lsn(6), Bytes::from_static(b"late"))
            .await,
        Err(JournalError::Fenced { current: Epoch(2) })
    );
    assert_eq!(
        journal.seal(stream, Epoch(2), Uuid::from_u128(99)).await,
        Err(JournalError::Recovered { head: Lsn(5) })
    );
    let contract = contract_journal(&cluster, &cluster.credentials, report.voters);
    assert_eq!(
        contract.seal(stream, Epoch(3)).await,
        Err(JournalError::Recovered { head: Lsn(5) })
    );
    // A writer acknowledges the recovery through the generic journal
    // contract, so a consumer can resume without an administrator.
    let other = contract_journal(&cluster, &cluster.other, report.voters);
    let generic: &dyn journal_contract::Journal = &other;
    assert_eq!(generic.acknowledge_recovery(stream).await, Ok(Lsn(5)));
    assert_eq!(generic.acknowledge_recovery(stream).await, Ok(Lsn(5)));
    assert_eq!(contract.acknowledge_recovery(stream).await, Ok(Lsn(5)));
    assert_eq!(contract.seal(stream, Epoch(3)).await, Ok(Lsn(5)));
    assert_eq!(
        contract
            .append(stream, Epoch(3), Lsn(6), Bytes::from_static(b"after"))
            .await,
        Ok(Lsn(6))
    );
    assert_eq!(contract.head(stream).await, Ok(Lsn(6)));

    // A lost voter that returns cannot lead or disturb the stream, and
    // retires its copy once the certified placement excludes it.
    cluster.restart(b).await;
    let led = AtomicBool::new(false);
    let retired = timeout(RECOVERY_WAIT, async {
        loop {
            if let Some(group) = cluster.running[&b].engine.groups.lock().await.get(&stream)
                && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
            {
                led.store(true, Ordering::Relaxed);
            }
            if journal.replica_generation(stream, b).await != Ok(generation) {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await;
    assert!(retired.is_ok(), "the returning voter retired its copy");
    assert!(
        !led.load(Ordering::Relaxed),
        "the returning voter never led"
    );
    assert_eq!(
        journal
            .configuration(stream)
            .await
            .map(|current| current.voters),
        Ok(report.voters)
    );
    assert_eq!(
        contract
            .append(stream, Epoch(3), Lsn(7), Bytes::from_static(b"still"))
            .await,
        Ok(Lsn(7))
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn recovery_is_refused_while_another_voter_holds_a_healthy_replica() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let stream = StreamId(82);
    written_stream(&cluster, stream, [a, b, c], a, 2).await;
    cluster.running.remove(&a).unwrap().stop().await;
    // Both other voters are alive: the stream has a quorum.
    let refused = cluster.configs[&a]
        .recover_stream(stream, acknowledged())
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("quorum"), "{refused}");
    // One other voter is enough to keep a quorum with the survivor.
    cluster.running.remove(&b).unwrap().stop().await;
    let refused = cluster.configs[&a]
        .recover_stream(stream, acknowledged())
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("quorum"), "{refused}");
    // Named replacements must be live keepers outside the lost roster.
    cluster.running.remove(&c).unwrap().stop().await;
    let mut named = acknowledged();
    named.with = Some([b, d]);
    assert!(
        cluster.configs[&a]
            .recover_stream(stream, named)
            .await
            .is_err()
    );
    // Nothing was written: the survivor and a returning voter still serve
    // the original configuration.
    cluster.restart(a).await;
    cluster.restart(c).await;
    let journal = cluster.client(&cluster.credentials);
    assert_eq!(
        configured(&journal, stream, [a, b, c]).await.voters,
        [a, b, c]
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_recovery_write_is_all_or_nothing_across_a_crash() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let stream = StreamId(83);
    written_stream(&cluster, stream, [a, b, c], a, 3).await;
    let journal = cluster.client(&cluster.credentials);
    let mut generations = BTreeMap::new();
    for lost in [b, c] {
        generations.insert(
            lost,
            journal.replica_generation(stream, lost).await.unwrap(),
        );
    }
    for keeper in [b, c, a] {
        cluster.running.remove(&keeper).unwrap().stop().await;
    }
    let with = Some([d, Uuid::from_u128(6)]);
    let mut expected = [a, d, Uuid::from_u128(6)];
    expected.sort_unstable();
    // A crash before the round's boundary leaves no trace of it.
    let mut before = acknowledged();
    before.with = with;
    before.interrupt = Some(2);
    assert!(
        cluster.configs[&a]
            .recover_stream(stream, before)
            .await
            .is_err()
    );
    // A crash after the boundary leaves the whole recovery durable.
    let mut after = acknowledged();
    after.with = with;
    after.interrupt = Some(3);
    assert!(
        cluster.configs[&a]
            .recover_stream(stream, after)
            .await
            .is_err()
    );
    let report = cluster.configs[&a]
        .recover_stream(stream, acknowledged())
        .await
        .unwrap();
    assert!(!report.written, "the interrupted round was durable");
    assert_eq!(report.voters, expected);
    assert_eq!(report.head, Lsn(3));
    cluster.restart(a).await;
    configured(&journal, stream, expected).await;
    assert_eq!(journal.head(stream).await, Ok(Lsn(3)));
    assert_eq!(
        journal.seal(stream, Epoch(2), Uuid::from_u128(5)).await,
        Err(JournalError::Recovered { head: Lsn(3) })
    );
    assert_eq!(journal.acknowledge_recovery(stream).await, Ok(Lsn(3)));
    let sealed = journal
        .seal(stream, Epoch(2), Uuid::from_u128(5))
        .await
        .unwrap();
    assert_eq!(sealed.head, Lsn(3));

    // Both lost voters return together. They form a quorum of the lost
    // configuration, but the recovered voters refuse them without teaching
    // them the recovered term, and each retires its copy on contact.
    cluster.restart(b).await;
    cluster.restart(c).await;
    timeout(RECOVERY_WAIT, async {
        for (lost, generation) in &generations {
            while journal.replica_generation(stream, *lost).await == Ok(*generation) {
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        }
    })
    .await
    .expect("both returning voters retired their copies");
    assert_eq!(
        journal
            .configuration(stream)
            .await
            .map(|current| current.voters),
        Ok(expected)
    );
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(4), Bytes::from_static(b"four"))
            .await,
        Ok(Lsn(4))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(4)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_administrator_that_is_not_a_writer_cannot_write() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.writers = vec![OWNER.into()];
        config.administrators = vec![OWNER.into(), OTHER.into()];
        config.readers = vec![OWNER.into(), OTHER.into()];
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let owner = cluster.client(&cluster.credentials);
    let stream = StreamId(84);
    owner.create(stream, [a, b, c], 4096).await.unwrap();
    let sealed = owner
        .seal(stream, Epoch(0), Uuid::from_u128(5))
        .await
        .unwrap();

    let admin = cluster.client_within(&cluster.other, Duration::from_secs(3));
    assert!(
        admin
            .seal(stream, Epoch(1), Uuid::from_u128(77))
            .await
            .is_err()
    );
    assert!(
        admin
            .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"no"))
            .await
            .is_err()
    );
    assert!(admin.trim(stream, sealed.fence, Lsn(1)).await.is_err());
    assert_eq!(owner.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}
