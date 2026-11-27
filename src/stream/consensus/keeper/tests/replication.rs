//! Streams with five voters: creation behind the finalized version, writes
//! through the loss of two voters, repair, replacement, operator recovery
//! after losing three, and parking.

use super::*;
use crate::stream::consensus::{Configuration, ConsensusJournal, Voters, keeper::Recovery};

const FIVE_WAIT: Duration = Duration::from_secs(40);

/// Voters 1, 2, 3, 4 and 6, in domains a, b, c, d and e.
fn five(cluster: &Cluster) -> Voters {
    let [a, b, c, d] = cluster.ids;
    Voters::sorted(&[a, b, c, d, Uuid::from_u128(6)]).unwrap()
}

fn record(at: u64) -> Bytes {
    Bytes::from(format!("record-{at}"))
}

/// Creates `stream` on `voters`, seals it and appends records 1 to
/// `records`.
async fn written(journal: &Client, stream: StreamId, voters: Voters, records: u64) -> Fence {
    journal.create(stream, voters, 1 << 20).await.unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    for at in 1..=records {
        assert_eq!(
            journal
                .append(stream, sealed.fence, Lsn(at), record(at))
                .await,
            Ok(Lsn(at))
        );
    }
    sealed.fence
}

/// Waits until every keeper in `keepers` applied `head`.
async fn applied(cluster: &Cluster, stream: StreamId, keepers: &[Uuid], head: u64) {
    for id in keepers {
        let group = cluster.group(*id, stream).await;
        timeout(FIVE_WAIT, async {
            while group.state.head() != Ok(Lsn(head)) {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap_or_else(|_| panic!("{id} applied every record"));
    }
}

async fn reads_back(journal: &Client, stream: StreamId, head: u64) {
    let page = journal
        .read(stream, Lsn(1), head as usize + 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        (1..=head)
            .map(|at| (Lsn(at), record(at)))
            .collect::<Vec<_>>()
    );
}

/// Waits until the stream's configuration satisfies `done`.
async fn configured_until(
    journal: &Client,
    stream: StreamId,
    done: impl Fn(&Configuration) -> bool,
) -> Configuration {
    timeout(FIVE_WAIT, async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && done(&configuration)
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the stream reached the expected configuration")
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn five_voters_wait_for_the_finalized_version_then_replicate_to_all() {
    let cluster = Cluster::start().await;
    let journal = cluster.client(&cluster.credentials);
    let voters = five(&cluster);
    let stream = StreamId(0x501);
    // Before finalize an older keeper may still run, which cannot read a
    // five-voter roster.
    assert_eq!(
        journal.create(stream, voters, 1 << 20).await,
        Err(JournalError::Unsupported)
    );
    // Three voters need no finalize.
    let [a, b, c, _] = cluster.ids;
    written(&journal, StreamId(0x502), Voters::from([a, b, c]), 1).await;

    cluster.finalize().await;
    written(&journal, stream, voters, 8).await;
    let configuration = journal.configuration(stream).await.unwrap();
    assert_eq!(configuration.voters, voters);
    assert_eq!(configuration.voters.quorum(), 3);
    applied(&cluster, stream, &voters, 8).await;
    reads_back(&journal, stream, 8).await;
    // A cold client finds the five-voter genesis through the catalog.
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(cold.claimed_voters(stream).await, Ok(Some(voters)));
    reads_back(&cold, stream, 8).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn losing_two_of_five_keeps_writing_and_repair_replaces_both() {
    let mut cluster = Cluster::start().await;
    cluster.finalize().await;
    let journal = cluster.client(&cluster.credentials);
    let voters = five(&cluster);
    let stream = StreamId(0x503);
    let fence = written(&journal, stream, voters, 4).await;
    applied(&cluster, stream, &voters, 4).await;

    // Lose the leader and one follower at once: three voters remain, a
    // quorum, so the stream elects a leader and keeps committing.
    let leader = cluster.leader_after_head(&journal, stream).await;
    let follower = voters.iter().copied().find(|id| *id != leader).unwrap();
    for lost in [leader, follower] {
        cluster.running.remove(&lost).unwrap().stop().await;
    }
    for at in 5..=8 {
        assert_eq!(
            journal.append(stream, fence, Lsn(at), record(at)).await,
            Ok(Lsn(at))
        );
    }
    reads_back(&journal, stream, 8).await;

    // Repair replaces both lost voters, one at a time, with the spare
    // keepers 5 and 7, keeping three live voters throughout.
    let repaired = configured_until(&journal, stream, |configuration| {
        !configuration.voters.contains(&leader) && !configuration.voters.contains(&follower)
    })
    .await;
    assert_eq!(repaired.voters.len(), 5);
    assert!(repaired.voters.contains(&Uuid::from_u128(5)));
    assert!(repaired.voters.contains(&Uuid::from_u128(7)));
    assert!(
        cluster.running[&leader_of(&cluster, stream).await]
            .engine
            .placement
            .roster(&repaired.voters)
    );
    let running = repaired.voters.to_vec();
    applied(&cluster, stream, &running, 8).await;
    assert_eq!(
        journal.append(stream, fence, Lsn(9), record(9)).await,
        Ok(Lsn(9))
    );
    reads_back(&journal, stream, 9).await;
}

async fn leader_of(cluster: &Cluster, stream: StreamId) -> Uuid {
    let journal = cluster.client(&cluster.credentials);
    cluster.leader_after_head(&journal, stream).await
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_operator_replaces_one_of_five_and_never_two() {
    let cluster = Cluster::start().await;
    cluster.finalize().await;
    let journal = cluster.client(&cluster.credentials);
    let voters = five(&cluster);
    let stream = StreamId(0x504);
    let fence = written(&journal, stream, voters, 3).await;
    let current = journal.configuration(stream).await.unwrap();
    let [a, b, ..] = cluster.ids;
    let spare = Uuid::from_u128(7);

    // A move keeps the replication factor, and a five-voter move never keeps
    // just one or two voters, which would read as a recovery.
    let three = Voters::from([a, b, spare]).into_sorted();
    assert!(matches!(
        journal.replace(stream, current.revision, three).await,
        Err(JournalError::Conflict { .. })
    ));
    let next = voters.replacing(a, spare);
    let moved = journal
        .replace(stream, current.revision, next)
        .await
        .unwrap();
    assert_eq!(moved.voters, next);
    assert_eq!(moved.revision, current.revision + 1);
    applied(&cluster, stream, &next, 3).await;
    assert_eq!(
        journal.append(stream, fence, Lsn(4), record(4)).await,
        Ok(Lsn(4))
    );
    reads_back(&journal, stream, 4).await;
}

/// The acknowledgement of a recovery that names `lost`, with the
/// retirement proofs of `proven`.
fn acknowledging(lost: &[Uuid], proofs: &[super::super::FenceProof]) -> Recovery {
    Recovery {
        acknowledge_data_loss: true,
        lost: Some(lost.to_vec()),
        fence_proofs: proofs.to_vec(),
        ..Recovery::default()
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn losing_three_of_five_recovers_from_the_more_advanced_survivor() {
    use journal_contract::Journal;

    // Voters 1, 2, 3, 4, 6; spares 5, 7, 8 and 9.
    let mut cluster = Cluster::start_wide(2).await;
    cluster.finalize().await;
    let journal = cluster.client(&cluster.credentials);
    let voters = five(&cluster);
    let stream = StreamId(0x505);
    written(&journal, stream, voters, 5).await;
    applied(&cluster, stream, &voters, 5).await;
    let [low, high, ..] = cluster.ids;
    let lost = voters
        .iter()
        .copied()
        .filter(|id| *id != low && *id != high)
        .collect::<Vec<_>>();
    // Both survivors recorded the lost voters' media incarnations, which
    // their retirement proofs must match.
    for survivor in [low, high] {
        super::recovery::remember_peers(&cluster, survivor, [lost[0], lost[1]]).await;
        super::recovery::remember_peers(&cluster, survivor, [lost[1], lost[2]]).await;
    }
    for id in &lost {
        cluster.running.remove(id).unwrap().stop().await;
    }
    // The operator retires each lost keeper for good.
    let proofs = lost
        .iter()
        .map(|id| cluster.configs[id].fence_recovery(*id).unwrap())
        .collect::<Vec<_>>();

    // While four voters answer, nothing is recovered: refuse on a stopped
    // survivor when another healthy voter would still make a quorum with
    // it and the other survivor.
    cluster.running.remove(&high).unwrap().stop().await;
    // Both survivors applied the same log; the lower keeper ID is the more
    // advanced, so the higher one refuses and names it.
    let refused = cluster.configs[&high]
        .recover_stream(stream, acknowledging(&lost, &proofs))
        .await
        .unwrap_err();
    assert!(refused.to_string().contains(&low.to_string()), "{refused}");
    cluster.restart(high).await;
    cluster.running.remove(&low).unwrap().stop().await;
    // A surviving voter cannot be declared dead.
    let refused = cluster.configs[&low]
        .recover_stream(stream, acknowledging(&[high], &[]))
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("healthy replica"), "{refused}");
    let report = cluster.configs[&low]
        .recover_stream(stream, acknowledging(&lost, &proofs))
        .await
        .unwrap();
    assert!(report.written);
    assert_eq!(report.head, Lsn(5));
    assert_eq!(report.voters.len(), 5);
    assert!(report.voters.contains(&low) && report.voters.contains(&high));
    assert!(lost.iter().all(|id| !report.voters.contains(id)));
    let mut reported = report.lost.clone();
    reported.sort_unstable();
    assert_eq!(reported, lost);

    cluster.restart(low).await;
    let recovered = configured_until(&journal, stream, |configuration| {
        configuration.voters == report.voters
    })
    .await;
    assert_eq!(recovered.revision, report.revision);
    assert_eq!(
        journal
            .seal(stream, report.epoch, Uuid::from_u128(99))
            .await,
        Err(JournalError::Recovered { head: Lsn(5) })
    );
    let contract: &dyn Journal = &ConsensusJournal::new(
        &cluster.credentials,
        &crate::stream::consensus::JournalConfig {
            keepers: cluster.keepers.clone(),
            catalog: cluster.catalog,
            catalog_voters: None,
            voters: Some(report.voters),
            replication_factor: 5,
            placement: None,
            draining: Default::default(),
            retired: Default::default(),
            quota_bytes: 1 << 20,
            max_record_bytes: 1024,
            deadline_ms: 10_000,
            domain: None,
        },
    )
    .unwrap();
    assert_eq!(contract.acknowledge_recovery(stream).await, Ok(Lsn(5)));
    let epoch = Epoch(report.epoch.0 + 1);
    assert_eq!(contract.seal(stream, epoch).await, Ok(Lsn(5)));
    assert_eq!(
        contract.append(stream, epoch, Lsn(6), record(6)).await,
        Ok(Lsn(6))
    );
    reads_back(&journal, stream, 6).await;
    // The kept survivor and the three replacements hold the recovered log.
    applied(&cluster, stream, &report.voters, 6).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_idle_five_voter_stream_parks_and_reopens_for_a_write() {
    let mut cluster = Cluster::start().await;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    cluster.finalize().await;
    let journal = cluster.client(&cluster.credentials);
    let voters = five(&cluster);
    let stream = StreamId(0x506);
    let fence = written(&journal, stream, voters, 2).await;
    timeout(FIVE_WAIT, async {
        loop {
            let mut parked = true;
            for id in &voters {
                let engine = &cluster.running[id].engine;
                parked &= engine.parked.read().contains_key(&stream)
                    && !engine.groups.lock().await.contains_key(&stream);
            }
            if parked {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("every voter parked the idle five-voter stream");
    assert_eq!(
        journal.append(stream, fence, Lsn(3), record(3)).await,
        Ok(Lsn(3))
    );
    reads_back(&journal, stream, 3).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_immutable_five_voter_stream_takes_scoped_sessions_without_two_voters() {
    use journal_contract::{Journal, WriterSessionId};

    let mut cluster = Cluster::start().await;
    cluster.finalize().await;
    let voters = five(&cluster);
    let journal = ConsensusJournal::new(
        &cluster.credentials,
        &crate::stream::consensus::JournalConfig {
            keepers: cluster.keepers.clone(),
            catalog: cluster.catalog,
            catalog_voters: None,
            voters: Some(voters),
            replication_factor: 5,
            placement: None,
            draining: Default::default(),
            retired: Default::default(),
            quota_bytes: 1 << 20,
            max_record_bytes: 1024,
            deadline_ms: 10_000,
            domain: None,
        },
    )
    .unwrap();
    let stream = StreamId(0x507);
    journal.create_immutable(stream).await.unwrap();
    assert_eq!(journal.require_immutable(stream).await, Ok(()));
    let client = cluster.client(&cluster.credentials);
    assert_eq!(client.configuration(stream).await.unwrap().voters, voters);
    let seal = journal
        .seal_session(stream, Epoch(0), WriterSessionId(5))
        .await
        .unwrap();
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(1), vec![record(1), record(2)])
            .await,
        Ok(Lsn(2))
    );
    applied(&cluster, stream, &voters, 2).await;
    // Two voters down: the immutable history keeps committing.
    let [a, b, ..] = cluster.ids;
    for lost in [a, b] {
        cluster.running.remove(&lost).unwrap().stop().await;
    }
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(3), vec![record(3)])
            .await,
        Ok(Lsn(3))
    );
    reads_back(&client, stream, 3).await;
}
