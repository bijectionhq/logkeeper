//! The journal-contract conformance suite against real consensus keepers.
#![cfg(feature = "consensus-testing")]

use std::sync::Arc;

use journal_contract::{Journal, conformance};
use logkeeper::stream::consensus::testing::LocalCluster;

const PRINCIPALS: [&str; 3] = [
    "urn:logkeeper:client:1",
    "urn:logkeeper:client:2",
    "urn:logkeeper:client:3",
];

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_journal_satisfies_the_contract() {
    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(
        conformance::LIMITS.stream_quota_bytes,
        conformance::LIMITS.max_record_bytes,
    );
    let journals = PRINCIPALS.map(|principal| cluster.journal(principal, &config).unwrap());
    conformance::run(|identity| {
        let index = PRINCIPALS
            .iter()
            .position(|principal| identity.as_str() == *principal)
            .expect("conformance identity has a principal");
        Arc::new(journals[index].clone()) as Arc<dyn Journal>
    })
    .await;
    cluster.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn contract_state_survives_a_full_keeper_restart() {
    use bytes::Bytes;
    use journal_contract::{Epoch, JournalError, Lsn, StreamId};

    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let owner = cluster.journal(PRINCIPALS[0], &config).unwrap();
    let other = cluster.journal(PRINCIPALS[1], &config).unwrap();
    let stream = StreamId(77);
    owner.create(stream).await.unwrap();
    // A seal may jump ahead of the stream's current epoch.
    assert_eq!(owner.seal(stream, Epoch(3)).await, Ok(Lsn(0)));
    let records = (1..=5)
        .map(|at| (Lsn(at), Bytes::from(format!("record {at}"))))
        .collect();
    assert_eq!(
        owner.append_batch(stream, Epoch(3), records).await,
        Ok(Lsn(5))
    );
    assert_eq!(
        other.seal(stream, Epoch(3)).await,
        Err(JournalError::Fenced { current: Epoch(3) })
    );

    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    assert_eq!(owner.head(stream).await, Ok(Lsn(5)));
    // The same principal reseals its epoch after the restart.
    assert_eq!(owner.seal(stream, Epoch(3)).await, Ok(Lsn(5)));
    assert_eq!(
        owner
            .append(stream, Epoch(3), Lsn(6), Bytes::from_static(b"after"))
            .await,
        Ok(Lsn(6))
    );
    // A later epoch by another principal fences the owner.
    assert_eq!(other.seal(stream, Epoch(4)).await, Ok(Lsn(6)));
    assert_eq!(
        owner
            .append(stream, Epoch(3), Lsn(7), Bytes::from_static(b"stale"))
            .await,
        Err(JournalError::Fenced { current: Epoch(4) })
    );
    let page = other
        .read(stream, Lsn(1), 16, std::time::Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.head, Lsn(6));
    cluster.shutdown().await.unwrap();
}

fn batch_record(at: u64) -> bytes::Bytes {
    // Varied lengths, including empty records, exercise every extent offset.
    bytes::Bytes::from(vec![(at % 251) as u8; (at as usize * 37) % 900])
}

async fn read_all(
    journal: &logkeeper::stream::consensus::ConsensusJournal,
    stream: journal_contract::StreamId,
    through: u64,
) -> Vec<(journal_contract::Lsn, bytes::Bytes)> {
    let mut records = Vec::new();
    let mut from = journal_contract::Lsn(1);
    while from.0 <= through {
        let page = journal
            .read(stream, from, 512, std::time::Duration::ZERO)
            .await
            .unwrap();
        assert!(!page.records.is_empty(), "read stalled at {from:?}");
        from = journal_contract::Lsn(page.records.last().unwrap().0.0 + 1);
        records.extend(page.records);
    }
    records
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn batches_commit_atomically_and_survive_restart_and_replacement() {
    use journal_contract::{Epoch, JournalError, Lsn, StreamId};

    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    let stream = StreamId(78);
    journal.create(stream).await.unwrap();
    assert_eq!(journal.seal(stream, Epoch(1)).await, Ok(Lsn(0)));

    // 300 records span two keeper batches.
    let group = |from: u64, to: u64| {
        (from..=to)
            .map(|at| (Lsn(at), batch_record(at)))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        journal.append_batch(stream, Epoch(1), group(1, 300)).await,
        Ok(Lsn(300))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(300)));
    assert_eq!(read_all(&journal, stream, 300).await, group(1, 300));

    // An identical retry, including a retained prefix, returns the head.
    assert_eq!(
        journal
            .append_batch(stream, Epoch(1), group(201, 300))
            .await,
        Ok(Lsn(300))
    );
    // Overlapping changed bytes, a gap and an over-quota group are refused
    // whole, leaving the head unchanged.
    let mut changed = group(299, 302);
    changed[0].1 = bytes::Bytes::from_static(b"different");
    assert!(matches!(
        journal.append_batch(stream, Epoch(1), changed).await,
        Err(JournalError::Conflict { .. })
    ));
    assert!(matches!(
        journal
            .append_batch(stream, Epoch(1), group(302, 303))
            .await,
        Err(JournalError::Conflict { .. })
    ));
    // Ten 4,000-byte records exceed a 16,000-byte quota, so the whole
    // batch is refused and no record of it commits.
    let tight = StreamId(79);
    let tight_config = cluster.journal_config(16_000, 4096);
    let tight_journal = cluster.journal(PRINCIPALS[0], &tight_config).unwrap();
    tight_journal.create(tight).await.unwrap();
    tight_journal.seal(tight, Epoch(1)).await.unwrap();
    let oversized = (1..=10)
        .map(|at| (Lsn(at), bytes::Bytes::from(vec![1; 4000])))
        .collect::<Vec<_>>();
    assert!(matches!(
        tight_journal.append_batch(tight, Epoch(1), oversized).await,
        Err(JournalError::Full { .. })
    ));
    assert_eq!(tight_journal.head(tight).await, Ok(Lsn(0)));
    // A stale epoch cannot append a batch.
    let other = cluster.journal(PRINCIPALS[1], &config).unwrap();
    assert_eq!(other.seal(stream, Epoch(2)).await, Ok(Lsn(300)));
    assert_eq!(
        journal
            .append_batch(stream, Epoch(1), group(301, 302))
            .await,
        Err(JournalError::Fenced { current: Epoch(2) })
    );
    assert_eq!(
        other.append_batch(stream, Epoch(2), group(301, 400)).await,
        Ok(Lsn(400))
    );

    // Every retained extent reads back after a full restart.
    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    assert_eq!(other.head(stream).await, Ok(Lsn(400)));
    assert_eq!(read_all(&other, stream, 400).await, group(1, 400));

    // A replacement voter catches up on batch entries and serves them.
    let configuration = other.client().configuration(stream).await.unwrap();
    let [first, second, third] = cluster.voters();
    let next = [first, third, cluster.catalog()];
    let replaced = other
        .client()
        .replace(stream, configuration.revision, next)
        .await
        .unwrap();
    assert!(replaced.revision > configuration.revision);
    cluster.stop(second).await.unwrap();
    cluster.stop(first).await.unwrap();
    // The two remaining voters, one of them new, are a quorum of the new roster.
    assert_eq!(other.head(stream).await, Ok(Lsn(400)));
    assert_eq!(read_all(&other, stream, 400).await, group(1, 400));
    assert_eq!(
        other.append_batch(stream, Epoch(2), group(401, 410)).await,
        Ok(Lsn(410))
    );
    cluster.restart(first).await.unwrap();
    cluster.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn placement_spreads_streams_and_drains_a_keeper() {
    use journal_contract::{Epoch, Lsn, StreamId};
    use std::collections::BTreeSet;

    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let mut config = cluster.placement_config(1 << 20, 4096);
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    let streams = (100..112).map(StreamId).collect::<Vec<_>>();
    let mut rosters = Vec::new();
    for stream in &streams {
        journal.create(*stream).await.unwrap();
        // A retried create derives the same voters.
        journal.create(*stream).await.unwrap();
        journal.seal(*stream, Epoch(1)).await.unwrap();
        journal
            .append_batch(
                *stream,
                Epoch(1),
                (1..=20).map(|at| (Lsn(at), batch_record(at))).collect(),
            )
            .await
            .unwrap();
        rosters.push(journal.client().configuration(*stream).await.unwrap());
    }
    let carried = rosters
        .iter()
        .flat_map(|roster| roster.voters)
        .collect::<BTreeSet<_>>();
    assert_eq!(carried.len(), 4, "placement uses every eligible keeper");
    for stream in &streams {
        assert_eq!(journal.reconcile_placement(*stream).await, Ok(None));
    }

    // Drain one voter keeper. Only the streams on it move, one voter each.
    let drained = cluster.voters()[0];
    config.draining.insert(drained);
    journal.update_placement(&config).unwrap();
    let mut moved = 0;
    for (stream, before) in streams.iter().zip(&rosters) {
        let change = journal.reconcile_placement(*stream).await.unwrap();
        if before.voters.contains(&drained) {
            let after = change.expect("a stream on the drained keeper moves");
            assert!(!after.voters.contains(&drained));
            assert_eq!(
                after
                    .voters
                    .iter()
                    .filter(|voter| before.voters.contains(voter))
                    .count(),
                2
            );
            assert!(after.revision > before.revision);
            moved += 1;
        } else {
            assert_eq!(change, None);
        }
        assert_eq!(journal.reconcile_placement(*stream).await, Ok(None));
    }
    assert!(moved > 0);
    // The drained keeper can stop. Every stream keeps its records and quorum.
    cluster.stop(drained).await.unwrap();
    for stream in &streams {
        assert_eq!(journal.head(*stream).await, Ok(Lsn(20)));
        assert_eq!(
            read_all(&journal, *stream, 20).await,
            (1..=20)
                .map(|at| (Lsn(at), batch_record(at)))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            journal
                .append(
                    *stream,
                    Epoch(1),
                    Lsn(21),
                    bytes::Bytes::from_static(b"after drain")
                )
                .await,
            Ok(Lsn(21))
        );
    }
    // A fixed roster never moves.
    let fixed = cluster
        .journal(PRINCIPALS[0], &cluster.journal_config(1 << 20, 4096))
        .unwrap();
    assert_eq!(fixed.reconcile_placement(streams[0]).await, Ok(None));
    cluster.shutdown().await.unwrap();
}

fn now_micros() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_micros() as i64
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn timed_originals_prove_quorum_sync_before_their_cutoff() {
    use journal_contract::{Epoch, JournalError, Lsn, StreamId};
    use logkeeper::stream::timed::TimedOriginal;
    use sha2::{Digest, Sha256};

    let mut cluster = LocalCluster::start_timed(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let verifier = cluster.timed_verifier();
    let journal = cluster
        .journal(PRINCIPALS[0], &config)
        .unwrap()
        .with_timed_original(verifier.clone(), Some(2048));
    assert_eq!(journal.maximum_timed_original_bytes(), Some(2048));
    let stream = StreamId(81);
    journal.create(stream).await.unwrap();
    journal.seal(stream, Epoch(1)).await.unwrap();
    journal
        .append(
            stream,
            Epoch(1),
            Lsn(1),
            bytes::Bytes::from_static(b"ordinary"),
        )
        .await
        .unwrap();
    let payload = bytes::Bytes::from_static(b"funded write");
    let original = |at: u64, payload: &[u8], cutoff: i64| TimedOriginal {
        stream,
        epoch: Epoch(1),
        at: Lsn(at),
        payload_sha256: Sha256::digest(payload).into(),
        exclusive_journal_cutoff_micros: cutoff,
        original_receiver_certificate_sha256: [7; 32],
    };
    let cutoff = now_micros() + 60_000_000;
    let timed = original(2, &payload, cutoff);
    let proof = journal
        .append_timed_original(timed, payload.clone())
        .await
        .unwrap();
    assert_eq!(proof.original, timed);
    assert!(0 < proof.original_quorum_sync_upper_micros);
    assert!(proof.original_quorum_sync_upper_micros < cutoff);
    // Readers see only the payload, and the retry returns the same proof.
    let page = journal
        .read(stream, Lsn(1), 8, std::time::Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records[1], (Lsn(2), payload.clone()));
    assert_eq!(
        journal.append_timed_original(timed, payload.clone()).await,
        Ok(proof)
    );
    assert_eq!(journal.prove_timed_original(timed).await, Ok(proof));
    // An ordinary append cannot overwrite the timed record, and an ordinary
    // record has no timed proof.
    assert!(matches!(
        journal
            .append(stream, Epoch(1), Lsn(2), payload.clone())
            .await,
        Err(JournalError::Conflict { .. })
    ));
    assert!(
        journal
            .prove_timed_original(original(1, b"ordinary", cutoff))
            .await
            .is_err()
    );

    // A durability sample at or after the cutoff refuses the original.
    cluster.shift_timed_clock(120_000_000);
    let late = original(3, b"late", now_micros() + 60_000_000);
    assert!(
        journal
            .append_timed_original(late, bytes::Bytes::from_static(b"late"))
            .await
            .is_err()
    );
    cluster.shift_timed_clock(0);
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));

    // A payload that does not match its original is refused before staging.
    let mismatched = original(3, b"declared", cutoff);
    assert!(
        journal
            .append_timed_original(mismatched, bytes::Bytes::from_static(b"other"))
            .await
            .is_err()
    );
    // A fenced writer cannot stage or append.
    let other = cluster
        .journal(PRINCIPALS[1], &config)
        .unwrap()
        .with_timed_original(verifier.clone(), Some(2048));
    assert_eq!(other.seal(stream, Epoch(2)).await, Ok(Lsn(2)));
    let fenced = original(3, b"fenced", cutoff);
    assert!(
        journal
            .append_timed_original(fenced, bytes::Bytes::from_static(b"fenced"))
            .await
            .is_err()
    );
    // A successor reopens the retained proof under the original identities.
    assert_eq!(other.prove_timed_original(timed).await, Ok(proof));
    let next = TimedOriginal {
        epoch: Epoch(2),
        ..original(3, b"successor", cutoff)
    };
    let successor = other
        .append_timed_original(next, bytes::Bytes::from_static(b"successor"))
        .await
        .unwrap();
    assert_eq!(successor.original, next);

    // The evidence survives a full restart and a snapshot.
    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    assert_eq!(other.prove_timed_original(timed).await, Ok(proof));
    assert_eq!(other.prove_timed_original(next).await, Ok(successor));
    let page = other
        .read(stream, Lsn(1), 8, std::time::Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records[2],
        (Lsn(3), bytes::Bytes::from_static(b"successor"))
    );
    // A replacement voter installs the timed records and keeps their proofs.
    let configuration = other.client().configuration(stream).await.unwrap();
    let [first, second, third] = cluster.voters();
    other
        .client()
        .replace(
            stream,
            configuration.revision,
            [first, third, cluster.catalog()],
        )
        .await
        .unwrap();
    cluster.stop(second).await.unwrap();
    cluster.stop(first).await.unwrap();
    assert_eq!(other.prove_timed_original(timed).await, Ok(proof));
    assert_eq!(
        other
            .read(stream, Lsn(2), 1, std::time::Duration::ZERO)
            .await
            .unwrap()
            .records,
        vec![(Lsn(2), payload)]
    );
    cluster.restart(first).await.unwrap();
    cluster.shutdown().await.unwrap();
}
