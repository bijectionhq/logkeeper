//! The journal-contract conformance suite against real consensus keepers.
#![cfg(feature = "consensus-testing")]

use std::sync::Arc;

use journal_contract::{Journal, conformance};
use logkeeper::stream::consensus::{Voters, testing::LocalCluster};

const PRINCIPALS: [&str; 3] = [
    "urn:logkeeper:client:1",
    "urn:logkeeper:client:2",
    "urn:logkeeper:client:3",
];

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn immutable_trim_checks_the_exact_checkpoint_and_current_writer() {
    use std::time::Duration;

    use bytes::Bytes;
    use journal_contract::{CheckpointAnchor, Epoch, JournalError, Lsn, StreamId, WriterSessionId};
    use logkeeper::stream::consensus::CLUSTER_VERSION_V4;
    use sha2::{Digest, Sha256};

    let mut cluster = LocalCluster::start_replicated_catalog(&PRINCIPALS)
        .await
        .unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let writer = cluster.journal(PRINCIPALS[0], &config).unwrap();
    tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            match writer.finalize_version(CLUSTER_VERSION_V4).await {
                Ok(version) => break assert_eq!(version, CLUSTER_VERSION_V4),
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(20)).await
                }
                Err(error) => panic!("finalizing immutable stream support: {error}"),
            }
        }
    })
    .await
    .unwrap();
    let stream = StreamId(68);
    writer.create_immutable(stream).await.unwrap();
    let original = writer
        .seal_session(stream, Epoch(0), WriterSessionId(1))
        .await
        .unwrap();
    let checkpoint = Bytes::from_static(b"checkpoint record");
    writer
        .append_session_batch(
            original.fence,
            Lsn(1),
            vec![Bytes::from_static(b"covered"), checkpoint.clone()],
        )
        .await
        .unwrap();

    let anchor = CheckpointAnchor {
        announced_at: Lsn(2),
        covered_through: Lsn(1),
        record_sha256: Sha256::digest(&checkpoint).into(),
    };
    for invalid in [
        CheckpointAnchor {
            record_sha256: [0; 32],
            ..anchor
        },
        CheckpointAnchor {
            covered_through: Lsn(2),
            ..anchor
        },
        CheckpointAnchor {
            announced_at: Lsn(3),
            ..anchor
        },
    ] {
        assert_eq!(
            writer.trim_checkpoint(original.fence, invalid).await,
            Err(JournalError::Conflict { head: Lsn(2) })
        );
    }
    let current = writer
        .seal_session(stream, original.fence.writer_epoch, WriterSessionId(2))
        .await
        .unwrap();
    assert_eq!(
        writer.trim_checkpoint(original.fence, anchor).await,
        Err(JournalError::Fenced {
            current: current.fence.writer_epoch
        })
    );
    assert_eq!(
        writer
            .read_page(stream, Lsn(1), Lsn(2), 2, Duration::ZERO)
            .await
            .unwrap()
            .floor,
        Lsn(1)
    );
    writer.trim_checkpoint(current.fence, anchor).await.unwrap();
    writer.trim_checkpoint(current.fence, anchor).await.unwrap();
    let page = writer
        .read_page(stream, Lsn(2), Lsn(2), 2, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.floor, Lsn(2));
    assert_eq!(page.records, [(Lsn(2), checkpoint)]);
    cluster.shutdown().await.unwrap();
}

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
async fn consensus_journal_with_a_replicated_catalog_satisfies_the_contract() {
    let mut cluster = LocalCluster::start_replicated_catalog(&PRINCIPALS)
        .await
        .unwrap();
    let config = cluster.journal_config(
        conformance::LIMITS.stream_quota_bytes,
        conformance::LIMITS.max_record_bytes,
    );
    assert!(config.catalog_voters.is_some());
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
async fn a_replicated_catalog_creates_without_its_seeding_keeper_and_survives_restart() {
    use bytes::Bytes;
    use journal_contract::{Epoch, Lsn, StreamId};

    let mut cluster = LocalCluster::start_replicated_catalog(&PRINCIPALS)
        .await
        .unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    journal.create(StreamId(70)).await.unwrap();
    cluster.stop(cluster.catalog()).await.unwrap();
    let stream = StreamId(71);
    journal.create(stream).await.unwrap();
    assert_eq!(journal.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
    assert_eq!(
        journal
            .append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"one"))
            .await,
        Ok(Lsn(1))
    );
    cluster.restart(cluster.catalog()).await.unwrap();
    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    let cold = cluster.journal(PRINCIPALS[1], &config).unwrap();
    assert_eq!(cold.head(stream).await, Ok(Lsn(1)));
    assert_eq!(journal.create(StreamId(72)).await, Ok(()));
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

/// Full keeper batches change every snapshot index page between two
/// snapshots. Snapshots must still succeed, or the stream's Raft group stops.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn full_batches_snapshot_across_many_index_pages_and_survive_restart() {
    use journal_contract::{Epoch, Lsn, StreamId};

    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(64 << 20, 4096);
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    let stream = StreamId(79);
    journal.create(stream).await.unwrap();
    assert_eq!(journal.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
    let record = |at: u64| bytes::Bytes::from(at.to_be_bytes().to_vec());
    // 300 entries of 200 records cross two snapshot intervals of 128 entries.
    // The second snapshot changes about 200 of the 469 index pages.
    const PER: u64 = 200;
    let batches = 300u64;
    for batch in 0..batches {
        let group = (batch * PER + 1..=(batch + 1) * PER)
            .map(|at| (Lsn(at), record(at)))
            .collect::<Vec<_>>();
        assert_eq!(
            journal.append_batch(stream, Epoch(1), group).await,
            Ok(Lsn((batch + 1) * PER)),
            "batch {batch}"
        );
    }
    let head = batches * PER;
    assert_eq!(journal.head(stream).await, Ok(Lsn(head)));
    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    assert_eq!(journal.head(stream).await, Ok(Lsn(head)));
    let page = journal
        .read(stream, Lsn(head - 3), 4, std::time::Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page.records,
        (head - 3..=head)
            .map(|at| (Lsn(at), record(at)))
            .collect::<Vec<_>>()
    );
    cluster.shutdown().await.unwrap();
}

/// A stream holds 262,144 retained records. Filled in full keeper batches,
/// it snapshots, survives a restart of every keeper with its first and last
/// records, and refuses one more record as full.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_stream_fills_to_its_retained_record_limit_and_survives_restart() {
    use journal_contract::{Epoch, JournalError, Lsn, StreamId};

    const LIMIT: u64 = 262_144;
    const PER: u64 = 256;
    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(64 << 20, 4096);
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    let stream = StreamId(80);
    journal.create(stream).await.unwrap();
    assert_eq!(journal.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
    let record = |at: u64| bytes::Bytes::from(at.to_be_bytes().to_vec());
    for batch in 0..LIMIT / PER {
        let group = (batch * PER + 1..=(batch + 1) * PER)
            .map(|at| (Lsn(at), record(at)))
            .collect::<Vec<_>>();
        assert_eq!(
            journal.append_batch(stream, Epoch(1), group).await,
            Ok(Lsn((batch + 1) * PER)),
            "batch {batch}"
        );
    }
    assert!(matches!(
        journal
            .append(stream, Epoch(1), Lsn(LIMIT + 1), record(LIMIT + 1))
            .await,
        Err(JournalError::Full { .. })
    ));
    cluster.shutdown().await.unwrap();
    for keeper in cluster.voters().into_iter().chain([cluster.catalog()]) {
        cluster.restart(keeper).await.unwrap();
    }
    let journal = cluster.journal(PRINCIPALS[0], &config).unwrap();
    assert_eq!(journal.head(stream).await, Ok(Lsn(LIMIT)));
    for at in [1, LIMIT] {
        let page = journal
            .read(stream, Lsn(at), 1, std::time::Duration::ZERO)
            .await
            .unwrap();
        assert_eq!(page.records, vec![(Lsn(at), record(at))]);
    }
    assert_eq!(journal.seal(stream, Epoch(1)).await, Ok(Lsn(LIMIT)));
    assert!(matches!(
        journal
            .append_batch(stream, Epoch(1), vec![(Lsn(LIMIT + 1), record(LIMIT + 1))])
            .await,
        Err(JournalError::Full { .. })
    ));
    assert_eq!(journal.head(stream).await, Ok(Lsn(LIMIT)));
    cluster.shutdown().await.unwrap();
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
    let [first, second, third] = <[_; 3]>::try_from(&cluster.voters()[..]).unwrap();
    let next = Voters::from([first, third, cluster.catalog()]);
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
    let [first, second, third] = <[_; 3]>::try_from(&cluster.voters()[..]).unwrap();
    other
        .client()
        .replace(
            stream,
            configuration.revision,
            Voters::from([first, third, cluster.catalog()]),
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_written_keeper_configuration_reads_back_for_a_keeper_process() {
    use logkeeper::stream::consensus::{Config, SyncMode};

    let mut cluster = LocalCluster::start(&PRINCIPALS).await.unwrap();
    let keeper = cluster.voters()[0];
    cluster.stop(keeper).await.unwrap();
    let config = Config::read(&cluster.write_config(keeper).unwrap()).unwrap();
    assert_eq!(config.keeper, keeper);
    assert_eq!(cluster.keepers()[&keeper], config.listen);
    assert_eq!(config.catalog, cluster.catalog());
    assert_eq!(config.sync_mode, SyncMode::Fsync);
    // The keeper serves its media again from the configuration read back.
    let listener = tokio::net::TcpListener::bind(config.listen).await.unwrap();
    let stop = tokio_util::sync::CancellationToken::new();
    let serving = tokio::spawn(config.serve(listener, stop.clone()));
    let journal = cluster
        .journal(PRINCIPALS[0], &cluster.journal_config(1 << 20, 4096))
        .unwrap();
    let stream = journal_contract::StreamId(7);
    journal.create(stream).await.unwrap();
    journal
        .seal(stream, journal_contract::Epoch(1))
        .await
        .unwrap();
    stop.cancel();
    serving.await.unwrap().unwrap();
    cluster.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn timed_staging_and_retries_require_the_immutable_writer_session() {
    use std::time::Duration;

    use bytes::Bytes;
    use journal_contract::{Epoch, JournalError, Lsn, StreamId, WriterFence, WriterSessionId};
    use logkeeper::stream::consensus::CLUSTER_VERSION_V4;
    use logkeeper::stream::timed::TimedOriginal;
    use sha2::{Digest, Sha256};

    let mut cluster = LocalCluster::start_timed(&PRINCIPALS).await.unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let journal = cluster
        .journal(PRINCIPALS[0], &config)
        .unwrap()
        .with_timed_original(cluster.timed_verifier(), Some(2048));
    let stream = StreamId(82);
    let finalized = tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            match journal.finalize_version(CLUSTER_VERSION_V4).await {
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(20)).await
                }
                result => break result,
            }
        }
    })
    .await
    .expect("all keepers respond to v4 finalization");
    assert_eq!(finalized, Ok(CLUSTER_VERSION_V4));
    journal.create_immutable(stream).await.unwrap();
    let fence = journal
        .seal_session(stream, Epoch(0), WriterSessionId(1))
        .await
        .unwrap()
        .fence;
    let wrong = WriterFence {
        writer_session_id: WriterSessionId(2),
        ..fence
    };
    let cutoff = now_micros() + 60_000_000;
    let original = |payload: &[u8]| TimedOriginal {
        stream,
        epoch: Epoch(1),
        at: Lsn(1),
        payload_sha256: Sha256::digest(payload).into(),
        exclusive_journal_cutoff_micros: cutoff,
        original_receiver_certificate_sha256: [7; 32],
    };
    // A seal can commit before both selected signers have applied it.
    let stage = |fence: WriterFence, payload: Bytes| {
        let original = original(&payload);
        let journal = &journal;
        async move {
            let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
            loop {
                let result = journal
                    .append_session_timed_original(fence, original, payload.clone())
                    .await;
                let waiting_for_signer = match &result {
                    Err(JournalError::Unavailable | JournalError::NotFound) => true,
                    Err(JournalError::Fenced { current }) => *current < fence.writer_epoch,
                    _ => false,
                };
                if !waiting_for_signer || tokio::time::Instant::now() >= deadline {
                    return result;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        }
    };
    assert_eq!(
        stage(wrong, Bytes::from_static(b"wrong session")).await,
        Err(JournalError::Fenced { current: Epoch(1) }),
    );
    let payload = Bytes::from_static(b"current session");
    let exact = original(&payload);
    let proof = stage(fence, payload.clone()).await.unwrap();
    assert!(proof.original_quorum_sync_upper_micros < cutoff);
    assert_eq!(
        journal
            .append_session_timed_original(fence, exact, payload.clone())
            .await,
        Ok(proof)
    );
    assert_eq!(
        journal
            .append_session_timed_original(wrong, exact, payload.clone())
            .await,
        Err(JournalError::Fenced { current: Epoch(1) }),
    );
    journal
        .seal_session(stream, Epoch(1), WriterSessionId(2))
        .await
        .unwrap();
    assert_eq!(
        journal
            .append_session_timed_original(fence, exact, payload)
            .await,
        Err(JournalError::Fenced { current: Epoch(2) }),
    );
    assert_eq!(journal.prove_timed_original(exact).await, Ok(proof));
    assert_eq!(
        journal.attest_timed_original(exact).await,
        Err(JournalError::Unsupported)
    );
    cluster.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn timed_original_proof_survives_local_eviction_until_checkpoint_trim() {
    use std::{
        sync::atomic::{AtomicUsize, Ordering},
        time::Duration,
    };

    use bytes::Bytes;
    use journal_contract::{
        CheckpointInstallation, Epoch, JournalError, Lsn, StreamId, WriterSessionId,
    };
    use logkeeper::stream::{
        timed::{TimedCommitment, TimedOriginal, TimedOriginalVerifier},
        wire::KeeperId,
    };
    use sha2::{Digest, Sha256};

    let objects = tempfile::tempdir().unwrap();
    let offload = serde_json::from_value(serde_json::json!({
        "url": format!("file://{}", objects.path().display()),
        "batch_interval_ms": 3_600_000,
        "retain_local_bytes": 0,
    }))
    .unwrap();
    let mut cluster = LocalCluster::start_timed(&PRINCIPALS).await.unwrap();
    cluster
        .enable_offload(PRINCIPALS[0], offload)
        .await
        .unwrap();
    let config = cluster.journal_config(1 << 20, 4096);
    let verifier = cluster.timed_verifier();
    let journal = cluster
        .journal(PRINCIPALS[0], &config)
        .unwrap()
        .with_timed_original(verifier.clone(), Some(2048));
    let stream = StreamId(83);
    journal.create_immutable(stream).await.unwrap();
    let writer = journal
        .seal_session(stream, Epoch(0), WriterSessionId(1))
        .await
        .unwrap();
    let payload = Bytes::from_static(b"offloaded timed original");
    let original = TimedOriginal {
        stream,
        at: Lsn(1),
        epoch: writer.fence.writer_epoch,
        payload_sha256: Sha256::digest(&payload).into(),
        exclusive_journal_cutoff_micros: now_micros() + 60_000_000,
        original_receiver_certificate_sha256: [9; 32],
    };
    struct StopBeforeCommit {
        verifier: Arc<dyn TimedOriginalVerifier>,
        samples: AtomicUsize,
    }
    impl TimedOriginalVerifier for StopBeforeCommit {
        fn verify(&self, keeper: KeeperId, statement: &[u8], signature: &[u8; 64]) -> bool {
            self.verifier.verify(keeper, statement, signature)
                && self.samples.fetch_add(1, Ordering::Relaxed) == 0
        }
    }

    let stop = Arc::new(StopBeforeCommit {
        verifier: verifier.clone(),
        samples: AtomicUsize::new(0),
    });
    let stage_only = cluster
        .journal(PRINCIPALS[0], &config)
        .unwrap()
        .with_timed_original(stop.clone(), Some(2048));
    assert_eq!(
        stage_only
            .append_session_timed_original(writer.fence, original, payload.clone())
            .await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(stop.samples.load(Ordering::Relaxed), 2);
    assert_eq!(
        journal.attest_timed_original(original).await,
        Err(JournalError::Conflict { head: Lsn(0) })
    );
    let accepted = journal
        .append_session_timed_original(writer.fence, original, payload.clone())
        .await
        .unwrap();
    assert_eq!(journal.prove_timed_original(original).await, Ok(accepted));

    let status = journal.client().offload_status(stream, true).await.unwrap();
    assert_eq!(status.offloaded_through, original.at);
    assert_eq!(status.floor, original.at);
    assert_eq!(status.local_floor, Lsn(2));
    assert_eq!(
        journal
            .read(stream, original.at, 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        vec![(original.at, payload)]
    );
    assert_eq!(journal.prove_timed_original(original).await, Ok(accepted));
    let different = TimedOriginal {
        payload_sha256: [5; 32],
        ..original
    };
    assert_eq!(
        journal.prove_timed_original(different).await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        journal.attest_timed_original(different).await,
        Err(JournalError::Unavailable)
    );
    let saved = journal
        .attest_timed_original(original)
        .await
        .unwrap()
        .encode();

    journal
        .install_checkpoint(
            writer.fence,
            CheckpointInstallation {
                operation_id: 2,
                checkpoint_lsn: Lsn(2),
                covered_through_lsn: original.at,
                record: Bytes::from_static(b"covering checkpoint"),
            },
        )
        .await
        .unwrap();
    assert_eq!(
        journal.prove_timed_original(original).await,
        Err(JournalError::Trimmed { floor: Lsn(2) })
    );
    assert_eq!(
        journal.attest_timed_original(original).await,
        Err(JournalError::Trimmed { floor: Lsn(2) })
    );
    cluster.shutdown().await.unwrap();

    let commitment = TimedCommitment::decode(&saved).unwrap();
    assert_eq!(
        commitment.verify(config.catalog, original, &*verifier),
        Some(accepted)
    );
    assert_eq!(
        commitment.verify(uuid::Uuid::from_u128(999), original, &*verifier),
        None
    );
    assert_eq!(
        commitment.verify(config.catalog, different, &*verifier),
        None
    );
    let mut tampered = saved;
    *tampered.last_mut().unwrap() ^= 1;
    assert_eq!(
        TimedCommitment::decode(&tampered)
            .unwrap()
            .verify(config.catalog, original, &*verifier),
        None
    );
}
