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
