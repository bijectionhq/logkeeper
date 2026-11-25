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
