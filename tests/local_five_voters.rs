//! A consumer writes to a five-voter stream on a `LocalCluster` through the
//! generic journal contract, keeps writing and reading after losing any two
//! voters, and catches the returning voters up.
#![cfg(feature = "consensus-testing")]

use std::time::{Duration, Instant};

use bytes::Bytes;
use journal_contract::{Epoch, Journal, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::testing::LocalCluster;

const PRINCIPAL: &str = "urn:logkeeper:client:local-five";
const DEADLINE: Duration = Duration::from_secs(60);

async fn retry<T, F: std::future::Future<Output = Result<T, JournalError>>>(
    call: impl Fn() -> F,
) -> Result<T, JournalError> {
    let started = Instant::now();
    loop {
        match call().await {
            Err(JournalError::Unavailable) if started.elapsed() < DEADLINE => {
                tokio::time::sleep(Duration::from_millis(100)).await
            }
            result => return result,
        }
    }
}

fn record(at: u64) -> Bytes {
    Bytes::from(format!("record-{at}"))
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_five_voter_stream_keeps_serving_without_two_voters() {
    let mut cluster = LocalCluster::start_five_voters(&[PRINCIPAL]).await.unwrap();
    let voters = cluster.voters();
    assert_eq!(voters.len(), 5);
    let config = cluster.journal_config(1 << 20, 1024);
    assert_eq!(config.replication_factor, 5);
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    let stream = StreamId(0x5f5);
    retry(|| journal.create(stream)).await.unwrap();
    assert_eq!(retry(|| journal.seal(stream, Epoch(1))).await, Ok(Lsn(0)));
    for at in 1..=4 {
        assert_eq!(
            retry(|| journal.append(stream, Epoch(1), Lsn(at), record(at))).await,
            Ok(Lsn(at))
        );
    }

    // Lose two voters in one zone: three remain, a quorum.
    let (first, second) = (voters[1], voters[3]);
    cluster.stop(first).await.unwrap();
    cluster.stop(second).await.unwrap();
    for at in 5..=8 {
        assert_eq!(
            retry(|| journal.append(stream, Epoch(1), Lsn(at), record(at))).await,
            Ok(Lsn(at))
        );
    }
    let page = retry(|| journal.read(stream, Lsn(1), 10, Duration::ZERO))
        .await
        .unwrap();
    assert_eq!(
        page.records,
        (1..=8).map(|at| (Lsn(at), record(at))).collect::<Vec<_>>()
    );

    // The returning voters catch up and the stream goes on.
    cluster.restart(first).await.unwrap();
    cluster.restart(second).await.unwrap();
    assert_eq!(
        retry(|| journal.append(stream, Epoch(1), Lsn(9), record(9))).await,
        Ok(Lsn(9))
    );
    assert_eq!(retry(|| journal.head(stream)).await, Ok(Lsn(9)));
    cluster.shutdown().await.unwrap();
}
