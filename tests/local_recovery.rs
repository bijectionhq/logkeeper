//! A consumer recovers a stream that lost two of its three voters on a
//! `LocalCluster` with spares, through the generic journal contract: the
//! operator runs `recover-stream` on the stopped survivor, a writer meets
//! `Recovered`, acknowledges it, seals again and keeps writing on the
//! survivor and two spares.
#![cfg(feature = "consensus-testing")]

use std::time::{Duration, Instant};

use bytes::Bytes;
use journal_contract::{Epoch, Journal, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::testing::LocalCluster;

const PRINCIPAL: &str = "urn:logkeeper:client:local-recovery";
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
async fn a_spared_cluster_recovers_a_stream_that_lost_two_voters() {
    let mut cluster = LocalCluster::start_spared(&[PRINCIPAL]).await.unwrap();
    let [survivor, b, c] = <[_; 3]>::try_from(&cluster.voters()[..]).unwrap();
    assert_eq!(cluster.spares().len(), 2);
    let config = cluster.journal_config(1 << 20, 1024);
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    // With liveness leases finalized, the catalog fences the lost voters
    // and the recovery waits out their leases, so it needs no retirement
    // proofs from their hosts.
    // Every keeper learns the level before writing, so the survivor records
    // its commit index and the recovery keeps exactly the committed prefix.
    let version = logkeeper::stream::consensus::CLUSTER_VERSION_CURRENT;
    assert_eq!(
        cluster.finalize_version(PRINCIPAL, version).await.unwrap(),
        version
    );
    let stream = StreamId(0x5eed);
    retry(|| journal.create(stream)).await.unwrap();
    assert_eq!(retry(|| journal.seal(stream, Epoch(1))).await, Ok(Lsn(0)));
    for at in 1..=5 {
        assert_eq!(
            retry(|| journal.append(stream, Epoch(1), Lsn(at), record(at))).await,
            Ok(Lsn(at))
        );
    }
    // Every voter holds the records before two of them are lost.
    tokio::time::sleep(Duration::from_millis(500)).await;
    cluster.stop(b).await.unwrap();
    cluster.stop(c).await.unwrap();
    assert!(
        cluster
            .recover_stream(survivor, stream, [b, c])
            .await
            .is_err(),
        "a running survivor must not be recovered"
    );
    cluster.stop(survivor).await.unwrap();
    let report = cluster
        .recover_stream(survivor, stream, [c, b])
        .await
        .unwrap();
    assert!(report.written);
    assert_eq!(report.head, Lsn(5));
    // The replacements are two live keepers outside the lost configuration,
    // in domains distinct from each other and from the survivor's.
    assert!(report.voters.contains(&survivor));
    assert!(!report.voters.contains(&b) && !report.voters.contains(&c));
    cluster.restart(survivor).await.unwrap();

    assert_eq!(
        retry(|| journal.seal(stream, Epoch(2))).await,
        Err(JournalError::Recovered { head: Lsn(5) })
    );
    assert_eq!(
        retry(|| journal.acknowledge_recovery(stream)).await,
        Ok(Lsn(5))
    );
    // The acknowledgement wrote the recovery's typed entry right after the
    // last record kept, as the first entry of the recovered epoch.
    let epoch = Epoch(report.epoch.0 + 1);
    assert_eq!(retry(|| journal.seal(stream, epoch)).await, Ok(Lsn(6)));
    assert_eq!(
        retry(|| journal.append(stream, epoch, Lsn(7), record(7))).await,
        Ok(Lsn(7))
    );
    let page = retry(|| journal.read(stream, Lsn(1), 10, Duration::ZERO))
        .await
        .unwrap();
    let entry = page.recovery(Lsn(6)).cloned().expect("the recovery's typed entry");
    assert_eq!(entry.fence.head, Lsn(5));
    assert_eq!(entry.loss_point, report.loss_point);
    assert!(entry.exact);
    assert_eq!(entry.configuration_epoch, report.revision);
    assert_eq!(entry.marker, None);
    assert_eq!(page.recoveries.len(), 1);
    let mut records = page.records;
    assert_eq!(records.remove(5), (Lsn(6), entry.encode()));
    assert_eq!(
        records,
        [1, 2, 3, 4, 5, 7].map(|at| (Lsn(at), record(at))).to_vec()
    );
    cluster.shutdown().await.unwrap();
}
