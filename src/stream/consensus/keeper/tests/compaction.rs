//! Segment compaction on running keepers.

use super::*;
use crate::stream::consensus::Voters;

/// One retained record of an otherwise idle stream no longer keeps its
/// whole WAL segment once the rest of the segment is dead: its owner
/// snapshots and purges, its slice moves to the active segment, its
/// snapshot is rebuilt to name the copy, and the old segment goes. The
/// record survives a restart.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_cold_record_no_longer_pins_its_segment() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let (cold, filler) = (StreamId(230), StreamId(231));
    let mut fences = Vec::new();
    for stream in [cold, filler] {
        journal
            .create(stream, Voters::from([a, b, c]), 64 << 20)
            .await
            .unwrap();
        let sealed = journal
            .seal(stream, Epoch(0), Uuid::from_u128(9))
            .await
            .unwrap();
        fences.push(sealed.fence);
    }
    let record = Bytes::from(vec![42; 2048]);
    journal
        .append(cold, fences[0], Lsn(1), record.clone())
        .await
        .unwrap();
    let group = cluster.group(a, cold).await;
    let segment = timeout(WAIT, async {
        loop {
            if let Some((segment, _)) = group.state.payload_path() {
                return segment;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(group);
    let engines = [a, b, c].map(|id| cluster.running[&id].engine.clone());
    let mut at = 0;
    // Relocated slices are a format N-1 cannot read: before the cluster
    // version is finalized, passes copy nothing and the segment stays.
    for _ in 0..12 {
        for _ in 0..8 {
            at += 1;
            journal
                .append(filler, fences[1], Lsn(at), Bytes::from(vec![7; 64 * 1024]))
                .await
                .unwrap();
            journal.trim(filler, fences[1], Lsn(at)).await.unwrap();
        }
        for engine in &engines {
            engine.compact_pass(Duration::ZERO).await;
        }
    }
    assert!(segment.exists(), "nothing relocates before finalization");
    cluster.finalize().await;
    timeout(Duration::from_secs(60), async {
        while segment.exists() {
            for _ in 0..8 {
                at += 1;
                journal
                    .append(filler, fences[1], Lsn(at), Bytes::from(vec![7; 64 * 1024]))
                    .await
                    .unwrap();
                journal.trim(filler, fences[1], Lsn(at)).await.unwrap();
            }
            for engine in &engines {
                engine.compact_pass(Duration::ZERO).await;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("the cold record's segment was compacted away");
    let group = cluster.group(a, cold).await;
    let (moved, _) = group.state.payload_path().unwrap();
    assert_ne!(moved, segment, "the record lives in a newer segment");
    assert_eq!(
        group.state.page(Lsn(1), 1).await.unwrap().records,
        [(Lsn(1), record.clone())]
    );
    drop(group);

    cluster.running.remove(&a).unwrap().stop().await;
    cluster.restart(a).await;
    let group = cluster.group(a, cold).await;
    assert_eq!(
        group.state.page(Lsn(1), 1).await.unwrap().records,
        [(Lsn(1), record)]
    );
    cluster.stop_all().await;
}
