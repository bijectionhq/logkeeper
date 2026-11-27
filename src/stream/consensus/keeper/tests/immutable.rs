use super::*;
use crate::stream::consensus::{ConsensusJournal, JournalConfig};
use journal_contract::{Journal, WriterSessionId};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn immutable_streams_keep_exact_seal_receipts_across_snapshots_and_restart() {
    let mut cluster = Cluster::start_replicated().await;
    let [a, b, c, d] = cluster.ids;
    let voters = [a, b, c];
    let stream = StreamId(9641);
    let legacy_stream = StreamId(9642);
    let config = JournalConfig {
        keepers: cluster.keepers.clone(),
        catalog: cluster.catalog,
        catalog_voters: cluster.catalog_voters,
        voters: Some(Voters::from(voters)),
        replication_factor: 3,
        placement: None,
        draining: Default::default(),
        retired: Default::default(),
        quota_bytes: 32 * 1024,
        max_record_bytes: 4096,
        deadline_ms: 10_000,
        domain: None,
    };
    let journal = ConsensusJournal::new(&cluster.credentials, &config).unwrap();
    let other = cluster.client(&cluster.other);
    let session = WriterSessionId(77);
    let second_session = WriterSessionId(78);

    assert_eq!(
        journal.create_immutable(stream).await,
        Err(JournalError::Unsupported)
    );
    cluster.finalize().await;
    journal.create_immutable(stream).await.unwrap();
    assert_eq!(journal.require_immutable(stream).await, Ok(()));
    journal.create(legacy_stream).await.unwrap();
    assert_eq!(
        journal.require_immutable(legacy_stream).await,
        Err(JournalError::Unsupported)
    );
    assert_eq!(
        journal.create_immutable(legacy_stream).await,
        Err(JournalError::Conflict { head: Lsn(0) }),
    );
    assert_eq!(
        journal.seal_session(legacy_stream, Epoch(0), session).await,
        Err(JournalError::Unsupported),
    );
    assert_eq!(journal.seal(legacy_stream, Epoch(1)).await, Ok(Lsn(0)));
    assert_eq!(
        journal.seal(stream, Epoch(1)).await,
        Err(JournalError::Unsupported)
    );

    let seal = journal
        .seal_session(stream, Epoch(0), session)
        .await
        .unwrap();
    assert_eq!(seal.sealed_head_lsn, Lsn(0));
    assert_eq!(
        other.seal_session(stream, Epoch(0), session).await,
        Err(JournalError::Fenced { current: Epoch(1) }),
    );
    assert_eq!(
        journal.seal_session(stream, Epoch(0), second_session).await,
        Err(JournalError::Fenced { current: Epoch(1) }),
    );
    let first = Bytes::from_static(b"first");
    let second = Bytes::from_static(b"second");
    let records = vec![first.clone(), second.clone()];
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(1), records.clone())
            .await,
        Ok(Lsn(2))
    );
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(1), records)
            .await,
        Ok(Lsn(2))
    );
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(2), vec![second.clone(), first.clone()])
            .await,
        Err(JournalError::Conflict { head: Lsn(2) }),
    );
    let page = journal
        .read_page(stream, Lsn(1), Lsn(2), 2, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.head, Lsn(2));
    assert_eq!(
        page.records,
        vec![(Lsn(1), first.clone()), (Lsn(2), second)]
    );
    assert_eq!(
        journal.seal_session(stream, Epoch(0), session).await,
        Ok(seal)
    );

    for voter in voters {
        let group = cluster.group(voter, stream).await;
        timeout(WAIT, async {
            while group.state.head() != Ok(Lsn(2)) {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap();
        let index = group.state.applied().unwrap();
        group.raft.trigger().snapshot().await.unwrap();
        timeout(WAIT, group.state.wait_for_snapshot(index))
            .await
            .unwrap()
            .unwrap();
    }

    cluster.stop_all().await;
    let error = cluster.configs[&a]
        .recover_stream(stream, Recovery::default())
        .await
        .unwrap_err();
    assert!(error.to_string().contains("immutable histories"));
    let keepers = cluster.configs.keys().copied().collect::<Vec<_>>();
    for keeper in keepers {
        cluster.restart(keeper).await;
    }

    assert_eq!(
        journal.seal_session(stream, Epoch(0), session).await,
        Ok(seal)
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    let changed = cluster
        .client(&cluster.credentials)
        .replace(stream, 0, Voters::from([a, b, d]))
        .await
        .unwrap();
    assert_eq!(changed.voters, [a, b, d]);
    assert_eq!(
        journal.seal_session(stream, Epoch(0), session).await,
        Ok(seal)
    );
    let replacement = journal
        .seal_session(stream, Epoch(1), second_session)
        .await
        .unwrap();
    assert_eq!(replacement.sealed_head_lsn, Lsn(2));
    assert_eq!(
        journal
            .append_session_batch(seal.fence, Lsn(3), vec![first.clone()])
            .await,
        Err(JournalError::Fenced { current: Epoch(2) }),
    );
    assert_eq!(
        journal
            .append_session_batch(replacement.fence, Lsn(3), vec![first])
            .await,
        Ok(Lsn(3))
    );
    assert_eq!(
        journal.trim_session(replacement.fence, Lsn(2)).await,
        Ok(())
    );
    assert_eq!(
        journal
            .append_session_batch(replacement.fence, Lsn(2), vec![Bytes::from_static(b"lost")])
            .await,
        Err(JournalError::Trimmed { floor: Lsn(3) }),
    );
    let retained = journal
        .read_page(stream, Lsn(3), Lsn(3), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        retained.records,
        vec![(Lsn(3), Bytes::from_static(b"first"))]
    );
    cluster.stop_all().await;
}
