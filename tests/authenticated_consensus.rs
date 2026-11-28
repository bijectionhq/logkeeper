#![cfg(feature = "consensus-testing")]

use std::{fs::File, time::Duration};

use bytes::Bytes;
use journal_contract::{
    CheckpointAnchor, CheckpointHold, CheckpointInstallation, Epoch, Journal, JournalError, Lsn,
    StreamId, WriterSessionId,
};
use logkeeper::stream::consensus::{
    CLUSTER_VERSION_AUTHENTICATED, JournalConfig, Voters,
    authenticated::{Archive, CatalogRoot},
    testing::LocalCluster,
};
use logkeeper::stream::timed::TimedOriginal;
use sha2::{Digest, Sha256};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn authenticated_consensus_survives_trim_replacement_rotation_and_shutdown() {
    let principal = "urn:logkeeper:client:authenticated-test";
    let mut cluster = LocalCluster::start_authenticated(&[principal])
        .await
        .unwrap();
    let stream = StreamId(73);
    let config = cluster.journal_config(1 << 20, 65_536);
    let journal = cluster
        .journal(principal, &config)
        .unwrap()
        .with_timed_original(cluster.timed_verifier(), Some(65_536));
    assert_eq!(
        journal.create_authenticated(stream).await,
        Err(JournalError::Unsupported)
    );
    cluster
        .finalize_version(principal, CLUSTER_VERSION_AUTHENTICATED)
        .await
        .unwrap();
    let root = cluster.catalog_root().unwrap();
    journal.create_authenticated(stream).await.unwrap();

    let writer = journal
        .seal_session(stream, Epoch(0), WriterSessionId(1))
        .await
        .unwrap();
    let ordinary = Bytes::from_static(b"ordinary");
    journal
        .append_session_batch(writer.fence, Lsn(1), vec![ordinary.clone()])
        .await
        .unwrap();
    let payload = Bytes::from_static(b"authorized");
    let original = TimedOriginal {
        stream,
        epoch: writer.fence.writer_epoch,
        at: Lsn(2),
        payload_sha256: Sha256::digest(&payload).into(),
        exclusive_journal_cutoff_micros: now_micros() + 60_000_000,
        original_receiver_certificate_sha256: [7; 32],
    };
    let [first, second, third] =
        <[_; 3]>::try_from(cluster.voters().into_sorted().to_vec()).unwrap();
    tokio::time::timeout(Duration::from_secs(20), async {
        while journal.client().leader(stream) != Some(third) {
            let _ = journal.client().prefer_leader(stream, third).await;
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .unwrap();
    let timed = journal
        .append_session_timed_original(writer.fence, original, payload)
        .await
        .unwrap();
    assert_eq!(
        journal.attest_timed_original(original).await,
        Err(JournalError::Unsupported)
    );
    let (earlier, history) = journal.authenticated_head(stream, Some(2)).await.unwrap();
    earlier.verify(root, &history).unwrap();

    let replacement_writer = journal
        .seal_session(stream, writer.fence.writer_epoch, WriterSessionId(2))
        .await
        .unwrap();
    let first_checkpoint = Bytes::from_static(b"first checkpoint");
    journal
        .install_checkpoint(
            replacement_writer.fence,
            CheckpointInstallation {
                operation_id: 1,
                checkpoint_lsn: Lsn(3),
                covered_through_lsn: Lsn(1),
                record: first_checkpoint.clone(),
            },
        )
        .await
        .unwrap();
    let hold = CheckpointHold {
        operation_id: 7,
        installation_sha256: [1; 32],
        anchor: CheckpointAnchor {
            announced_at: Lsn(3),
            covered_through: Lsn(1),
            record_sha256: Sha256::digest(&first_checkpoint).into(),
        },
    };
    journal
        .client()
        .retain_checkpoint(stream, hold)
        .await
        .unwrap();
    journal
        .client()
        .release_checkpoint(stream, hold)
        .await
        .unwrap();
    journal
        .install_checkpoint(
            replacement_writer.fence,
            CheckpointInstallation {
                operation_id: 2,
                checkpoint_lsn: Lsn(4),
                covered_through_lsn: Lsn(3),
                record: Bytes::from_static(b"covering checkpoint"),
            },
        )
        .await
        .unwrap();
    assert!(matches!(
        journal.read(stream, Lsn(2), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(4) })
    ));
    let proof = journal.inclusion(stream, Lsn(2), None).await.unwrap();
    let leaf = proof.verify(root).unwrap();
    assert_eq!(leaf.payload_sha256, original.payload_sha256);
    assert_eq!(
        leaf.quorum_durable_upper_micros,
        timed.original_quorum_sync_upper_micros
    );

    let replacement_keeper = cluster.spares()[1];
    let current = journal.client().configuration(stream).await.unwrap();
    journal
        .client()
        .replace(
            stream,
            current.revision,
            Voters::from([first, second, replacement_keeper]),
        )
        .await
        .unwrap();
    let (_, after_move) = journal.authenticated_head(stream, Some(4)).await.unwrap();
    let moved = after_move.stream.last().unwrap().authority.voters.clone();
    assert!(moved.keepers().contains(&replacement_keeper));
    assert!(!moved.keepers().contains(&third));
    assert!(after_move.history.transitions.is_empty(), "a stream move leaves the catalog history alone");

    cluster.rotate_authentication_key(first).await.unwrap();
    journal
        .append_session_batch(replacement_writer.fence, Lsn(5), vec![ordinary.clone()])
        .await
        .unwrap();
    let old_key = moved.key(first).copied();
    let (later, rotated) = tokio::time::timeout(Duration::from_secs(20), async {
        loop {
            if let Ok((head, certification)) = journal.authenticated_head(stream, Some(5)).await
                && certification.stream.last().unwrap().authority.voters.key(first).copied()
                    != old_key
            {
                break (head, certification);
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .unwrap();
    assert!(
        earlier.verify(root, &rotated).is_err(),
        "a replaced roster's head no longer verifies on its own"
    );
    journal
        .consistency(earlier, later)
        .await
        .unwrap()
        .verify(root)
        .unwrap();
    journal.client().delete(stream).await.unwrap();
    let archived = journal.inclusion(stream, Lsn(2), None).await.unwrap();
    cluster.shutdown().await.unwrap();
    assert_eq!(archived.verify(root).unwrap(), leaf);

    let path = cluster
        .directory()
        .join("stream-archives")
        .join(format!("catalog-{:032x}", cluster.catalog().as_u128()))
        .join(format!("{:032x}", stream.0))
        .join("0000000000000005.archive");
    let archive = Archive::read_from(&mut File::open(path).unwrap()).unwrap();
    archive.verify(root).unwrap();
    assert_eq!(archive.tree.leaf(Lsn(2)), Some(leaf));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn authenticated_refused_stage_does_not_reserve_the_position() {
    let principal = "urn:logkeeper:client:authenticated-retry";
    let mut cluster = LocalCluster::start_authenticated(&[principal])
        .await
        .unwrap();
    cluster
        .finalize_version(principal, CLUSTER_VERSION_AUTHENTICATED)
        .await
        .unwrap();
    let config = cluster.journal_config(512, 1024);
    let journal = cluster.journal(principal, &config).unwrap();
    let root = cluster.catalog_root().unwrap();
    let unpinned = cluster
        .journal(principal, &JournalConfig { catalog_root: None, ..config.clone() })
        .unwrap();
    assert_eq!(unpinned.catalog_history().await, Err(JournalError::Unsupported));
    let misled = cluster
        .journal(
            principal,
            &JournalConfig {
                catalog_root: Some(CatalogRoot([9; 32])),
                ..config.clone()
            },
        )
        .unwrap();
    assert_eq!(misled.catalog_history().await, Err(JournalError::Corrupted));
    let stream = StreamId(74);
    journal.create_authenticated(stream).await.unwrap();
    let writer = journal
        .seal_session(stream, Epoch(0), WriterSessionId(1))
        .await
        .unwrap();
    journal
        .append_session_batch(writer.fence, Lsn(1), vec![Bytes::from_static(b"first")])
        .await
        .unwrap();

    assert!(matches!(
        journal
            .append_session_batch(writer.fence, Lsn(2), vec![Bytes::from(vec![0; 1024])])
            .await,
        Err(JournalError::Full { floor: Lsn(1) })
    ));
    let checkpoint = CheckpointInstallation {
        operation_id: 1,
        checkpoint_lsn: Lsn(2),
        covered_through_lsn: Lsn(1),
        record: Bytes::from_static(b"covering checkpoint"),
    };
    journal
        .install_checkpoint(writer.fence, checkpoint.clone())
        .await
        .unwrap();
    let inclusion = journal.inclusion(stream, Lsn(2), None).await.unwrap();
    let committed = inclusion.verify(root).unwrap();
    assert_eq!(
        committed.payload_sha256,
        <[u8; 32]>::from(Sha256::digest(&checkpoint.record))
    );

    journal
        .install_checkpoint(writer.fence, checkpoint)
        .await
        .unwrap();
    assert_eq!(
        journal
            .inclusion(stream, Lsn(2), None)
            .await
            .unwrap()
            .verify(root)
            .unwrap(),
        committed
    );
    cluster.shutdown().await.unwrap();
}

fn now_micros() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_micros() as i64
}
