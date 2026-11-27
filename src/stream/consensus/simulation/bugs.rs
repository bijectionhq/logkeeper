//! Minimal failing reproductions of bugs discovered by the randomized
//! consensus fault-injection harness.
//!
//! A test stays `#[ignore]`d until its bug is fixed, then guards the fix.
//! Run the ignored ones with:
//! `cargo test --locked --features stream --lib stream::consensus::simulation::bugs -- --ignored --nocapture`

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use bytes::Bytes;
use journal_contract::{
    Epoch, Identity, Journal, JournalError, Lsn, StreamId,
    conformance::history::{Call, Op, Value, linearizable},
    reference::Limits,
};
use tokio::time::timeout;

use super::{
    super::network::{Lane, RpcFault},
    cluster::{ClusterOptions, READER, SimCluster, WAIT, WRITER_A, WRITER_B},
};

/// Retries a setup call while a loaded machine answers `Unavailable`, for at
/// most 30 s. Only for idempotent calls outside the race under test.
macro_rules! settle {
    ($call:expr) => {{
        let end = tokio::time::Instant::now() + Duration::from_secs(30);
        loop {
            match $call.await {
                Err(journal_contract::JournalError::Unavailable)
                    if tokio::time::Instant::now() < end =>
                {
                    tokio::time::sleep(Duration::from_millis(50)).await
                }
                result => break result,
            }
        }
    }};
}

/// Minimal reproduction of the linearizability bug found on soak seed 24
/// (`Profile::NetworkAndMembership`).
///
/// When `ConsensusJournal::append` (or `Client::append`) sends an `Append`,
/// the leader commits it, and the reply is dropped over the network,
/// `Client::decide` / `retry_unavailable` retries the same request. If a
/// competing writer sealed a higher epoch in between, the retry returns
/// `Err(JournalError::Fenced { current })` — a definitive refusal claiming the
/// append did not take effect — even though Attempt 1 already committed and
/// the competing `Seal` returned that committed LSN. No valid linearization
/// exists for this history.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn bug_repro_append_retry_after_dropped_reply_returns_fenced_after_committing() {
    let options = ClusterOptions {
        park_after_secs: 3600,
        repair_after_secs: 60,
        ..ClusterOptions::default()
    };
    let mut cluster = SimCluster::start(240_001, options.clone()).await;
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let stream = StreamId(240_001);
    let writer_a = cluster.journal(WRITER_A, voters);
    let writer_b = cluster.journal(WRITER_B, voters);
    let id_a = Identity::from_static(WRITER_A);
    let id_b = Identity::from_static(WRITER_B);

    settle!(writer_a.create(stream)).unwrap();
    assert_eq!(settle!(writer_a.seal(stream, Epoch(1))), Ok(Lsn(0)));
    let p1 = Bytes::from_static(b"one");
    assert_eq!(
        settle!(writer_a.append(stream, Epoch(1), Lsn(1), p1.clone())),
        Ok(Lsn(1))
    );

    // Arm a one-shot reply drop with a 400 ms delay on Writer A's next
    // Application RPC: the leader commits Lsn(2) immediately, but Writer A's
    // client receives a dropped reply 400 ms later and retries.
    let armed = Arc::new(AtomicBool::new(true));
    let filter_flag = armed.clone();
    writer_a.client().set_transport_filter(
        uuid::Uuid::from_u128(0x1001),
        Some(Arc::new(move |_, _, lane| {
            if lane == Lane::Application && filter_flag.swap(false, Ordering::SeqCst) {
                RpcFault::DropReply(Duration::from_millis(400))
            } else {
                RpcFault::Allow
            }
        })),
    );

    let p2 = Bytes::from_static(b"two");
    let append_fut = writer_a.append(stream, Epoch(1), Lsn(2), p2.clone());
    let seal_fut = async {
        // Wait until Attempt 1 has committed Lsn(2) on the leader while its
        // reply is being delayed/dropped, then seal Epoch(2) as Writer B.
        tokio::time::sleep(Duration::from_millis(120)).await;
        writer_b.seal(stream, Epoch(2)).await
    };
    let (append_res, seal_res) = tokio::join!(append_fut, seal_fut);
    cluster.stop_all().await;

    let calls = vec![
        Call {
            identity: id_a.clone(),
            op: Op::Create,
            invocation: 0,
            response: 1,
            result: Ok(Value::Unit),
        },
        Call {
            identity: id_a.clone(),
            op: Op::Seal(Epoch(1)),
            invocation: 2,
            response: 3,
            result: Ok(Value::Position(Lsn(0))),
        },
        Call {
            identity: id_a.clone(),
            op: Op::Append(Epoch(1), Lsn(1), p1),
            invocation: 4,
            response: 5,
            result: Ok(Value::Position(Lsn(1))),
        },
        Call {
            identity: id_a,
            op: Op::Append(Epoch(1), Lsn(2), p2),
            invocation: 6,
            response: 9,
            result: append_res.clone().map(Value::Position),
        },
        Call {
            identity: id_b,
            op: Op::Seal(Epoch(2)),
            invocation: 7,
            response: 8,
            result: seal_res.clone().map(Value::Position),
        },
    ];
    let limits = Limits {
        max_record_bytes: options.max_record_bytes,
        stream_quota_bytes: options.quota_bytes,
    };
    assert!(
        linearizable(&calls, limits),
        "linearizability violated: Append(Epoch(1), Lsn(2)) returned {append_res:?} \
         while concurrent Seal(Epoch(2)) returned {seal_res:?}"
    );
}

/// Minimal reproduction of the zombie-replica bug found on soak seed 14
/// (`Profile::StorageAndCrash`).
///
/// When a keeper's available disk space temporarily drops below
/// `PROTOCOL_FLOOR` (`Space::set_available(0)`), a `Vote` or `Blank` control
/// write fails with `StorageFull`, which OpenRaft treats as a fatal
/// `StorageError` and terminates the stream's `RaftCore`. Because the WAL
/// thread itself did not fail, `Disk::healthy()` and `StateMachine::healthy()`
/// remain `true` and `KeeperStatus` still reports `replica == Some(true)` once
/// disk space returns. The voter never replicates again and automatic repair
/// never replaces it, causing permanent cross-voter divergence.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn bug_repro_zero_disk_space_leaves_voter_as_zombie_replica() {
    let options = ClusterOptions {
        park_after_secs: 3600,
        repair_after_secs: 60,
        ..ClusterOptions::default()
    };
    let mut cluster = SimCluster::start(140_001, options).await;
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let stream = StreamId(140_001);
    let writer = cluster.journal(WRITER_A, voters);

    settle!(writer.create(stream)).unwrap();
    assert_eq!(settle!(writer.seal(stream, Epoch(1))), Ok(Lsn(0)));
    assert_eq!(
        settle!(writer.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"one"))),
        Ok(Lsn(1))
    );

    let leader = cluster.leader(stream).await.expect("stream has a leader");
    // Drop available space to 0 (below PROTOCOL_FLOOR). E5 sheds leadership to
    // a follower, whose new-term Vote / Blank entry fails with StorageFull on
    // `leader` and kills its OpenRaft RaftCore.
    cluster.set_disk_zero(leader, true);
    let _ = timeout(WAIT, async {
        while cluster
            .leader(stream)
            .await
            .is_none_or(|current| current == leader)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await;

    assert_eq!(
        settle!(writer.append(stream, Epoch(1), Lsn(2), Bytes::from_static(b"two"))),
        Ok(Lsn(2))
    );
    // Disk space recovers.
    cluster.set_disk_zero(leader, false);
    let status = cluster
        .probe_client()
        .keeper_status(leader, stream)
        .await
        .unwrap();
    let converged = cluster
        .wait_converged(stream, &voters, Duration::from_secs(6))
        .await;
    cluster.stop_all().await;

    assert!(
        converged.is_ok(),
        "voter {leader} became a permanent zombie replica after transient disk-full \
         (KeeperStatus still reported accepting={}, replica={:?}): {:?}",
        status.accepting,
        status.replica,
        converged.err(),
    );
}

/// Minimal reproduction of the post-recovery split-brain head regression found
/// on soak seed 16 (`Profile::OperatorRecovery`), sharpening design-doc
/// item #13 (durable fencing of keepers lost in a recovery).
///
/// After `recover-stream` replaces two lost voters `[b, c]` with `[d, e]` and
/// post-recovery writes advance the stream to `Lsn(5)`, restarting both lost
/// voters simultaneously and crashing survivor `a` before `[b, c]` receive
/// `EXCLUDED` allows `[b, c]` to form a permanent quorum of the old
/// configuration `[a, b, c]`. A client holding a cached route to `[a, b, c]`
/// then observes `head() == Lsn(3)` after `Lsn(5)` was already acknowledged.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "reproduces post-recovery split-brain residual risk found on soak seed 16"]
async fn bug_repro_simultaneous_lost_voter_return_and_survivor_crash_regresses_head() {
    let options = ClusterOptions {
        park_after_secs: 3600,
        repair_after_secs: 60,
        ..ClusterOptions::default()
    };
    let mut cluster = SimCluster::start(160_001, options).await;
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let [a, b, c] = voters;
    let stream = StreamId(160_001);
    let writer_a = cluster.journal(WRITER_A, voters);
    let writer_b = cluster.journal(WRITER_B, voters);
    let reader = cluster.journal(READER, voters);

    settle!(writer_a.create(stream)).unwrap();
    assert_eq!(settle!(writer_a.seal(stream, Epoch(1))), Ok(Lsn(0)));
    for at in 1..=3 {
        assert_eq!(
            settle!(writer_a.append(stream, Epoch(1), Lsn(at), Bytes::from(format!("r{at}")))),
            Ok(Lsn(at))
        );
    }
    // Reader caches the pre-recovery route [a, b, c].
    assert_eq!(settle!(reader.head(stream)), Ok(Lsn(3)));

    // Lose b and c; recover stream offline on survivor a.
    cluster.crash(b).await;
    cluster.crash(c).await;
    let report = cluster
        .recover_stream_offline(a, [b, c], stream)
        .await
        .unwrap();
    let probe = cluster.probe_client();
    timeout(WAIT, async {
        loop {
            if let Ok(cfg) = probe.configuration(stream).await
                && cfg.voters == report.voters
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .unwrap();

    // Acknowledge recovery, seal, and commit Lsn(4) and Lsn(5) on recovered roster.
    assert!(writer_b.acknowledge_recovery(stream).await.is_ok());
    let next_epoch = Epoch(report.epoch.0 + 1);
    assert!(writer_b.seal(stream, next_epoch).await.is_ok());
    assert_eq!(
        settle!(writer_b.append(stream, next_epoch, Lsn(4), Bytes::from_static(b"after-4"))),
        Ok(Lsn(4))
    );
    assert_eq!(
        settle!(writer_b.append(stream, next_epoch, Lsn(5), Bytes::from_static(b"after-5"))),
        Ok(Lsn(5))
    );

    // Both lost voters return together, and survivor a crashes before they
    // contact it to receive EXCLUDED.
    cluster.crash(a).await;
    cluster.restart(b).await;
    cluster.restart(c).await;
    tokio::time::sleep(Duration::from_millis(800)).await;

    let observed = reader.head(stream).await;
    cluster.stop_all().await;

    assert!(
        observed.as_ref().is_ok_and(|&h| h >= Lsn(5)) || observed.is_err(),
        "post-recovery head regressed: reader with cached route observed {observed:?} \
         after Lsn(5) was committed on recovered roster {:?}",
        report.voters
    );
}

/// Minimal reproduction of the contract-conformance bug found on soak seed 25
/// (`Profile::ReplicatedCatalog`).
///
/// The `journal_contract` reference (`contract/src/state.rs:109-116`) and
/// linearizability checker (`contract/src/conformance/history.rs:356`) require
/// an idempotent retry at `at <= head` to match both the committing `Epoch`
/// and the `payload` bytes. Because `src/stream/consensus/state.rs` does not
/// record the committing epoch per retained record, a new writer under
/// `Epoch(2)` appending identical bytes at an LSN written under `Epoch(1)`
/// receives `Ok(at)` instead of `Err(JournalError::Conflict { head })`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn bug_repro_cross_epoch_identical_payload_retry_violates_contract() {
    let options = ClusterOptions {
        park_after_secs: 3600,
        repair_after_secs: 60,
        ..ClusterOptions::default()
    };
    let mut cluster = SimCluster::start(250_001, options.clone()).await;
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let stream = StreamId(250_001);
    let writer_a = cluster.journal(WRITER_A, voters);
    let writer_b = cluster.journal(WRITER_B, voters);
    let id_a = Identity::from_static(WRITER_A);
    let id_b = Identity::from_static(WRITER_B);

    settle!(writer_a.create(stream)).unwrap();
    assert_eq!(settle!(writer_a.seal(stream, Epoch(1))), Ok(Lsn(0)));
    let payload = Bytes::from_static(b"same-bytes");
    assert_eq!(
        settle!(writer_a.append(stream, Epoch(1), Lsn(1), payload.clone())),
        Ok(Lsn(1))
    );
    assert_eq!(settle!(writer_b.seal(stream, Epoch(2))), Ok(Lsn(1)));
    let cross_epoch = writer_b
        .append(stream, Epoch(2), Lsn(1), payload.clone())
        .await;
    cluster.stop_all().await;

    let calls = vec![
        Call {
            identity: id_a.clone(),
            op: Op::Create,
            invocation: 0,
            response: 1,
            result: Ok(Value::Unit),
        },
        Call {
            identity: id_a.clone(),
            op: Op::Seal(Epoch(1)),
            invocation: 2,
            response: 3,
            result: Ok(Value::Position(Lsn(0))),
        },
        Call {
            identity: id_a,
            op: Op::Append(Epoch(1), Lsn(1), payload.clone()),
            invocation: 4,
            response: 5,
            result: Ok(Value::Position(Lsn(1))),
        },
        Call {
            identity: id_b.clone(),
            op: Op::Seal(Epoch(2)),
            invocation: 6,
            response: 7,
            result: Ok(Value::Position(Lsn(1))),
        },
        Call {
            identity: id_b,
            op: Op::Append(Epoch(2), Lsn(1), payload),
            invocation: 8,
            response: 9,
            result: cross_epoch.clone().map(Value::Position),
        },
    ];
    let limits = Limits {
        max_record_bytes: options.max_record_bytes,
        stream_quota_bytes: options.quota_bytes,
    };
    assert!(
        linearizable(&calls, limits),
        "contract violated: cross-epoch append of identical bytes at Lsn(1) under Epoch(2) \
         returned {cross_epoch:?} instead of Err(Conflict {{ head: Lsn(1) }})"
    );
}

/// The epochs of retained records survive a local snapshot and a restart of
/// every keeper: the same bytes a writer of an earlier epoch committed still
/// conflict, and the current writer's identical retry still succeeds.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn record_epochs_survive_a_snapshot_and_a_full_restart() {
    let options = ClusterOptions {
        park_after_secs: 3600,
        repair_after_secs: 60,
        quota_bytes: 4 * 1024 * 1024,
        ..ClusterOptions::default()
    };
    let mut cluster = SimCluster::start(250_002, options).await;
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let stream = StreamId(250_002);
    let writer_a = cluster.journal(WRITER_A, voters);
    let writer_b = cluster.journal(WRITER_B, voters);
    let record = |at: u64| Bytes::from(format!("record-{at}"));

    settle!(writer_a.create(stream)).unwrap();
    assert_eq!(settle!(writer_a.seal(stream, Epoch(1))), Ok(Lsn(0)));
    for at in 1..=100 {
        assert_eq!(
            settle!(writer_a.append(stream, Epoch(1), Lsn(at), record(at))),
            Ok(Lsn(at))
        );
    }
    assert_eq!(settle!(writer_b.seal(stream, Epoch(2))), Ok(Lsn(100)));
    // Enough entries past the 128-entry snapshot policy that every voter
    // reopens from a local snapshot.
    for at in 101..=300 {
        assert_eq!(
            settle!(writer_b.append(stream, Epoch(2), Lsn(at), record(at))),
            Ok(Lsn(at))
        );
    }
    for id in voters {
        cluster.stop_graceful(id).await;
    }
    cluster.restart_all_stopped().await;

    let earlier = settle!(writer_b.append(stream, Epoch(2), Lsn(50), record(50)));
    let retry = settle!(writer_b.append(stream, Epoch(2), Lsn(250), record(250)));
    cluster.stop_all().await;
    assert_eq!(earlier, Err(JournalError::Conflict { head: Lsn(300) }));
    assert_eq!(retry, Ok(Lsn(250)));
}
