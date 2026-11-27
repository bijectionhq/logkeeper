//! Deterministic reproductions of protocol counterexamples discovered by the
//! TLA+ model in `verification/tla/`.
//!
//! Each test reproduces a real safety or liveness failure against the live
//! keeper implementation and is marked `#[ignore]` as a known failure so the
//! default workspace suite stays green. Run them with:
//!
//! ```sh
//! cargo test --locked --all-features --lib model_counterexamples -- --ignored --nocapture
//! ```

use super::*;
use crate::stream::consensus::{Configuration, keeper::Recovery};

const RECOVERY_WAIT: Duration = Duration::from_secs(30);

async fn wait_configured(journal: &Client, stream: StreamId, voters: [Uuid; 3]) -> Configuration {
    timeout(RECOVERY_WAIT, async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && configuration.voters == voters
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("stream reached expected configuration")
}

/// Counterexample CE-2 (`verification/tla/AbortedReplaceLiveness.cfg`):
///
/// An aborted replacement `[a, b, c] -> [a, b, d]` at revision `r` executes
/// `StageReplica` on `d`, advancing `d`'s durable `Ownership::high` to `r + 1`
/// with `installed = false`. If that replacement aborts before entering joint
/// consensus (e.g., leader `a` crashes), the stream remains at revision `r`
/// (`[a, b, c]`). When `b` and `c` subsequently attempt to replace dead voter
/// `a` with `d` (`[a, b, c] -> [b, c, d]`, still from `source = r`), `d`
/// rejects `StageReplica` in `ownership.rs` (`revision = r + 1 <= self.high`)
/// with `stale()`, and also refuses `Change::Detach` (`!installed` and
/// `r < self.high`). Repair onto `d` is permanently wedged.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "known protocol failure (CE-2): Ownership::high after an aborted replacement permanently blocks subsequent repair onto the same keeper at the same revision"]
async fn an_aborted_replacement_does_not_wedge_subsequent_repair_on_the_same_keeper() {
    let mut cluster = Cluster::start().await;
    // Disable automatic background repair onto extra test keepers (5, 6, 7) so
    // the stream stays on [a, b, c] at revision 0 and we test replacing dead `a`
    // directly onto `d` (as in a 4-keeper cluster).
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.repair_after_secs = 3600;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }

    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(201);
    journal.create(stream, [a, b, c], 4096).await.unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    assert_eq!(initial.voters, [a, b, c]);

    // Ensure `a` leads the stream so stopping `a` aborts the in-flight replace.
    journal.prefer_leader(stream, a).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, a).await);

    // Block replication appends to `d` so `replace([a, b, d])` stages `d` via
    // `StageReplica` (raising `d`'s Ownership::high to `initial.revision + 1`)
    // and then stalls waiting for learner catch-up before `InstallReplica`.
    *cluster.running[&d].engine.reject_append.write() =
        Some(Box::new(move |group, _, _| group == stream));

    let short = cluster.client_within(&cluster.credentials, Duration::from_secs(3));
    let aborted =
        tokio::spawn(async move { short.replace(stream, initial.revision, [a, b, d]).await });

    // Wait until `d` has durably recorded the staged (uninstalled) copy.
    timeout(WAIT, async {
        loop {
            if let Some(book) = cluster.running[&d].engine.disk.ownership(stream)
                && book.high_water() > initial.revision
                && !book.installed()
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("d staged the aborted replacement");

    // Cancel the client call before stopping `a` so it cannot retry the
    // aborted `[a, b, d]` replacement against `b` or `c`, then crash leader `a`
    // before joint consensus so `a`'s server-side replacement task terminates.
    aborted.abort();
    let _ = aborted.await;
    cluster.running.remove(&a).unwrap().stop().await;
    *cluster.running[&d].engine.reject_append.write() = None;

    // Stream is still finalized at `[a, b, c]` with revision `initial.revision`,
    // while `d` retains the uninstalled high-water mark from the aborted stage.
    let current = journal.configuration(stream).await.unwrap();
    assert_eq!(current.voters, [a, b, c]);
    assert_eq!(current.revision, initial.revision);
    let d_own = cluster.running[&d]
        .engine
        .disk
        .ownership(stream)
        .expect("d kept its staged ownership record");
    assert!(d_own.high_water() > current.revision);
    assert!(!d_own.installed());

    // Now `b` and `c` (the live majority) try to replace dead `a` with `d`.
    // Today this fails permanently with `Unavailable` because `d` rejects
    // `StageReplica` for `source = initial.revision` (`revision = r + 1 <=
    // high_water = r + 1` in `ownership.rs`).
    let mut target = [b, c, d];
    target.sort_unstable();
    let replaced = journal.replace(stream, current.revision, target).await;
    assert_eq!(
        replaced.map(|cfg| cfg.voters),
        Ok(target),
        "repairing dead voter `a` onto `d` after an aborted replacement of `c` must succeed"
    );
    cluster.stop_all().await;
}

/// Counterexample CE-3 (`verification/tla/RecoverySingleReturnSnap.cfg`):
///
/// After operator recovery from a lagging survivor `a` (`[a, d, f]`), even if
/// ONLY ONE lost voter `b` returns (`c` stays permanently stopped), a local
/// snapshot persisted on `b` before loss restores `b`'s applied state on
/// startup (`StateMachine::open`). Because `Request::ReadAt` checks only
/// `serves_applied_pages` without a quorum or read barrier, a reader with a
/// cached route (or local-domain preference) to `b` reads the acknowledged-lost
/// record `Lsn(2) = "lost-2"` from `b` before `b` retires, and then reads
/// `Lsn(3) = "recovered-3"` from `[a, d, f]` — observing a mixed history.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "known protocol failure (CE-3): a single returning lost voter with a persisted snapshot serves the lost suffix via ReadAt before retiring, producing a mixed history"]
async fn a_single_returning_lost_voter_with_a_snapshot_cannot_serve_the_lost_suffix() {
    let mut cluster = Cluster::start().await;
    // Order IDs so lost voter `b` precedes survivor `a` in the sorted roster
    // `[b, c, a]`: a reader in `c`'s domain reads Lsn(1) from `c` before loss
    // (caching `[b, c, a]` with no stale socket to `b`). After `c` is lost and
    // `b` restarts, the reader tries `c` (down) and immediately falls over to
    // `b` on a fresh connection.
    let [b, c, a, d] = cluster.ids;
    let f = Uuid::from_u128(6);
    let stream = StreamId(202);
    let journal = cluster.client(&cluster.credentials);

    journal.create(stream, [b, c, a], 1 << 20).await.unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    journal
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"shared-1"))
        .await
        .unwrap();

    // Make `b` leader and ensure `a` and `c` have applied Lsn(1).
    journal.prefer_leader(stream, b).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, b).await);
    for id in [a, c] {
        let group = cluster.group(id, stream).await;
        timeout(WAIT, async {
            while group.state.head() != Ok(Lsn(1)) {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap();
    }

    // Block appends to `a` so Lsn(2) = "lost-2" commits only on `[b, c]`.
    *cluster.running[&a].engine.reject_append.write() = Some(Box::new(move |group, _, req| {
        group == stream && !req.entries.is_empty()
    }));
    journal
        .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"lost-2"))
        .await
        .unwrap();

    // Persist a local snapshot on `b` covering Lsn(2) before `b` is lost.
    let group_b = cluster.group(b, stream).await;
    timeout(WAIT, async {
        while group_b.state.head() != Ok(Lsn(2)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    let b_applied = group_b.state.applied().unwrap();
    group_b.raft.trigger().snapshot().await.unwrap();
    timeout(WAIT, async {
        while !group_b
            .state
            .covered()
            .is_some_and(|cut| cut.index >= b_applied.index)
        {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("b persisted a snapshot covering the lost suffix");

    // `b` fails first; while `[a, c]` still serve rev 0 `[b, c, a]`, a reader
    // in `b`'s domain reads Lsn(1) from `c` and caches route `[b, c, a]` (with
    // no stale pooled socket to `b`).
    cluster.running.remove(&b).unwrap().stop().await;
    let reader = cluster
        .client(&cluster.credentials)
        .with_local_keepers(BTreeSet::from([b]));
    let page1 = reader
        .read(stream, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page1.records,
        vec![(Lsn(1), Bytes::from_static(b"shared-1"))]
    );

    // Then `c` is lost too, and `a` is stopped for offline recovery.
    for id in [c, a] {
        cluster.running.remove(&id).unwrap().stop().await;
    }

    // Offline operator recovery from `a` onto `[a, d, f]`.
    let report = cluster.configs[&a]
        .recover_stream(
            stream,
            Recovery {
                acknowledge_data_loss: true,
                with: Some([d, f]),
                ..Recovery::default()
            },
        )
        .await
        .unwrap();
    assert_eq!(report.head, Lsn(1));

    // Restart `a`, acknowledge recovery, and append post-recovery records.
    cluster.restart(a).await;
    wait_configured(&journal, stream, report.voters).await;
    assert_eq!(journal.acknowledge_recovery(stream).await, Ok(Lsn(1)));
    let new_seal = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    journal
        .append(
            stream,
            new_seal.fence,
            Lsn(2),
            Bytes::from_static(b"recovered-2"),
        )
        .await
        .unwrap();
    journal
        .append(
            stream,
            new_seal.fence,
            Lsn(3),
            Bytes::from_static(b"recovered-3"),
        )
        .await
        .unwrap();

    // Restart ONLY `b` (`c` stays permanently dead). Wait until `b`'s startup
    // finishes reopening the stream group from its persisted snapshot and its
    // application listener is accepting connections.
    cluster.restart(b).await;
    let reopened_b = cluster.group(b, stream).await;
    assert_eq!(reopened_b.state.head(), Ok(Lsn(2)));
    timeout(WAIT, async {
        while journal.replica_generation(stream, b).await.is_err() {
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    })
    .await
    .unwrap();

    let page2 = reader
        .read(stream, Lsn(2), 1, Duration::ZERO)
        .await
        .unwrap();
    let page3 = reader
        .read(stream, Lsn(3), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(
        page3.records,
        vec![(Lsn(3), Bytes::from_static(b"recovered-3"))]
    );
    assert_ne!(
        page2.records,
        vec![(Lsn(2), Bytes::from_static(b"lost-2"))],
        "mixed history observed: single returning lost voter `b` served lost Lsn(2) = \"lost-2\" \
         alongside post-recovery Lsn(3) = \"recovered-3\""
    );
    cluster.stop_all().await;
}

/// Counterexample CE-4 (`verification/tla/RecoveryBothReturn.cfg` and
/// `RecoveryBothReturnLiveness.cfg`):
///
/// After operator recovery from `a` onto `[a, d, f]`, if `a` is later replaced
/// by `g` (yielding a completely healthy recovered roster `[d, f, g]`) and both
/// lost voters `b` and `c` return together:
///   1. `[b, c]` elect a leader of the old configuration `[a, b, c]` and serve
///      the lost suffix `"lost-2"` (and even accept divergent writes under the
///      old fence), violating `NoMixedHistory`.
///   2. Because `a` is no longer in the recovered roster (or stopped) and
///      neither `b` nor `c` knows about `d`, `f`, or `g`, neither receives
///      `EXCLUDED`; the old leader skips `retire_removed` and the old follower
///      keeps refreshing `heard` from its heartbeats, so neither lost voter
///      EVER retires (`LostVotersEventuallyRetire` violated).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "known protocol failure (CE-4): returning lost voters form a permanent split-brain quorum and never retire once the survivor is stopped or replaced"]
async fn returning_lost_voters_retire_and_cannot_form_a_permanent_split_brain_when_survivor_is_replaced()
{
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let f = Uuid::from_u128(6);
    let g = Uuid::from_u128(7);
    let stream = StreamId(203);
    let journal = cluster.client(&cluster.credentials);

    journal.create(stream, [a, b, c], 1 << 20).await.unwrap();
    let old_seal = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap();
    journal
        .append(stream, old_seal.fence, Lsn(1), Bytes::from_static(b"shared-1"))
        .await
        .unwrap();

    // Make `b` leader, wait for `a` to apply Lsn(1), then block `a` so Lsn(2)
    // commits only on `[b, c]`.
    journal.prefer_leader(stream, b).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, b).await);
    let group_a = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while group_a.state.head() != Ok(Lsn(1)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    *cluster.running[&a].engine.reject_append.write() = Some(Box::new(move |group, _, req| {
        group == stream && !req.entries.is_empty()
    }));
    journal
        .append(stream, old_seal.fence, Lsn(2), Bytes::from_static(b"lost-2"))
        .await
        .unwrap();

    let gen_b = journal.replica_generation(stream, b).await.unwrap();
    let gen_c = journal.replica_generation(stream, c).await.unwrap();

    // Stop `b`, `c`, `a` and recover from `a` onto `[a, d, f]`.
    for id in [b, c, a] {
        cluster.running.remove(&id).unwrap().stop().await;
    }
    let report = cluster.configs[&a]
        .recover_stream(
            stream,
            Recovery {
                acknowledge_data_loss: true,
                with: Some([d, f]),
                ..Recovery::default()
            },
        )
        .await
        .unwrap();
    assert_eq!(report.head, Lsn(1));

    cluster.restart(a).await;
    let recovered_cfg = wait_configured(&journal, stream, report.voters).await;
    assert_eq!(journal.acknowledge_recovery(stream).await, Ok(Lsn(1)));
    let new_seal = journal
        .seal(stream, report.epoch, Uuid::from_u128(100))
        .await
        .unwrap();
    journal
        .append(
            stream,
            new_seal.fence,
            Lsn(2),
            Bytes::from_static(b"recovered-2"),
        )
        .await
        .unwrap();

    // Later, survivor `a` is replaced by `g` (healthy 3-voter roster `[d, f, g]`)
    // and stopped before `b` and `c` return.
    let mut final_roster = [d, f, g];
    final_roster.sort_unstable();
    let moved = journal
        .replace(stream, recovered_cfg.revision, final_roster)
        .await
        .unwrap();
    assert_eq!(moved.voters, final_roster);
    cluster.running.remove(&a).unwrap().stop().await;
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));

    // Both lost voters return together after the survivor has been replaced.
    cluster.restart(b).await;
    cluster.restart(c).await;

    // Wait well past `repair_after_secs` (2 s in tests): both lost voters must
    // retire instead of forming a permanent split-brain quorum.
    let retired = timeout(Duration::from_secs(6), async {
        loop {
            let b_gone = journal.replica_generation(stream, b).await != Ok(gen_b);
            let c_gone = journal.replica_generation(stream, c).await != Ok(gen_c);
            if b_gone && c_gone {
                return;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await;
    assert!(
        retired.is_ok(),
        "both returning lost voters failed to retire after survivor `a` was replaced (permanent split-brain quorum)"
    );
    cluster.stop_all().await;
}
