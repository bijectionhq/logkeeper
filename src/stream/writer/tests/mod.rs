mod keeper;

use std::{sync::Arc, time::Duration};

use bytes::Bytes;
use futures::{future::join_all, poll};
use journal_contract::{Epoch, Identity, Journal, JournalError, Lsn, StreamId};

use super::{SealPolicy, Writer};
use keeper::{Fault, Gate, KEEPERS, Kind, Network};

const STREAM: StreamId = StreamId(42);
const E1: Epoch = Epoch(1);
const E2: Epoch = Epoch(2);
const E3: Epoch = Epoch(3);
const WAIT: Duration = Duration::from_secs(2);

fn writer(network: &Arc<Network>, identity: u128) -> Writer {
    Writer::new(network.client(identity), KEEPERS).unwrap()
}

async fn started() -> (Arc<Network>, Writer) {
    let network = Arc::new(Network::default());
    let writer = writer(&network, 1);
    writer.create(STREAM).await.unwrap();
    network
        .until(|| {
            KEEPERS[..3]
                .iter()
                .all(|&id| network.view(id, STREAM).is_some())
        })
        .await;
    assert_eq!(writer.seal(STREAM, E1).await, Ok(Lsn(0)));
    network
        .until(|| {
            KEEPERS[..3]
                .iter()
                .all(|&id| network.view(id, STREAM).unwrap().synced == Some(E1))
        })
        .await;
    (network, writer)
}

fn record(value: &'static str) -> Bytes {
    Bytes::from_static(value.as_bytes())
}

#[tokio::test(start_paused = true)]
async fn different_payload_after_uncertain_append_has_no_decided_conflict() {
    let (network, writer) = started().await;
    let [survivor, second, third] = KEEPERS[..3].try_into().unwrap();
    network.down(second, true);
    network.down(third, true);

    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("first")).await,
        Err(JournalError::Unavailable)
    );
    network
        .until(|| network.view(survivor, STREAM).unwrap().tail == Lsn(1))
        .await;
    assert_eq!(network.view(survivor, STREAM).unwrap().head, Lsn(0));
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("different")).await,
        Err(JournalError::Unavailable),
        "an unresolved append cannot report a decided conflict"
    );

    network.down(second, false);
    network.down(third, false);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("first")).await,
        Ok(Lsn(1))
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("different")).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
}

#[tokio::test(start_paused = true)]
async fn publishing_on_first_accept_would_expose_a_history_takeover_can_discard() {
    let (network, old) = started().await;
    let [only, left, right] = KEEPERS[..3].try_into().unwrap();
    network.down(left, true);
    network.down(right, true);
    assert_eq!(
        old.append(STREAM, E1, Lsn(1), record("unselected")).await,
        Err(JournalError::Unavailable)
    );
    network
        .until(|| network.view(only, STREAM).unwrap().tail == Lsn(1))
        .await;
    let reader = writer(&network, 9);
    let observed = reader
        .read(STREAM, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert!(
        observed.records.is_empty(),
        "single-keeper read exposed an unchosen record"
    );

    network.down(only, true);
    network.down(left, false);
    network.down(right, false);
    let successor = writer(&network, 2);
    assert_eq!(successor.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        successor.append(STREAM, E2, Lsn(1), record("chosen")).await,
        Ok(Lsn(1))
    );
    let observed = reader
        .read(STREAM, Lsn(1), 1, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(observed.records, [(Lsn(1), record("chosen"))]);
}

#[tokio::test(start_paused = true)]
async fn stale_trim_checks_the_fence_before_reporting_a_local_head_conflict() {
    let (network, stale) = started().await;
    let successor = writer(&network, 2);
    assert_eq!(successor.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        successor.append(STREAM, E2, Lsn(1), record("first")).await,
        Ok(Lsn(1))
    );
    assert_eq!(
        stale.trim(STREAM, E1, Lsn(1)).await,
        Err(JournalError::Fenced { current: E2 }),
        "a stale writer cannot report a conflict at its old head"
    );
}

#[tokio::test(start_paused = true)]
async fn trim_conflict_uses_writer_authorization() {
    let (network, writer) = started().await;
    assert_eq!(
        writer.trim(STREAM, E1, Lsn(1)).await,
        Err(JournalError::Conflict { head: Lsn(0) })
    );
    assert!(
        network.calls(Kind::Check).is_empty(),
        "a trim bound must not require client authorization"
    );
}

#[tokio::test(start_paused = true)]
async fn zombie_writer_is_fenced_and_recovery_contains_the_prior_commit() {
    let (network, zombie) = started().await;
    assert_eq!(
        zombie.append(STREAM, E1, Lsn(1), record("prior")).await,
        Ok(Lsn(1))
    );
    let successor = writer(&network, 2);
    assert_eq!(successor.seal(STREAM, E2).await, Ok(Lsn(1)));
    assert_eq!(
        zombie.append(STREAM, E1, Lsn(2), record("zombie")).await,
        Err(JournalError::Fenced { current: E2 })
    );
    assert_eq!(zombie.head(STREAM).await, Ok(Lsn(1)));
    assert_eq!(
        successor.append(STREAM, E2, Lsn(2), record("new")).await,
        Ok(Lsn(2))
    );
    let page = successor.read(STREAM, Lsn(1), 2, WAIT).await.unwrap();
    assert_eq!(page.records[0], (Lsn(1), record("prior")));
}

#[tokio::test(start_paused = true)]
async fn two_identities_at_the_same_epoch_cannot_both_seal() {
    let (network, _) = started().await;
    let a = writer(&network, 2);
    let b = writer(&network, 3);
    let (a_seal, b_seal) = tokio::join!(a.seal(STREAM, E2), b.seal(STREAM, E2));
    assert_ne!(
        a_seal.is_ok(),
        b_seal.is_ok(),
        "one identity must win the seal race"
    );
    let (winner, loser) = if a_seal.is_ok() { (&a, &b) } else { (&b, &a) };
    assert_eq!(
        winner.append(STREAM, E2, Lsn(1), record("chosen")).await,
        Ok(Lsn(1))
    );
    assert_eq!(
        loser.append(STREAM, E2, Lsn(1), record("other")).await,
        Err(JournalError::Fenced { current: E2 })
    );
}

#[tokio::test(start_paused = true)]
async fn a_new_writer_with_the_same_identity_cannot_reseal() {
    let (network, original) = started().await;
    assert_eq!(original.clone().seal(STREAM, E1).await, Ok(Lsn(0)));
    drop(original);

    let restarted = writer(&network, 1);
    assert_eq!(
        restarted.seal(STREAM, E1).await,
        Err(JournalError::Fenced { current: E1 }),
        "independent writer re-elected an existing epoch"
    );
    assert_eq!(restarted.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        restarted
            .append(STREAM, E2, Lsn(1), record("new epoch"))
            .await,
        Ok(Lsn(1))
    );
}

#[tokio::test(start_paused = true)]
async fn head_and_reseal_accept_the_winning_identity_amid_a_split_promise() {
    use crate::stream::wire::{Reply, Request, Transport};

    let (network, _) = started().await;
    let ensemble = KEEPERS[..3].try_into().unwrap();
    let losing = network
        .client(90)
        .call(
            KEEPERS[0],
            Request::Seal {
                stream: STREAM,
                ensemble,
                epoch: E2,
                proposal: 1,
            },
        )
        .await
        .unwrap();
    assert!(matches!(losing, Reply::Sealed(_)));
    let winner = writer(&network, 2);
    assert_eq!(winner.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        winner.append(STREAM, E2, Lsn(1), record("winner")).await,
        Ok(Lsn(1))
    );
    let observer = writer(&network, 3);
    assert_eq!(
        observer.head(STREAM).await,
        Ok(Lsn(1)),
        "a minority promise must not mask the winning identity"
    );
    assert_eq!(
        winner.seal(STREAM, E2).await,
        Ok(Lsn(1)),
        "reseal ignores a minority promise"
    );
}

#[tokio::test(start_paused = true)]
async fn recovery_discards_a_longer_tail_from_a_lower_synced_epoch() {
    let (network, first) = started().await;
    first
        .append(STREAM, E1, Lsn(1), record("prefix"))
        .await
        .unwrap();
    network
        .until(|| {
            KEEPERS[..3]
                .iter()
                .all(|&id| network.view(id, STREAM).unwrap().tail == Lsn(1))
        })
        .await;
    network.down(KEEPERS[0], true);
    network.down(KEEPERS[1], true);
    assert_eq!(
        first.append(STREAM, E1, Lsn(2), record("minority")).await,
        Err(JournalError::Unavailable)
    );
    network
        .until(|| network.view(KEEPERS[2], STREAM).unwrap().tail == Lsn(2))
        .await;
    network.down(KEEPERS[0], false);
    network.down(KEEPERS[1], false);
    network.down(KEEPERS[2], true);
    let second = writer(&network, 2);
    assert_eq!(second.seal(STREAM, E2).await, Ok(Lsn(1)));
    network.down(KEEPERS[1], true);
    network.down(KEEPERS[2], false);
    let third = writer(&network, 3);
    assert_eq!(third.seal(STREAM, E3).await, Ok(Lsn(1)));
    assert_eq!(network.view(KEEPERS[2], STREAM).unwrap().tail, Lsn(1));
    third
        .append(STREAM, E3, Lsn(2), record("replacement"))
        .await
        .unwrap();
    let page = third.read(STREAM, Lsn(2), 1, WAIT).await.unwrap();
    assert_eq!(page.records, [(Lsn(2), record("replacement"))]);
}

#[tokio::test(start_paused = true)]
async fn recovery_fetches_a_durable_tail_before_any_keeper_advertises_commit() {
    let (network, first) = started().await;
    network.down(KEEPERS[2], true);
    for keeper in KEEPERS[..2].iter().copied() {
        network.fault(keeper, Kind::Append, Fault::LoseReply);
    }
    assert_eq!(
        first.append(STREAM, E1, Lsn(1), record("unknown")).await,
        Err(JournalError::Unavailable)
    );
    network
        .until(|| {
            KEEPERS[..2]
                .iter()
                .all(|&id| network.view(id, STREAM).unwrap().tail == Lsn(1))
        })
        .await;
    assert_eq!(
        first
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        []
    );
    network.down(KEEPERS[1], true);
    network.down(KEEPERS[2], false);
    let next = writer(&network, 2);
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(1)));
    assert!(!network.calls(Kind::Recover).is_empty());
    assert_eq!(
        next.read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        [(Lsn(1), record("unknown"))]
    );
}

#[tokio::test(start_paused = true)]
async fn append_retry_after_lost_replies_is_exact() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    for keeper in KEEPERS[..2].iter().copied() {
        network.fault(keeper, Kind::Append, Fault::LoseReply);
    }
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("once")).await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("changed")).await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("once")).await,
        Ok(Lsn(1))
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("once")).await,
        Ok(Lsn(1))
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("changed")).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(3), record("gap")).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
}

#[tokio::test(start_paused = true)]
async fn committed_retry_does_not_send_unassigned_bytes() {
    let (network, writer) = started().await;
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("chosen")).await,
        Ok(Lsn(1))
    );
    network
        .until(|| {
            KEEPERS[..3]
                .iter()
                .all(|&keeper| network.view(keeper, STREAM).unwrap().tail == Lsn(1))
        })
        .await;
    let sent = network.calls(Kind::Append);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("different")).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
    assert_eq!(
        network.calls(Kind::Append),
        sent,
        "committed retry sent unassigned bytes"
    );
}

#[tokio::test(start_paused = true)]
async fn conflicting_retry_cannot_fill_a_lagging_keeper() {
    let (network, writer) = started().await;
    let lagging = KEEPERS[2];
    network.down(lagging, true);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("chosen")).await,
        Ok(Lsn(1))
    );
    network.down(lagging, false);

    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("other")).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
    // The background lane may have already repaired the keeper. A retry must
    // never let that keeper publish the conflicting payload at this position.
    let reply = crate::stream::wire::Transport::call(
        &*network.client(1),
        lagging,
        crate::stream::wire::Request::Read {
            stream: STREAM,
            from: Lsn(1),
            max: 1,
            wait_ms: 0,
        },
    )
    .await
    .unwrap();
    let crate::stream::wire::Reply::Records { records, .. } = reply else {
        panic!("expected a page, got {reply:?}");
    };
    assert!(
        records.is_empty() || records == [(Lsn(1), record("chosen"))],
        "conflicting retry published different bytes on a lagging keeper"
    );
}

#[tokio::test(start_paused = true)]
async fn seal_retries_lost_promises_and_completed_syncs_at_the_same_epoch() {
    let (network, _) = started().await;
    let next = writer(&network, 2);
    network.down(KEEPERS[2], true);
    for keeper in KEEPERS[..2].iter().copied() {
        network.fault(keeper, Kind::Seal, Fault::LoseReply);
    }
    assert_eq!(next.seal(STREAM, E2).await, Err(JournalError::Unavailable));
    for keeper in KEEPERS[..2].iter().copied() {
        network.fault(keeper, Kind::Sync, Fault::LoseReply);
    }
    assert_eq!(next.seal(STREAM, E2).await, Err(JournalError::Unavailable));
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        next.append(STREAM, E2, Lsn(1), record("once")).await,
        Ok(Lsn(1))
    );
}

#[tokio::test(start_paused = true)]
async fn one_keeper_down_requires_both_survivors_to_acknowledge() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    let gate = Gate::new();
    network.fault(KEEPERS[1], Kind::Append, Fault::HoldReply(gate.clone()));
    let pending = writer.append(STREAM, E1, Lsn(1), record("duplex"));
    tokio::pin!(pending);
    assert!(poll!(&mut pending).is_pending());
    gate.reached().await;
    network
        .until(|| network.view(KEEPERS[0], STREAM).unwrap().tail == Lsn(1))
        .await;
    assert!(
        poll!(&mut pending).is_pending(),
        "one acknowledgement cannot head"
    );
    gate.release();
    assert_eq!(pending.await, Ok(Lsn(1)));
    network.down(KEEPERS[1], true);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(2), record("minority")).await,
        Err(JournalError::Unavailable)
    );
}

#[tokio::test(start_paused = true)]
async fn append_pipeline_advances_without_waiting_for_a_slow_third_keeper() {
    let (network, writer) = started().await;
    let gate = Gate::new();
    network.fault(KEEPERS[2], Kind::Append, Fault::HoldReply(gate.clone()));
    let calls = async {
        tokio::join!(
            writer.append(STREAM, E1, Lsn(1), record("first")),
            writer.append(STREAM, E1, Lsn(2), record("second"))
        )
    };
    assert_eq!(
        tokio::time::timeout(WAIT, calls).await.unwrap(),
        (Ok(Lsn(1)), Ok(Lsn(2)))
    );
    gate.reached().await;
    // Both pending records travel in the slow keeper's single held append.
    assert_eq!(network.view(KEEPERS[2], STREAM).unwrap().tail, Lsn(2));
    gate.release();
    network
        .until(|| network.view(KEEPERS[2], STREAM).unwrap().tail == Lsn(2))
        .await;
}

#[tokio::test(start_paused = true)]
async fn heads_waiting_on_the_same_stream_batch_into_one_fresh_round() {
    let (network, writer) = started().await;
    let start = network.calls(Kind::Check).len();
    let results = join_all((0..32).map(|_| writer.head(STREAM))).await;
    assert_eq!(results, vec![Ok(Lsn(0)); 32]);
    let checks = network.calls(Kind::Check);
    assert!(
        (2..=3).contains(&(checks.len() - start)),
        "one Check per keeper"
    );
    writer
        .append(STREAM, E1, Lsn(1), record("frontier"))
        .await
        .unwrap();
    assert_eq!(writer.head(STREAM).await, Ok(Lsn(1)));
    assert!(network.calls(Kind::Check).len() > checks.len());
}

#[tokio::test(start_paused = true)]
async fn head_joining_after_a_round_opens_gets_a_new_round() {
    let (network, writer) = started().await;
    let gate = Gate::new();
    network.down(KEEPERS[2], true);
    network.fault(KEEPERS[0], Kind::Check, Fault::HoldReply(gate.clone()));
    let old = tokio::spawn({
        let writer = writer.clone();
        async move { writer.head(STREAM).await }
    });
    gate.reached().await;
    writer
        .append(STREAM, E1, Lsn(1), record("after old round"))
        .await
        .unwrap();
    assert_eq!(
        tokio::time::timeout(WAIT, writer.head(STREAM))
            .await
            .unwrap(),
        Ok(Lsn(1))
    );
    gate.release();
    assert!(old.await.unwrap().is_ok());
}

#[tokio::test(start_paused = true)]
async fn observer_head_requires_quorum_commit_coverage() {
    let (network, writer) = started().await;
    let observer = self::writer(&network, 9);
    network.down(KEEPERS[2], true);
    let gate = Gate::new();
    network.fault(KEEPERS[1], Kind::Append, Fault::HoldReply(gate.clone()));
    let pending = writer.append(STREAM, E1, Lsn(1), record("tail"));
    tokio::pin!(pending);
    assert!(poll!(&mut pending).is_pending());
    gate.reached().await;
    assert_eq!(observer.head(STREAM).await, Err(JournalError::Unavailable));
    gate.release();
    assert_eq!(pending.await, Ok(Lsn(1)));
    network
        .until(|| {
            KEEPERS[..2]
                .iter()
                .all(|&id| network.view(id, STREAM).unwrap().head == Lsn(1))
        })
        .await;
    assert_eq!(observer.head(STREAM).await, Ok(Lsn(1)));
}

#[tokio::test(start_paused = true)]
async fn read_long_poll_wakes_when_the_keeper_publishes_head() {
    let (network, writer) = started().await;
    let reader = self::writer(&network, 9);
    network.down(KEEPERS[2], true);
    let poll = reader.read(STREAM, Lsn(1), 1, WAIT);
    tokio::pin!(poll);
    assert!(poll!(&mut poll).is_pending());
    writer
        .append(STREAM, E1, Lsn(1), record("wake"))
        .await
        .unwrap();
    let page = tokio::time::timeout(WAIT / 2, &mut poll)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(page.records, [(Lsn(1), record("wake"))]);
    assert_eq!((page.floor, page.head), (Lsn(1), Lsn(1)));
    assert_eq!(
        writer.trim(STREAM, E1, Lsn(2)).await,
        Err(JournalError::Conflict { head: Lsn(1) })
    );
    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    network.down(KEEPERS[0], true);
    network.down(KEEPERS[2], false);
    assert_eq!(
        reader.read(STREAM, Lsn(1), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(2) })
    );
    let empty = reader
        .read(STREAM, Lsn(2), 8, Duration::from_millis(10))
        .await
        .unwrap();
    assert_eq!(
        (empty.floor, empty.head, empty.records),
        (Lsn(2), Lsn(1), vec![])
    );
}

#[tokio::test(start_paused = true)]
async fn single_keeper_read_serves_committed_records_below_a_remote_floor() {
    let (network, writer) = started().await;
    writer
        .append(STREAM, E1, Lsn(1), record("retained"))
        .await
        .unwrap();
    let [first, second, third] = KEEPERS[..3].try_into().unwrap();
    network
        .until(|| {
            [first, second, third]
                .into_iter()
                .all(|keeper| network.view(keeper, STREAM).unwrap().head == Lsn(1))
        })
        .await;
    let reader = self::writer(&network, 9);
    let reads = network.calls(Kind::Read).len();
    assert_eq!(
        reader
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .head,
        Lsn(1)
    );
    assert_eq!(
        &network.calls(Kind::Read)[reads..],
        &[first],
        "read must prefer the nearest keeper"
    );
    network.down(third, true);
    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    network.down(first, true);
    network.down(third, false);

    let checks = network.calls(Kind::Check);
    assert_eq!(network.view(second, STREAM).unwrap().floor, Lsn(2));
    let page = reader
        .read(STREAM, Lsn(1), 1, Duration::ZERO)
        .await
        .expect("a reachable keeper still retains the committed record");
    assert_eq!(
        (page.floor, page.head, page.records),
        (Lsn(1), Lsn(1), vec![(Lsn(1), record("retained"))])
    );
    assert_eq!(
        network.calls(Kind::Check),
        checks,
        "read performed a quorum check"
    );

    network.down(second, true);
    assert_eq!(
        reader
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .head,
        Lsn(1),
    );
    assert_eq!(reader.head(STREAM).await, Err(JournalError::Unavailable));
}

#[tokio::test(start_paused = true)]
async fn stale_routes_can_read_committed_records_after_a_replacement_trim() {
    use crate::stream::keeper::{Sweep, sweep_idle};

    let (network, old_writer) = started().await;
    old_writer
        .append(STREAM, E1, Lsn(1), record("discard"))
        .await
        .unwrap();
    let [first, second, retired, learner] = KEEPERS;
    let old = [first, second, retired];
    let new = [first, second, learner];
    let plan = Sweep::new(STREAM, old, [first, second], learner, E2);
    let result = sweep_idle(&*network.client(2), [plan]).await;
    assert!(result[0].1.is_ok(), "{result:?}");

    let new_writer = writer(&network, 3);
    new_writer.bind_ensemble(STREAM, new).unwrap();
    assert_eq!(new_writer.seal(STREAM, E3).await, Ok(Lsn(1)));
    network
        .until(|| network.view(learner, STREAM).unwrap().synced == Some(E3))
        .await;
    network.down(second, true);
    new_writer.trim(STREAM, E3, Lsn(1)).await.unwrap();
    network.down(first, true);
    network.down(second, false);
    assert_eq!(network.view(second, STREAM).unwrap().floor, Lsn(1));
    assert_eq!(network.view(retired, STREAM).unwrap().floor, Lsn(1));

    assert_eq!(
        writer(&network, 4)
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        [(Lsn(1), record("discard"))],
    );
    let reader = writer(&network, 5);
    reader.bind_ensemble(STREAM, new).unwrap();
    assert_eq!(
        reader
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        [(Lsn(1), record("discard"))],
    );
    network.down(second, true);
    assert_eq!(
        reader.read(STREAM, Lsn(1), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(2) }),
    );
}

#[tokio::test(start_paused = true)]
async fn an_append_reply_waits_for_quorum_commit_visibility() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    let gate = Gate::new();
    network.fault(KEEPERS[1], Kind::Publish, Fault::HoldReply(gate.clone()));
    let append = writer.append(STREAM, E1, Lsn(1), record("published"));
    tokio::pin!(append);
    assert!(poll!(&mut append).is_pending());
    gate.reached().await;
    assert!(
        poll!(&mut append).is_pending(),
        "append reply requires quorum head visibility"
    );
    gate.release();
    assert_eq!(append.await, Ok(Lsn(1)));
}

#[tokio::test(start_paused = true)]
async fn head_and_trim_wait_for_a_sampled_append_to_be_visible() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    let gate = Gate::new();
    network.fault(KEEPERS[1], Kind::Publish, Fault::HoldReply(gate.clone()));
    let append = writer.append(STREAM, E1, Lsn(1), record("visible"));
    tokio::pin!(append);
    assert!(poll!(&mut append).is_pending());
    gate.reached().await;

    let head = writer.head(STREAM);
    let trim = writer.trim(STREAM, E1, Lsn(1));
    tokio::pin!(head, trim);
    let quiet = Duration::from_millis(25);
    assert!(
        tokio::time::timeout(quiet, &mut head).await.is_err(),
        "head must wait for quorum head visibility"
    );
    assert!(
        tokio::time::timeout(quiet, &mut trim).await.is_err(),
        "trim must wait for quorum head visibility"
    );
    gate.release();
    assert_eq!(head.await, Ok(Lsn(1)));
    assert_eq!(trim.await, Ok(()));
    assert_eq!(append.await, Ok(Lsn(1)));
}

#[tokio::test(start_paused = true)]
async fn a_fenced_publication_leaves_a_chosen_append_outcome_unknown() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    let gates = [Gate::new(), Gate::new()];
    for (&keeper, gate) in KEEPERS.iter().zip(&gates) {
        network.fault(keeper, Kind::Append, Fault::HoldReply(gate.clone()));
    }
    let append = writer.append(STREAM, E1, Lsn(1), record("chosen before fence"));
    tokio::pin!(append);
    assert!(poll!(&mut append).is_pending());
    for gate in &gates {
        gate.reached().await;
    }
    let successor = self::writer(&network, 2);
    assert_eq!(successor.seal(STREAM, E2).await, Ok(Lsn(1)));
    for gate in &gates {
        gate.release();
    }
    assert_eq!(
        append.await,
        Err(JournalError::Unavailable),
        "a publication fence does not rule out the already chosen append"
    );
    assert_eq!(
        successor
            .read(STREAM, Lsn(1), 1, Duration::ZERO)
            .await
            .unwrap()
            .records,
        [(Lsn(1), record("chosen before fence"))]
    );
}

#[tokio::test(start_paused = true)]
async fn create_uses_url_order_or_explicit_ensemble_and_delete_is_terminal() {
    let network = Arc::new(Network::default());
    let order = [KEEPERS[3], KEEPERS[1], KEEPERS[2], KEEPERS[0]];
    let writer = Writer::new(network.client(1), order).unwrap();
    let explicit = StreamId(43);
    writer.create(STREAM).await.unwrap();
    writer.create(STREAM).await.unwrap();
    network
        .until(|| {
            order[..3]
                .iter()
                .all(|&id| network.view(id, STREAM).is_some())
        })
        .await;
    assert!(network.view(KEEPERS[0], STREAM).is_none());

    let ensemble = [KEEPERS[0], KEEPERS[2], KEEPERS[3]];
    writer.create_in(explicit, ensemble).await.unwrap();
    writer.seal(explicit, E1).await.unwrap();
    writer.delete(explicit).await.unwrap();
    assert_eq!(
        writer.create_in(explicit, ensemble).await,
        Err(JournalError::Deleted)
    );
    assert_eq!(writer.head(explicit).await, Err(JournalError::Deleted));
    assert!(Writer::new(network.client(2), [KEEPERS[0]; 3]).is_err());
}

#[tokio::test(start_paused = true)]
async fn limits_refuse_without_consuming_a_position_and_trim_frees_capacity() {
    let (network, writer) = started().await;
    assert_eq!(
        writer
            .append(STREAM, E1, Lsn(1), Bytes::from(vec![0; 65]))
            .await,
        Err(JournalError::TooLarge { max: 64 })
    );
    network
        .until(|| network.calls(Kind::Append).len() >= 3)
        .await;
    for i in 1..=3 {
        assert_eq!(
            writer
                .append(STREAM, E1, Lsn(i), Bytes::from(vec![i as u8; 64]))
                .await,
            Ok(Lsn(i))
        );
    }
    assert_eq!(
        writer.append(STREAM, E1, Lsn(4), record("x")).await,
        Err(JournalError::Full { floor: Lsn(1) })
    );
    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    assert_eq!(
        writer.append(STREAM, E1, Lsn(4), record("x")).await,
        Ok(Lsn(4))
    );
}

#[tokio::test(start_paused = true)]
async fn capacity_refusals_do_not_release_a_timed_out_append() {
    let (network, writer) = started().await;
    for i in 1..=3 {
        writer
            .append(STREAM, E1, Lsn(i), Bytes::from(vec![i as u8; 64]))
            .await
            .unwrap();
    }
    network
        .until(|| {
            KEEPERS[..3].iter().all(|&keeper| {
                network
                    .view(keeper, STREAM)
                    .is_some_and(|view| view.head == Lsn(3))
            })
        })
        .await;

    let delayed = Gate::new();
    network.fault(
        KEEPERS[0],
        Kind::Append,
        Fault::DelayRequest(delayed.clone()),
    );
    let append = |payload| writer.append(STREAM, E1, Lsn(4), record(payload));
    assert_eq!(append("original").await, Err(JournalError::Unavailable));
    delayed.reached().await;
    assert_eq!(
        append("original").await,
        Err(JournalError::Unavailable),
        "capacity refusals released a position with an unanswered append"
    );

    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    assert_eq!(
        append("different").await,
        Err(JournalError::Unavailable),
        "capacity refusals released a position with an unanswered append"
    );
    delayed.release();
    assert_eq!(append("original").await, Ok(Lsn(4)));
    assert_eq!(
        append("different").await,
        Err(JournalError::Conflict { head: Lsn(4) })
    );
}

#[tokio::test(start_paused = true)]
async fn seal_policy_refuses_before_sending_a_seal() {
    struct Deny;
    impl SealPolicy for Deny {
        fn authorize(&self, _: StreamId, _: Epoch, _: &Identity) -> journal_contract::Result<()> {
            Err(JournalError::Unavailable)
        }
    }
    let network = Arc::new(Network::default());
    let writer = writer(&network, 1).with_seal_policy(Arc::new(Deny));
    assert_eq!(
        writer.seal(STREAM, E1).await,
        Err(JournalError::Unavailable)
    );
    assert!(network.calls(Kind::Seal).is_empty());
}

#[tokio::test(start_paused = true)]
async fn a_writer_head_reuses_only_append_requests_opened_inside_its_round() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    let stream = writer.stream(STREAM);
    let active = stream.active.lock().clone();
    let checking = super::head::check(&writer.io, &stream, active.clone());
    tokio::pin!(checking);
    assert!(poll!(&mut checking).is_pending());

    let gates = [Gate::new(), Gate::new()];
    for (&keeper, gate) in KEEPERS.iter().zip(&gates) {
        network.fault(keeper, Kind::Append, Fault::HoldReply(gate.clone()));
    }
    let appending = writer.append(STREAM, E1, Lsn(1), record("fresh"));
    tokio::pin!(appending);
    assert!(poll!(&mut appending).is_pending());
    for gate in &gates {
        gate.reached().await;
    }

    // These requests were dispatched after the first round opened.
    assert!(poll!(&mut checking).is_pending());
    assert!(
        network
            .calls(Kind::Check)
            .iter()
            .all(|id| *id == KEEPERS[2])
    );

    // A second round must not reuse the same in-flight requests.
    let later = super::head::check(&writer.io, &stream, active);
    tokio::pin!(later);
    assert!(poll!(&mut later).is_pending());
    assert!(poll!(&mut later).is_pending());
    assert!(
        KEEPERS[..2]
            .iter()
            .all(|id| network.calls(Kind::Check).contains(id))
    );
    for gate in &gates {
        gate.release();
    }
    assert_eq!(appending.await, Ok(Lsn(1)));
    assert_eq!(checking.await, Ok(Lsn(1)));
    assert_eq!(later.await, Ok(Lsn(1)));
}

#[tokio::test(start_paused = true)]
async fn lagging_keeper_can_rejoin_after_a_committed_trim() {
    let (network, writer) = started().await;
    network.down(KEEPERS[2], true);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(1), record("retired")).await,
        Ok(Lsn(1))
    );
    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    network.down(KEEPERS[2], false);
    network.down(KEEPERS[0], true);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(2), record("retained")).await,
        Ok(Lsn(2))
    );
    let view = network.view(KEEPERS[2], STREAM).unwrap();
    assert_eq!((view.floor, view.tail), (Lsn(2), Lsn(2)));
}

#[tokio::test(start_paused = true)]
async fn unsynced_keeper_installs_the_seed_before_advancing_past_it() {
    let (network, _) = started().await;
    let [first, second, lagging] = KEEPERS[..3].try_into().unwrap();
    network.down(lagging, true);
    let next = writer(&network, 2);
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(0)));
    assert_eq!(
        next.append(STREAM, E2, Lsn(1), record("trimmed")).await,
        Ok(Lsn(1))
    );
    next.trim(STREAM, E2, Lsn(1)).await.unwrap();
    assert_eq!(network.view(lagging, STREAM).unwrap().synced, Some(E1));

    network.down(lagging, false);
    network.down(first, true);
    assert_eq!(
        next.append(STREAM, E2, Lsn(2), record("retained")).await,
        Ok(Lsn(2)),
        "lagging keeper must join after the floor passes the seed"
    );
    for keeper in [second, lagging] {
        let view = network.view(keeper, STREAM).unwrap();
        assert_eq!(
            (view.synced, view.floor, view.head),
            (Some(E2), Lsn(2), Lsn(2))
        );
    }
}

#[tokio::test(start_paused = true)]
async fn seal_requires_two_complete_sync_replies() {
    let (network, _) = started().await;
    let next = writer(&network, 2);
    network.down(KEEPERS[2], true);
    network.fault(KEEPERS[1], Kind::Sync, Fault::LoseReply);
    assert_eq!(next.seal(STREAM, E2).await, Err(JournalError::Unavailable));
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(0)));
}

#[tokio::test(start_paused = true)]
async fn journal_contract_conformance() {
    use journal_contract::conformance::{LIMITS, run_with_clock};

    let network = Arc::new(Network::new(
        3,
        LIMITS.max_record_bytes.try_into().unwrap(),
        LIMITS.stream_quota_bytes,
    ));
    let start = tokio::time::Instant::now();
    run_with_clock(
        |identity| {
            Arc::new(Writer::new(network.connect(identity), KEEPERS[..3].iter().copied()).unwrap())
        },
        || start.elapsed(),
        tokio::time::sleep,
    )
    .await;
}

#[tokio::test(start_paused = true)]
async fn read_assembles_a_page_across_keeper_frames() {
    let size = 32 * 1024 * 1024;
    let network = Arc::new(Network::new(3, size, 2 * u64::from(size)));
    let writer = Writer::new(network.client(1), KEEPERS[..3].iter().copied()).unwrap();
    writer.create(STREAM).await.unwrap();
    writer.seal(STREAM, E1).await.unwrap();
    let payload = Bytes::from(vec![7; size as usize]);
    for lsn in [Lsn(1), Lsn(2)] {
        writer
            .append(STREAM, E1, lsn, payload.clone())
            .await
            .unwrap();
    }
    let page = writer
        .read(STREAM, Lsn(1), 2, Duration::ZERO)
        .await
        .expect("complete page across keeper frames");
    assert_eq!(page.head, Lsn(2));
    assert_eq!(page.records, [(Lsn(1), payload.clone()), (Lsn(2), payload)]);
}

#[tokio::test(start_paused = true)]
async fn a_lost_read_chunk_discards_the_partial_page_before_fallback() {
    let size = 32 * 1024 * 1024;
    let network = Arc::new(Network::new(3, size, 3 * u64::from(size)));
    let writer = writer(&network, 1);
    writer.create(STREAM).await.unwrap();
    writer.seal(STREAM, E1).await.unwrap();
    let payload = Bytes::from(vec![7; size as usize]);
    for lsn in [Lsn(1), Lsn(2)] {
        writer
            .append(STREAM, E1, lsn, payload.clone())
            .await
            .unwrap();
    }
    network
        .until(|| {
            KEEPERS[..3].iter().all(|&keeper| {
                network
                    .view(keeper, STREAM)
                    .is_some_and(|view| view.head == Lsn(2))
            })
        })
        .await;

    let first = KEEPERS[0];
    let gate = Gate::new();
    network.fault(first, Kind::Read, Fault::HoldReply(gate.clone()));
    let read = writer.read(STREAM, Lsn(1), 3, Duration::ZERO);
    tokio::pin!(read);
    tokio::select! {
        _ = gate.reached() => {}
        _ = &mut read => panic!("the first chunk must be held"),
    }
    network.fault(first, Kind::Read, Fault::LoseReply);
    writer
        .append(STREAM, E1, Lsn(3), record("last"))
        .await
        .unwrap();
    network
        .until(|| {
            KEEPERS[..3].iter().all(|&keeper| {
                network
                    .view(keeper, STREAM)
                    .is_some_and(|view| view.head == Lsn(3))
            })
        })
        .await;
    gate.release();

    let page = read.await.unwrap();
    assert_eq!(page.head, Lsn(3), "fallback must use its own first reply");
    assert_eq!(
        page.records,
        [
            (Lsn(1), payload.clone()),
            (Lsn(2), payload),
            (Lsn(3), record("last"))
        ]
    );
    let calls = network.calls(Kind::Read);
    assert_eq!(&calls[..3], &[first, first, KEEPERS[1]]);
}

#[tokio::test(start_paused = true)]
async fn a_delayed_poll_reply_cannot_extend_the_read_wait() {
    let (network, writer) = started().await;
    let first = KEEPERS[0];
    network.fault(first, Kind::Poll, Fault::HoldReply(Gate::new()));
    let start = tokio::time::Instant::now();
    let page = writer.read(STREAM, Lsn(1), 1, WAIT).await.unwrap();
    assert!(
        start.elapsed() <= WAIT,
        "the first poll exhausted the wait budget"
    );
    assert_eq!(page.head, Lsn(0));
    assert!(page.records.is_empty());
    assert_eq!(network.calls(Kind::Poll), [first]);
    assert_eq!(network.calls(Kind::Read), KEEPERS[..3]);
}

/// Seal a fresh stream with a writer whose lanes send at most `records` per append.
async fn started_with_append_records(records: usize) -> (Arc<Network>, Writer) {
    let network = Arc::new(Network::default());
    let writer = writer(&network, 1).with_append_records(records);
    writer.create(STREAM).await.unwrap();
    assert_eq!(writer.seal(STREAM, E1).await, Ok(Lsn(0)));
    (network, writer)
}

async fn data_appends_for_a_batch(records: usize) -> usize {
    const BATCH: u64 = 32;
    let (network, writer) = started_with_append_records(records).await;
    let before = network.calls(Kind::Append).len();
    let acks =
        join_all((1..=BATCH).map(|at| writer.append(STREAM, E1, Lsn(at), record("batch")))).await;
    assert_eq!(acks, (1..=BATCH).map(|at| Ok(Lsn(at))).collect::<Vec<_>>());
    network.calls(Kind::Append).len() - before
}

#[tokio::test(start_paused = true)]
async fn concurrent_appends_to_one_stream_share_one_keeper_append_per_lane() {
    let shared = data_appends_for_a_batch(super::append::APPEND_RECORDS).await;
    assert!(
        shared <= 2 * KEEPERS[..3].len(),
        "32 concurrent appends used {shared} data appends"
    );
    // Negative control: one record per keeper append costs one round per record.
    let single = data_appends_for_a_batch(1).await;
    assert!(
        single >= 32 * 2,
        "the unbatched control used only {single} data appends"
    );
}

/// The observer's first round samples tail 1 while keeper 2's view is held. Before
/// the next round, keepers 0 and 1 publish head 1 and accept record 2, so a new
/// tail is always ahead of every published head, as under continuous writes.
async fn observer_head_while_tails_lead(
    index: super::head::Index,
) -> journal_contract::Result<Lsn> {
    use crate::stream::wire::{Reply, Request, Transport};

    let (network, _writer) = started().await;
    let raw = network.client(1);
    let append = |at: u64, head: u64| Request::Append {
        stream: STREAM,
        epoch: E1,
        at: Lsn(at),
        records: vec![record("lead")],
        head: Lsn(head),
    };
    for keeper in &KEEPERS[..2] {
        assert_eq!(
            raw.call(*keeper, append(1, 0)).await,
            Ok(Reply::Appended { tail: Lsn(1) })
        );
    }
    let gate = Gate::new();
    network.fault(KEEPERS[2], Kind::Check, Fault::HoldReply(gate.clone()));
    let observer = writer(&network, 9);
    let stream = observer.stream(STREAM);
    let head = super::head::observe(&observer.io, &stream, index);
    tokio::pin!(head);
    tokio::select! {
        _ = &mut head => panic!("observer finished before its first round completed"),
        _ = gate.reached() => {}
    }
    for keeper in &KEEPERS[..2] {
        assert_eq!(
            raw.call(*keeper, append(2, 1)).await,
            Ok(Reply::Appended { tail: Lsn(2) })
        );
    }
    gate.release();
    head.await
}

#[tokio::test(start_paused = true)]
async fn observer_head_pins_its_read_index_while_appends_continue() {
    assert_eq!(
        observer_head_while_tails_lead(super::head::Index::Pinned).await,
        Ok(Lsn(1))
    );
    // Negative control: resampling the tail each round chases the newest append.
    assert_eq!(
        observer_head_while_tails_lead(super::head::Index::Resampled).await,
        Err(JournalError::Unavailable)
    );
}

#[tokio::test(start_paused = true)]
async fn a_lane_retry_after_a_lost_batched_reply_resumes_from_the_keeper_tail() {
    use crate::stream::wire::{Refusal, Reply, Request, Transport};

    let (network, writer) = started().await;
    let [lost, down, survivor] = KEEPERS[..3].try_into().unwrap();
    network.fault(lost, Kind::Append, Fault::LoseReply);
    let first = join_all((1..=4).map(|at| writer.append(STREAM, E1, Lsn(at), record("one")))).await;
    assert_eq!(first, (1..=4).map(|at| Ok(Lsn(at))).collect::<Vec<_>>());
    network
        .until(|| network.view(lost, STREAM).unwrap().tail == Lsn(4))
        .await;

    // Negative control: the keeper refuses a retry that overlaps its tail and extends it.
    let raw = network.client(1);
    let retry = |records: usize| Request::Append {
        stream: STREAM,
        epoch: E1,
        at: Lsn(1),
        records: vec![record("one"); records],
        head: Lsn(0),
    };
    assert!(matches!(
        raw.call(lost, retry(8)).await,
        Ok(Reply::Refused(Refusal::Conflict { .. }))
    ));
    assert_eq!(
        raw.call(lost, retry(1)).await,
        Ok(Reply::Appended { tail: Lsn(4) })
    );

    // The lost keeper is now needed for a quorum. Its lane must not resend 1..=8.
    network.down(down, true);
    let second =
        join_all((5..=8).map(|at| writer.append(STREAM, E1, Lsn(at), record("two")))).await;
    assert_eq!(second, (5..=8).map(|at| Ok(Lsn(at))).collect::<Vec<_>>());
    for keeper in [lost, survivor] {
        assert_eq!(network.view(keeper, STREAM).unwrap().tail, Lsn(8));
    }
}
