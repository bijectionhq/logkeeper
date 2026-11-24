mod keeper;

use std::{sync::Arc, time::Duration};

use bytes::Bytes;
use futures::{future::join_all, poll};
use journal_contract::{Epoch, Journal, JournalError, Lsn, StreamId};

use super::{Holder, SealPolicy, Writer};
use keeper::{Fault, Gate, KEEPERS, Kind, Network};

const STREAM: StreamId = StreamId(42);
const E1: Epoch = Epoch(1);
const E2: Epoch = Epoch(2);
const E3: Epoch = Epoch(3);
const WAIT: Duration = Duration::from_secs(2);

fn writer(network: &Arc<Network>, holder: u128) -> Writer {
    Writer::new(network.client(holder), Holder(holder), KEEPERS).unwrap()
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

#[tokio::test]
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

#[tokio::test]
async fn two_holders_at_the_same_epoch_cannot_both_seal() {
    let (network, _) = started().await;
    let a = writer(&network, 2);
    let b = writer(&network, 3);
    let (a_seal, b_seal) = tokio::join!(a.seal(STREAM, E2), b.seal(STREAM, E2));
    assert_ne!(
        a_seal.is_ok(),
        b_seal.is_ok(),
        "one holder must win the seal race"
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

#[tokio::test]
async fn head_and_reseal_accept_the_winning_holder_amid_a_split_promise() {
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
                holder: Holder(90),
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
        "a minority promise must not mask the winning holder"
    );
    assert_eq!(
        winner.seal(STREAM, E2).await,
        Ok(Lsn(1)),
        "reseal ignores a minority promise"
    );
}

#[tokio::test]
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
                .all(|&id| network.view(id, STREAM).unwrap().end == Lsn(1))
        })
        .await;
    network.down(KEEPERS[0], true);
    network.down(KEEPERS[1], true);
    assert_eq!(
        first.append(STREAM, E1, Lsn(2), record("minority")).await,
        Err(JournalError::Unavailable)
    );
    network
        .until(|| network.view(KEEPERS[2], STREAM).unwrap().end == Lsn(2))
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
    assert_eq!(network.view(KEEPERS[2], STREAM).unwrap().end, Lsn(1));
    third
        .append(STREAM, E3, Lsn(2), record("replacement"))
        .await
        .unwrap();
    let page = third.read(STREAM, Lsn(2), 1, WAIT).await.unwrap();
    assert_eq!(page.records, [(Lsn(2), record("replacement"))]);
}

#[tokio::test]
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
                .all(|&id| network.view(id, STREAM).unwrap().end == Lsn(1))
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

#[tokio::test]
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
        Err(JournalError::Conflict {
            committed_end: Lsn(0)
        })
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
        Err(JournalError::Conflict {
            committed_end: Lsn(1)
        })
    );
    assert_eq!(
        writer.append(STREAM, E1, Lsn(3), record("gap")).await,
        Err(JournalError::Conflict {
            committed_end: Lsn(1)
        })
    );
}

#[tokio::test]
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

#[tokio::test]
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
        .until(|| network.view(KEEPERS[0], STREAM).unwrap().end == Lsn(1))
        .await;
    assert!(
        poll!(&mut pending).is_pending(),
        "one acknowledgement cannot commit"
    );
    gate.release();
    assert_eq!(pending.await, Ok(Lsn(1)));
    network.down(KEEPERS[1], true);
    assert_eq!(
        writer.append(STREAM, E1, Lsn(2), record("minority")).await,
        Err(JournalError::Unavailable)
    );
}

#[tokio::test]
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
    assert_eq!(network.view(KEEPERS[2], STREAM).unwrap().end, Lsn(1));
    gate.release();
    network
        .until(|| network.view(KEEPERS[2], STREAM).unwrap().end == Lsn(2))
        .await;
}

#[tokio::test]
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

#[tokio::test]
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

#[tokio::test]
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
                .all(|&id| network.view(id, STREAM).unwrap().commit == Lsn(1))
        })
        .await;
    assert_eq!(observer.head(STREAM).await, Ok(Lsn(1)));
}

#[tokio::test]
async fn read_long_poll_wakes_on_the_final_commit_and_uses_the_quorum_floor() {
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
    assert_eq!((page.floor, page.end), (Lsn(1), Lsn(1)));
    assert_eq!(
        writer.trim(STREAM, E1, Lsn(2)).await,
        Err(JournalError::Conflict {
            committed_end: Lsn(1)
        })
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
        (empty.floor, empty.end, empty.records),
        (Lsn(2), Lsn(1), vec![])
    );
}

#[tokio::test]
async fn read_floor_intersects_a_completed_trim() {
    use crate::stream::wire::{Reply, Request, Transport};

    let (network, writer) = started().await;
    writer
        .append(STREAM, E1, Lsn(1), record("discard"))
        .await
        .unwrap();
    writer
        .append(STREAM, E1, Lsn(2), record("retain"))
        .await
        .unwrap();
    let [first, second, third] = KEEPERS[..3].try_into().unwrap();
    network
        .until(|| network.view(third, STREAM).unwrap().commit == Lsn(2))
        .await;
    network.down(third, true);
    writer.trim(STREAM, E1, Lsn(1)).await.unwrap();
    network.down(first, true);
    network.down(third, false);

    let local = network
        .client(9)
        .call(
            third,
            Request::Read {
                stream: STREAM,
                from: Lsn(1),
                max: 1,
                wait_ms: 0,
            },
        )
        .await
        .unwrap();
    assert_eq!(
        local,
        Reply::Records {
            floor: Lsn(1),
            records: vec![(Lsn(1), record("discard"))],
            commit: Lsn(2),
        },
        "the third keeper still serves its local floor"
    );
    assert_eq!(network.view(second, STREAM).unwrap().floor, Lsn(2));

    let reader = self::writer(&network, 9);
    assert_eq!(
        reader.read(STREAM, Lsn(1), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(2) }),
        "stream-wide read floor"
    );
    assert_eq!(
        reader
            .read(STREAM, Lsn(2), 1, Duration::ZERO)
            .await
            .unwrap()
            .floor,
        Lsn(2),
        "stream-wide page floor"
    );
}

#[tokio::test]
async fn a_stale_route_cannot_read_below_a_replacement_ensemble_trim() {
    use crate::stream::keeper::{Sweep, sweep_idle};

    let (network, old_writer) = started().await;
    old_writer
        .append(STREAM, E1, Lsn(1), record("discard"))
        .await
        .unwrap();
    let [first, second, retired, learner] = KEEPERS;
    let old = [first, second, retired];
    let new = [first, second, learner];
    let plan = Sweep {
        stream: STREAM,
        ensemble: old,
        survivors: [first, second],
        learner,
        epoch: E2,
        holder: Holder(2),
    };
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
            .await,
        Err(JournalError::Unavailable),
        "stale routes cannot furnish the current read quorum"
    );
    let reader = writer(&network, 5);
    reader.bind_ensemble(STREAM, new).unwrap();
    assert_eq!(
        reader.read(STREAM, Lsn(1), 1, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(2) })
    );
}

#[tokio::test]
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
        "append reply requires quorum commit visibility"
    );
    gate.release();
    assert_eq!(append.await, Ok(Lsn(1)));
}

#[tokio::test]
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
        "head must wait for quorum commit visibility"
    );
    assert!(
        tokio::time::timeout(quiet, &mut trim).await.is_err(),
        "trim must wait for quorum commit visibility"
    );
    gate.release();
    assert_eq!(head.await, Ok(Lsn(1)));
    assert_eq!(trim.await, Ok(()));
    assert_eq!(append.await, Ok(Lsn(1)));
}

#[tokio::test]
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

#[tokio::test]
async fn create_uses_url_order_or_explicit_ensemble_and_delete_is_terminal() {
    let network = Arc::new(Network::default());
    let order = [KEEPERS[3], KEEPERS[1], KEEPERS[2], KEEPERS[0]];
    let writer = Writer::new(network.client(1), Holder(1), order).unwrap();
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
    assert!(Writer::new(network.client(2), Holder(2), [KEEPERS[0]; 3]).is_err());
}

#[tokio::test]
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

#[tokio::test]
async fn seal_policy_refuses_before_sending_a_seal() {
    struct Deny;
    impl SealPolicy for Deny {
        fn authorize(&self, _: StreamId, _: Epoch, _: Holder) -> journal_contract::Result<()> {
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

#[tokio::test]
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

#[tokio::test]
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
    assert_eq!((view.floor, view.end), (Lsn(2), Lsn(2)));
}

#[tokio::test]
async fn seal_requires_two_complete_sync_replies() {
    let (network, _) = started().await;
    let next = writer(&network, 2);
    network.down(KEEPERS[2], true);
    network.fault(KEEPERS[1], Kind::Sync, Fault::LoseReply);
    assert_eq!(next.seal(STREAM, E2).await, Err(JournalError::Unavailable));
    assert_eq!(next.seal(STREAM, E2).await, Ok(Lsn(0)));
}

#[tokio::test]
async fn journal_contract_conformance() {
    use journal_contract::conformance::{LIMITS, run};

    let network = Arc::new(Network::new(
        3,
        LIMITS.max_record_bytes.try_into().unwrap(),
        LIMITS.stream_quota_bytes,
    ));
    run(|identity| {
        Arc::new(
            Writer::new(
                network.client(identity.0),
                Holder(identity.0),
                KEEPERS[..3].iter().copied(),
            )
            .unwrap(),
        )
    })
    .await;
}

#[tokio::test]
async fn read_assembles_a_page_across_keeper_frames() {
    let size = 32 * 1024 * 1024;
    let network = Arc::new(Network::new(3, size, 2 * u64::from(size)));
    let writer = Writer::new(network.client(1), Holder(1), KEEPERS[..3].iter().copied()).unwrap();
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
    assert_eq!(page.end, Lsn(2));
    assert_eq!(page.records, [(Lsn(1), payload.clone()), (Lsn(2), payload)]);
}
