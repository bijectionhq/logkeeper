use super::*;

#[tokio::test(start_paused = true)]
async fn wire_guards() {
    let network = Network::new(0, Limits::default());
    let old = network.client(&OLD);
    let other = network.client(&NEW);
    let keeper = ENSEMBLE[0];
    let create = Request::Create {
        stream: STREAM,
        ensemble: ENSEMBLE,
    };
    let seal = |epoch| Request::Seal {
        stream: STREAM,
        ensemble: ENSEMBLE,
        epoch,
    };
    let append = |epoch, at, records, head| Request::Append {
        stream: STREAM,
        epoch,
        at,
        records,
        head,
    };
    let sync = |epoch, from, records, runs, head, complete| Request::Sync {
        stream: STREAM,
        epoch,
        from,
        records,
        runs,
        head,
        complete,
        floor: Lsn(1),
    };
    let trim = |epoch, through| Request::Trim {
        stream: STREAM,
        epoch,
        through,
    };
    let read = |from, max| Request::Read {
        stream: STREAM,
        from,
        max,
        wait_ms: 0,
    };
    let replace = |epoch, to| Request::Replace {
        stream: STREAM,
        epoch,
        from: ENSEMBLE,
        to,
    };
    let record = Bytes::from_static(b"record");
    let head0 = Lsn(0);
    let head1 = Lsn(1);
    let second = Lsn(2);

    assert_eq!(
        old.call(keeper, create.clone()).await.unwrap(),
        Reply::Created
    );
    assert!(matches!(
        old.call(keeper, seal(E1)).await.unwrap(),
        Reply::Sealed(_)
    ));
    assert_eq!(
        other.call(keeper, seal(E1)).await.unwrap(),
        Reply::Refused(Refusal::Fenced { promised: E1 }),
        "equal epoch changed identities",
    );
    assert_eq!(
        other
            .call(keeper, sync(E1, head1, vec![], vec![], head0, true))
            .await
            .unwrap(),
        Reply::Refused(Refusal::Fenced { promised: E1 }),
        "sync ignored the promised identity",
    );
    assert!(matches!(
        old.call(keeper, sync(E1, head1, vec![], vec![], head0, false))
            .await
            .unwrap(),
        Reply::Synced { .. },
    ));
    assert_eq!(
        old.call(keeper, append(E1, head1, vec![record.clone()], head0))
            .await
            .unwrap(),
        Reply::Refused(Refusal::NotSynced),
        "incomplete sync enabled an append",
    );
    assert!(matches!(
        old.call(keeper, sync(E1, head1, vec![], vec![], head0, true))
            .await
            .unwrap(),
        Reply::Synced { .. },
    ));
    assert_eq!(
        old.call(keeper, append(E1, second, vec![record.clone()], head0))
            .await
            .unwrap(),
        Reply::Refused(Refusal::Gap { head: head0 }),
        "append admitted a gap",
    );
    let write = append(E1, head1, vec![record], head0);
    for _ in 0..2 {
        assert_eq!(
            old.call(keeper, write.clone()).await.unwrap(),
            Reply::Appended { tail: head1 },
            "identical append retry was refused"
        );
    }
    assert_eq!(
        old.call(
            keeper,
            append(E1, head1, vec![Bytes::from_static(b"other")], head0)
        )
        .await
        .unwrap(),
        Reply::Refused(Refusal::Conflict { head: head0 }),
        "conflicting append counted as a retry",
    );
    assert_eq!(
        old.call(keeper, read(head1, 1)).await.unwrap(),
        Reply::Records {
            floor: head1,
            records: vec![],
            head: head0
        },
        "read exposed an uncommitted record",
    );
    let check = Request::Check {
        stream: STREAM,
        epoch: Epoch(42),
    };
    for _ in 0..2 {
        assert!(
            matches!(
                old.call(keeper, check.clone()).await.unwrap(),
                Reply::Checked(view) if view.tail == head1 && view.head == head0 && view.synced == Some(E1)
            ),
            "check misreported the durable view"
        );
    }
    assert_eq!(
        old.call(keeper, trim(E1, head1)).await.unwrap(),
        Reply::Refused(Refusal::AboveHead { head: head0 }),
        "trim crossed the head",
    );
    assert_eq!(
        old.call(keeper, append(E1, second, vec![], second))
            .await
            .unwrap(),
        Reply::Refused(Refusal::AboveHead { head: head0 }),
        "head publication exceeded the tail",
    );
    assert_eq!(
        old.call(keeper, append(E1, second, vec![], head1))
            .await
            .unwrap(),
        Reply::Appended { tail: head1 },
    );
    assert!(matches!(
        other.call(keeper, seal(E2)).await.unwrap(),
        Reply::Sealed(_)
    ));
    assert_eq!(
        old.call(keeper, seal(E1)).await.unwrap(),
        Reply::Refused(Refusal::Fenced { promised: E2 }),
        "lower epoch acquired a promise",
    );
    assert_eq!(
        old.call(keeper, append(E1, second, vec![Bytes::new()], head1))
            .await
            .unwrap(),
        Reply::Refused(Refusal::Fenced { promised: E2 }),
        "stale epoch admitted an append",
    );
    assert_eq!(
        other
            .call(keeper, replace(E2, [keeper, ENSEMBLE[1], LEARNER]))
            .await
            .unwrap(),
        Reply::Refused(Refusal::NotSynced),
        "unsynced keeper installed a replacement",
    );
    assert_eq!(
        other
            .call(keeper, sync(E2, second, vec![], vec![], head0, true))
            .await
            .unwrap(),
        Reply::Refused(Refusal::AboveHead { head: head1 }),
        "sync regressed the head",
    );
    assert_eq!(
        other
            .call(
                keeper,
                sync(
                    E2,
                    head1,
                    vec![Bytes::from_static(b"wrong")],
                    vec![EpochRun {
                        epoch: E1,
                        first: head1,
                        last: head1
                    }],
                    head1,
                    true,
                )
            )
            .await
            .unwrap(),
        Reply::Refused(Refusal::Conflict { head: head1 }),
        "sync replaced a committed record",
    );
    assert_eq!(
        other
            .call(keeper, sync(E2, second, vec![], vec![], head1, true))
            .await
            .unwrap(),
        Reply::Synced { tail: head1 },
    );
    assert_eq!(
        old.call(keeper, trim(E1, head1)).await.unwrap(),
        Reply::Refused(Refusal::Fenced { promised: E2 }),
        "stale epoch trimmed a record",
    );
    assert_eq!(
        other
            .call(keeper, replace(E2, [ENSEMBLE[1], keeper, LEARNER]))
            .await
            .unwrap(),
        Reply::Refused(Refusal::Unauthorized),
        "replacement changed multiple slots",
    );
    assert_eq!(
        other.call(keeper, trim(E2, head1)).await.unwrap(),
        Reply::Trimmed { floor: second }
    );
    assert_eq!(
        old.call(keeper, read(head1, 0)).await.unwrap(),
        Reply::Refused(Refusal::BelowFloor { floor: second }),
        "read admitted a position below floor",
    );
    network.lose_disk(ENSEMBLE[2]);
    assert_eq!(
        old.call(LEARNER, create.clone()).await.unwrap(),
        Reply::Created
    );
    assert!(matches!(
        old.call(LEARNER, seal(E1)).await.unwrap(),
        Reply::Sealed(_)
    ));
    assert_eq!(
        old.call(LEARNER, sync(E1, head1, vec![], vec![], head0, true))
            .await
            .unwrap(),
        Reply::Synced { tail: head0 },
    );
    assert_eq!(
        old.call(LEARNER, append(E1, head1, vec![Bytes::new()], head0))
            .await
            .unwrap(),
        Reply::Refused(Refusal::NotSynced),
        "synced learner voted before replacement",
    );

    let delete = Request::Delete {
        stream: STREAM,
        ensemble: ENSEMBLE,
    };
    assert_eq!(
        old.call(keeper, delete.clone()).await.unwrap(),
        Reply::Deleted
    );
    network.restart_survivors();
    assert_eq!(
        old.call(keeper, create).await.unwrap(),
        Reply::Refused(Refusal::Deleted),
        "delete permitted stream reuse after restart",
    );
    assert_eq!(old.call(keeper, delete).await.unwrap(), Reply::Deleted);
}

#[tokio::test(start_paused = true)]
async fn recovery_prefers_newer_synced_history() {
    let network = Network::new(0, Limits::default());
    let old = writer(&network, &OLD, ENSEMBLE);
    let next = writer(&network, &NEW, ENSEMBLE);
    let later = writer(&network, &READER, ENSEMBLE);
    let history = History::new(&network);
    let [lagging, _, other] = ENSEMBLE;

    history.call(&old, &OLD, Op::Create).await.unwrap();
    sleep(20).await;
    history.call(&old, &OLD, Op::Seal(E1)).await.unwrap();
    sleep(45).await;
    // An old writer can leave an accepted suffix on just one keeper.
    assert_eq!(
        network
            .client(&OLD)
            .call(
                lagging,
                Request::Append {
                    stream: STREAM,
                    epoch: E1,
                    at: Lsn(1),
                    records: vec![Bytes::from_static(b"old"), Bytes::from_static(b"old")],
                    head: Lsn(0),
                }
            )
            .await
            .unwrap(),
        Reply::Appended { tail: Lsn(2) },
    );
    network.isolate(Some(lagging));
    assert_eq!(
        position(history.call(&next, &NEW, Op::Seal(E2)).await),
        Lsn(0)
    );
    history
        .call(
            &next,
            &NEW,
            Op::Append(E2, Lsn(1), Bytes::from_static(b"new")),
        )
        .await
        .unwrap();
    sleep(30).await;
    network.isolate(Some(other));
    assert_eq!(
        history.call(&later, &READER, Op::Seal(E3)).await,
        Ok(Value::Position(Lsn(1))),
        "recovery must prefer the newer synced history",
    );
    history.check(0);
}

#[tokio::test(start_paused = true)]
async fn head_covers_acknowledged_appends_with_a_lagging_keeper() {
    for seed in 0..8 {
        let network = Network::new(seed, Limits::default());
        let old = writer(&network, &OLD, ENSEMBLE);
        let next = writer(&network, &NEW, ENSEMBLE);
        let observer = writer(&network, &READER, ENSEMBLE);
        let history = History::new(&network);
        let lagging = ENSEMBLE[seed as usize % ENSEMBLE.len()];

        history.call(&old, &OLD, Op::Create).await.unwrap();
        sleep(20).await;
        history.call(&old, &OLD, Op::Seal(E1)).await.unwrap();
        sleep(45).await;
        network.isolate(Some(lagging));
        history
            .call(&old, &OLD, Op::Append(E1, Lsn(1), Bytes::from_static(b"a")))
            .await
            .unwrap();
        sleep(30).await;
        network.isolate(None);
        assert_eq!(
            history.call(&observer, &READER, Op::Head).await,
            Ok(Value::Position(Lsn(1))),
            "observer head missed an acknowledged append",
        );
        assert_eq!(
            history.call(&next, &NEW, Op::Seal(E2)).await,
            Ok(Value::Position(Lsn(1))),
            "recovery must prefer the longer history at the same synced epoch",
        );
        history
            .call(
                &next,
                &NEW,
                Op::Append(E2, Lsn(2), Bytes::from_static(b"b")),
            )
            .await
            .unwrap();
        let zombie = history.call(&old, &OLD, Op::Head).await;
        assert!(
            matches!(
                zombie,
                Ok(Value::Position(Lsn(2))) | Err(JournalError::Unavailable)
            ),
            "writer head used a stale epoch"
        );
        history.check(seed);
    }
}

#[tokio::test(start_paused = true)]
async fn one_acceptance_cannot_publish_a_head() {
    for seed in 0..8 {
        let network = Network::new(seed, Limits::default());
        let old = writer(&network, &OLD, ENSEMBLE);
        let history = History::new(&network);
        history.call(&old, &OLD, Op::Create).await.unwrap();
        sleep(20).await;
        history.call(&old, &OLD, Op::Seal(E1)).await.unwrap();
        sleep(45).await;
        network.isolate(Some(ENSEMBLE[2]));
        network.arm(ENSEMBLE[1], Fault::CrashBefore);
        assert_eq!(
            history
                .call(
                    &old,
                    &OLD,
                    Op::Append(E1, Lsn(1), Bytes::from_static(b"only"))
                )
                .await,
            Err(JournalError::Unavailable),
        );
        sleep(35).await;
        assert!(
            !network.coverage().contains_key("head publication"),
            "writer published a head without two acceptances"
        );
        history.check(seed);
    }
}

#[tokio::test(start_paused = true)]
async fn failed_sync_never_replies() {
    let network = Network::new(0, Limits::default());
    let old = writer(&network, &OLD, ENSEMBLE);
    let history = History::new(&network);
    history.call(&old, &OLD, Op::Create).await.unwrap();
    sleep(20).await;
    history.call(&old, &OLD, Op::Seal(E1)).await.unwrap();
    sleep(45).await;
    let target = ENSEMBLE[0];
    network.arm(target, Fault::LoseUnsynced);
    assert_eq!(
        network
            .client(&OLD)
            .call(
                target,
                Request::Append {
                    stream: STREAM,
                    epoch: E1,
                    at: Lsn(1),
                    head: Lsn(0),
                    records: vec![Bytes::from_static(b"missing")],
                }
            )
            .await,
        Err(TransportError::Unreachable),
    );
    network.restart_survivors();
    assert_eq!(
        network.copies(
            &ENSEMBLE,
            STREAM,
            Lsn(1),
            &Bytes::from_static(b"missing"),
            false
        ),
        0
    );
    history.check(0);
}

#[tokio::test(start_paused = true)]
async fn conflicting_retry_cannot_publish_on_a_lagging_keeper() {
    let network = Network::new(0, Limits::default());
    let old = writer(&network, &OLD, ENSEMBLE);
    let reader = writer(&network, &READER, ENSEMBLE);
    let history = History::new(&network);
    history.call(&old, &OLD, Op::Create).await.unwrap();
    sleep(20).await;
    history.call(&old, &OLD, Op::Seal(E1)).await.unwrap();
    sleep(45).await;

    let at = Lsn(1);
    let chosen = Bytes::from_static(b"chosen");
    let lagging = ENSEMBLE[0];
    network.arm(lagging, Fault::Delay(100));
    history
        .call(&old, &OLD, Op::Append(E1, at, chosen.clone()))
        .await
        .unwrap();
    assert_eq!(network.copies(&[lagging], STREAM, at, &chosen, false), 0);
    assert_eq!(
        history
            .call(&old, &OLD, Op::Append(E1, at, Bytes::from_static(b"other")))
            .await,
        Err(JournalError::Conflict { head: at }),
    );
    history
        .call(&reader, &READER, Op::Read(at, 1))
        .await
        .unwrap();
    history.check(0);
}
