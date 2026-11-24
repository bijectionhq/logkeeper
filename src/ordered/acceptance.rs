use super::*;

fn apply(state: &mut State, principal: Principal, command: Command) -> Receipt {
    let id = RequestId::fresh(state.position(), state.limits.retry_positions).unwrap();
    state
        .apply(
            state.position() + 1,
            state.time(),
            Request {
                id,
                principal,
                placement: state.placement,
                command,
            },
        )
        .unwrap()
}

fn enroll(state: &mut State) -> Enrollment {
    let receipt = apply(
        state,
        Principal::Administrator,
        Command::Enroll {
            worker: Uuid::new_v4(),
            expected: None,
        },
    );
    let Ok(Outcome::Enrolled(enrollment)) = receipt.outcome else {
        panic!("the worker was not enrolled: {receipt:?}");
    };
    enrollment
}

fn grant(state: &mut State, enrollment: Enrollment) -> (Grant, Hold) {
    let expected = state.writer_state();
    let receipt = apply(
        state,
        Principal::Worker(enrollment),
        Command::Grant {
            expected,
            candidate: enrollment,
        },
    );
    let Ok(Outcome::Granted { grant, recovery }) = receipt.outcome else {
        panic!("the worker could not protect its startup cut: {receipt:?}");
    };
    (grant, recovery)
}

#[test]
fn full_data_and_read_capacity_let_a_replacement_publish_trim_and_reopen() {
    let charge = APPEND_RECORD_CHARGE_BYTES + 1;
    let junk = Uuid::new_v4();
    let initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 2,
            replay_holds: 1,
            retry_positions: 64,
            retained_data_bytes: 5 * charge,
            maintenance_bytes: 4 * charge,
            serving_lease: 30_000,
            clock_drift: 1_000,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: junk,
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: charge,
        },
    )
    .unwrap();
    let mut state = initial.clone();
    let first = enroll(&mut state);
    let second = enroll(&mut state);
    let (first_grant, first_start) = grant(&mut state, first);
    let original = Request {
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        placement: state.placement,
        principal: Principal::Worker(first),
        command: Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: first_grant,
            expected_next: 0,
            timestamp: 1,
            payload: Bytes::from_static(b"d"),
        },
    };
    let Some(original_receipt) = state
        .apply(state.position() + 1, state.time(), original.clone())
        .unwrap()
        .outcome
        .ok()
    else {
        panic!("the ordinary data allocation should have been spent");
    };
    let Outcome::Appended(original_result) = original_receipt else {
        panic!("not an append")
    };
    let read_receipt = apply(
        &mut state,
        original.principal,
        Command::Barrier,
    );
    let Ok(Outcome::Barrier { read, .. }) = read_receipt.outcome else {
        panic!("read not protected")
    };

    let (successor, startup) = grant(&mut state, second);
    let worker = Principal::Worker(second);
    let root_receipt = apply(&mut state, worker, Command::ProtectRoot { source: startup });
    assert!(matches!(root_receipt.outcome, Ok(Outcome::Protected(_))));
    let append = |state: &mut State, class| {
        let expected_next = state.head.next_lsn;
        apply(
            state,
            worker,
            Command::Append {
                references: None,
                class,
                grant: successor,
                expected_next,
                timestamp: 2,
                payload: Bytes::from_static(b"m"),
            },
        )
        .outcome
    };
    assert_eq!(
        append(&mut state, AppendClass::Data),
        Err(Refusal::Capacity)
    );
    assert!(matches!(
        append(&mut state, AppendClass::Maintenance),
        Ok(Outcome::Appended(_))
    ));
    let Ok(Outcome::Appended(boundary)) = append(&mut state, AppendClass::Maintenance) else {
        panic!("reserved capacity did not admit a block boundary");
    };
    assert!(matches!(
        append(&mut state, AppendClass::Maintenance),
        Ok(Outcome::Appended(_))
    ));
    let checkpoint = Checkpoint {
        cut: boundary.cut,
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 2,
            provider: [4; 32],
        },
    };
    let preparation = CheckpointPreparation {
        erasure: false,
        checkpoint: checkpoint.cut,
        root: checkpoint.root,
        source: successor,
        base: initial.checkpoint,
        custody: checkpoint.custody,
        usable_bytes: 64,
        descriptor: [5; 32],
    };
    assert!(matches!(
        apply(
            &mut state,
            Principal::Custodian,
            Command::PrepareCheckpoint {
                preparation,
                references: None
            }
        )
        .outcome,
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        apply(&mut state, worker, Command::Vacate { grant: successor }).outcome,
        Ok(Outcome::Vacated)
    );
    assert_eq!(
        apply(
            &mut state,
            Principal::Custodian,
            Command::Publish { checkpoint }
        )
        .outcome,
        Ok(Outcome::Published(checkpoint))
    );
    let trim = Command::Trim {
        selected: checkpoint,
        through: checkpoint.cut,
    };
    assert_eq!(
        apply(&mut state, Principal::Custodian, trim.clone()).outcome,
        Err(Refusal::Unavailable)
    );
    for hold in [first_start, startup, read] {
        assert_eq!(
            apply(
                &mut state,
                Principal::Worker(hold.owner),
                Command::Release { hold }
            )
            .outcome,
            Ok(Outcome::Released)
        );
    }
    assert_eq!(
        apply(&mut state, Principal::Custodian, trim).outcome,
        Ok(Outcome::Trimmed(TrimResult {
            from: initial.floor,
            through: checkpoint.cut,
            ordinary_bytes: charge,
            maintenance_bytes: 2 * charge,
        }))
    );

    let image = state.encode_base();
    let mut recovered = State::decode_base(&initial, image.clone()).unwrap();
    assert_eq!(recovered.encode_base(), image);
    assert_eq!(recovered.maintenance_retained, charge);
    assert!(recovered.record(0).is_none());
    assert_eq!(recovered.reconcile_append(&original), Ok(original_result));
    let window = Window {
        allocation: Uuid::new_v4(),
        serial: 2,
        bytes: charge,
    };
    assert_eq!(
        apply(
            &mut recovered,
            Principal::Custodian,
            Command::FundWindow { window }
        )
        .outcome,
        Ok(Outcome::WindowFunded(window))
    );
    assert!(recovered.writer_state().grant.is_none());
    let (renewed, _) = grant(&mut recovered, second);
    let next = recovered.head.next_lsn;
    assert!(matches!(
        apply(
            &mut recovered,
            worker,
            Command::Append {
                references: None,
                class: AppendClass::Data,
                grant: renewed,
                expected_next: next,
                timestamp: 3,
                payload: Bytes::from_static(b"n"),
            }
        )
        .outcome,
        Ok(Outcome::Appended(_))
    ));
}

#[test]
fn identical_reads_are_fresh_admissions_while_identical_appends_deduplicate() {
    let initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 1,
            replay_holds: 4,
            retry_positions: 64,
            retained_data_bytes: 1 << 16,
            maintenance_bytes: 1 << 12,
            serving_lease: 30_000,
            clock_drift: 1_000,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1 << 12,
        },
    )
    .unwrap();
    let mut state = initial.clone();
    let worker = enroll(&mut state);
    let (writer, _) = grant(&mut state, worker);
    let principal = Principal::Worker(worker);
    let request = |state: &State, command| Request {
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        placement: state.placement,
        principal,
        command,
    };
    let next = |state: &State| state.position() + 1;

    // Two identical append requests resolve to one receipt and one record.
    let append = request(
        &state,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: writer,
            expected_next: 0,
            timestamp: 1,
            payload: Bytes::from_static(b"a"),
        },
    );
    let appended = state
        .apply(next(&state), state.time(), append.clone())
        .unwrap();
    assert!(matches!(appended.outcome, Ok(Outcome::Appended(_))));
    assert_eq!(
        state
            .apply(next(&state), state.time(), append.clone())
            .unwrap(),
        appended
    );
    assert_eq!(state.retained_receipt(&append), Some(appended));
    assert_eq!(state.head().next_lsn, 1);

    // Two identical read commands are two admissions with distinct holds.
    let barrier = Command::Barrier;
    let first = state
        .apply(next(&state), state.time(), request(&state, barrier.clone()))
        .unwrap();
    let Ok(Outcome::Barrier { read: early, .. }) = first.outcome else {
        panic!("first read refused: {first:?}");
    };
    let second = state
        .apply(next(&state), state.time(), request(&state, barrier.clone()))
        .unwrap();
    let Ok(Outcome::Barrier { read: late, .. }) = second.outcome else {
        panic!("second read refused: {second:?}");
    };
    assert_ne!(first, second);
    assert_ne!(early.id, late.id);
    assert_eq!(early.through, late.through);
    assert_eq!(state.holds.len(), 3);

    // The exact reissue of an admitted read never replays its receipt and
    // never takes a second hold, and its original receipt stays retained.
    let reissue = Request {
        id: early.id,
        placement: state.placement,
        principal,
        command: barrier.clone(),
    };
    assert_eq!(state.retained_receipt(&reissue), None);
    let refused = state.apply(next(&state), state.time(), reissue).unwrap();
    assert_eq!(refused.outcome, Err(Refusal::Conflict));
    assert_eq!(refused.position, state.position());
    assert_eq!(state.holds.len(), 3);
    assert_eq!(state.outcomes[&(principal, early.id)].receipt, first);

    // A later read observes at or after every earlier read's cut.
    let more = request(
        &state,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: writer,
            expected_next: 1,
            timestamp: 2,
            payload: Bytes::from_static(b"b"),
        },
    );
    assert!(
        state
            .apply(next(&state), state.time(), more)
            .unwrap()
            .outcome
            .is_ok()
    );
    let third = state
        .apply(next(&state), state.time(), request(&state, barrier))
        .unwrap();
    let Ok(Outcome::Barrier { read: latest, .. }) = third.outcome else {
        panic!("third read refused: {third:?}");
    };
    assert!(latest.through.next_lsn > late.through.next_lsn);

    assert_eq!(
        apply(&mut state, principal, Command::Vacate { grant: writer }).outcome,
        Ok(Outcome::Vacated)
    );
    let Ok(Outcome::Barrier { read }) = apply(&mut state, principal, Command::Barrier).outcome else {
        panic!("an enrolled reader could not protect the committed head during a vacancy");
    };
    assert_eq!(read.through, latest.through);
    assert_eq!(read.owner, worker);

    let lease = apply(&mut state, principal, Command::LeaseRead { hold: read });
    assert!(matches!(lease.outcome, Ok(Outcome::ReadLeased { hold, issued_at, lease_end })
        if hold == read && lease_end > issued_at));
    assert_eq!(
        apply(&mut state, Principal::RouteReader, Command::LeaseRead { hold: read }).outcome,
        Err(Refusal::Unauthorized),
    );

    // Every live read hold keeps its own receipt as provenance.
    let image = state.encode_base();
    let recovered = State::decode_base(&initial, image.clone()).unwrap();
    assert_eq!(recovered.encode_base(), image);
}

#[test]
fn a_reader_that_lost_the_reply_releases_its_read_by_identity() {
    let initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 2,
            replay_holds: 4,
            retry_positions: 64,
            retained_data_bytes: 1 << 16,
            maintenance_bytes: 1 << 12,
            serving_lease: 30_000,
            clock_drift: 1_000,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1 << 12,
        },
    )
    .unwrap();
    let mut state = initial.clone();
    let reader = enroll(&mut state);
    let other = Principal::Worker(enroll(&mut state));
    let principal = Principal::Worker(reader);
    let expected = state.writer_state();
    let grant_request = Request {
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        placement: state.placement,
        principal,
        command: Command::Grant {
            expected,
            candidate: reader,
        },
    };
    let granted = state.apply(state.position() + 1, state.time(), grant_request.clone());
    let Ok(Outcome::Granted {
        grant: writer,
        recovery,
    }) = granted.unwrap().outcome
    else {
        panic!("the reader was not granted");
    };
    let issue = |state: &mut State, principal, command| {
        let request = Request {
            id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
            placement: state.placement,
            principal,
            command,
        };
        let receipt = state
            .apply(state.position() + 1, state.time(), request.clone())
            .unwrap();
        (request, receipt.outcome)
    };
    let release_read = |state: &mut State, principal, read| {
        issue(state, principal, Command::ReleaseRead { read }).1
    };
    let (append, appended) = issue(
        &mut state,
        principal,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: writer,
            expected_next: 0,
            timestamp: 1,
            payload: Bytes::from_static(b"a"),
        },
    );
    let Ok(Outcome::Appended(appended)) = appended else {
        panic!("append refused");
    };

    // The reply to this read is lost: the reader keeps only its identity.
    let (lost, _) = issue(&mut state, principal, Command::Barrier);
    assert_eq!(state.holds[&lost.id].hold.through, appended.cut);
    let (_, kept) = issue(&mut state, principal, Command::Barrier);
    let Ok(Outcome::Barrier { read: kept, .. }) = kept else {
        panic!("second read refused");
    };
    let (_, protected) = issue(
        &mut state,
        principal,
        Command::Protect {
            grant: writer,
            through: appended.cut,
        },
    );
    let Ok(Outcome::Protected(protected)) = protected else {
        panic!("protection refused");
    };

    // Only the admitting principal can release, and only a read.
    assert_eq!(
        release_read(&mut state, other, lost.id),
        Err(Refusal::Unauthorized)
    );
    assert_eq!(
        release_read(&mut state, Principal::Custodian, lost.id),
        Err(Refusal::Unauthorized)
    );
    assert_eq!(
        release_read(&mut state, principal, append.id),
        Err(Refusal::Conflict)
    );
    assert_eq!(
        release_read(&mut state, principal, grant_request.id),
        Err(Refusal::Conflict)
    );
    assert_eq!(
        release_read(&mut state, principal, protected.id),
        Err(Refusal::Conflict)
    );
    assert_eq!(state.holds.len(), 4);
    let image = state.encode_base();
    assert_eq!(
        State::decode_base(&initial, image.clone())
            .unwrap()
            .encode_base(),
        image
    );

    let checkpoint = Checkpoint {
        cut: appended.cut,
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 2,
            provider: [4; 32],
        },
    };
    let preparation = CheckpointPreparation {
        erasure: false,
        checkpoint: checkpoint.cut,
        root: checkpoint.root,
        source: writer,
        base: initial.checkpoint,
        custody: checkpoint.custody,
        usable_bytes: 64,
        descriptor: [5; 32],
    };
    assert!(matches!(
        issue(
            &mut state,
            Principal::Custodian,
            Command::PrepareCheckpoint {
                preparation,
                references: None
            }
        )
        .1,
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        issue(
            &mut state,
            Principal::Custodian,
            Command::Publish { checkpoint }
        )
        .1,
        Ok(Outcome::Published(checkpoint))
    );
    for hold in [recovery, kept, protected] {
        assert_eq!(
            issue(&mut state, principal, Command::Release { hold }).1,
            Ok(Outcome::Released)
        );
    }
    let trim = Command::Trim {
        selected: checkpoint,
        through: checkpoint.cut,
    };
    // The orphaned read alone still pins the suffix.
    assert_eq!(
        issue(&mut state, Principal::Custodian, trim.clone()).1,
        Err(Refusal::Unavailable)
    );

    assert_eq!(
        release_read(&mut state, principal, lost.id),
        Ok(Outcome::Released)
    );
    assert!(state.holds.is_empty());
    // The released read's identity stays spent until its window closes.
    let resent = state
        .apply(state.position() + 1, state.time(), lost.clone())
        .unwrap();
    assert_eq!(resent.outcome, Err(Refusal::Conflict));
    assert!(state.holds.is_empty());
    // Releasing again, or an unknown read, is already done.
    assert_eq!(
        release_read(&mut state, principal, lost.id),
        Ok(Outcome::Released)
    );
    let unknown = RequestId::fresh(state.position(), 8).unwrap();
    assert_eq!(
        release_read(&mut state, principal, unknown),
        Ok(Outcome::Released)
    );
    let image = state.encode_base();
    assert_eq!(
        State::decode_base(&initial, image.clone())
            .unwrap()
            .encode_base(),
        image
    );

    assert!(matches!(
        issue(&mut state, Principal::Custodian, trim).1,
        Ok(Outcome::Trimmed(_))
    ));

    // Past its window the receipt leaves with the hold.
    let (late, _) = issue(&mut state, principal, Command::Barrier);
    while state.position() < late.id.expires_at {
        let _ = issue(
            &mut state,
            Principal::Custodian,
            Command::Publish { checkpoint },
        );
    }
    assert!(state.outcomes.contains_key(&(principal, late.id)));
    assert_eq!(
        release_read(&mut state, principal, late.id),
        Ok(Outcome::Released)
    );
    assert!(!state.outcomes.contains_key(&(principal, late.id)));
    assert!(state.holds.is_empty());
    let image = state.encode_base();
    assert_eq!(
        State::decode_base(&initial, image.clone())
            .unwrap()
            .encode_base(),
        image
    );
}

#[test]
fn a_withdrawn_worker_is_disposed_only_after_its_lease_and_drift() {
    let initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 2,
            replay_holds: 4,
            retry_positions: 64,
            retained_data_bytes: 1 << 16,
            maintenance_bytes: 1 << 12,
            serving_lease: 1_000,
            clock_drift: 100,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1 << 12,
        },
    )
    .unwrap();
    let mut state = initial.clone();
    let at = |state: &mut State, time: u64, principal, command| {
        let request = Request {
            id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
            placement: state.placement,
            principal,
            command,
        };
        state
            .apply(state.position() + 1, time, request)
            .unwrap()
            .outcome
    };
    let round_trips = |state: &State| {
        let image = state.encode_base();
        let recovered = State::decode_base(&initial, image.clone()).unwrap();
        assert_eq!(recovered.encode_base(), image);
        assert_eq!(recovered.time(), state.time());
        assert_eq!(recovered.leases, state.leases);
    };
    let enroll_at = |state: &mut State, time| {
        let Ok(Outcome::Enrolled(enrollment)) = at(
            state,
            time,
            Principal::Administrator,
            Command::Enroll {
                worker: Uuid::new_v4(),
                expected: None,
            },
        ) else {
            panic!("enrollment refused");
        };
        enrollment
    };
    let grant_at = |state: &mut State, time, candidate: Enrollment| {
        let expected = state.writer_state();
        let Ok(Outcome::Granted { grant, recovery }) = at(
            state,
            time,
            Principal::Worker(candidate),
            Command::Grant {
                expected,
                candidate,
            },
        ) else {
            panic!("grant refused");
        };
        (grant, recovery)
    };
    let first = enroll_at(&mut state, 0);
    let second = enroll_at(&mut state, 0);
    let old = Principal::Worker(first);
    let (old_grant, old_recovery) = grant_at(&mut state, 10, first);

    // The current writer obtains a lease measured in journal time.
    assert_eq!(
        at(&mut state, 100, old, Command::Lease { grant: old_grant }),
        Ok(Outcome::Leased {
            grant: old_grant,
            issued_at: 100,
            lease_end: 1_100,
        })
    );
    assert_eq!(state.lease_end(first), Some(1_100));
    let Ok(Outcome::Appended(appended)) = at(
        &mut state,
        110,
        old,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: old_grant,
            expected_next: 0,
            timestamp: 1,
            payload: Bytes::from_static(b"a"),
        },
    ) else {
        panic!("append refused");
    };
    let Ok(Outcome::Barrier { read, .. }) =
        at(&mut state, 120, old, Command::Barrier)
    else {
        panic!("read refused");
    };

    // Journal time never moves back in decision order.
    let position = state.position();
    let backwards = Request {
        id: RequestId::fresh(position, state.limits.retry_positions).unwrap(),
        placement: state.placement,
        principal: old,
        command: Command::Lease { grant: old_grant },
    };
    assert_eq!(
        state.apply(position + 1, 119, backwards),
        Err(ApplyError::Time)
    );
    assert_eq!(state.position(), position);
    assert_eq!(state.time(), 120);

    // A grant change alone keeps the old writer's holds and lease.
    let (new_grant, new_recovery) = grant_at(&mut state, 200, second);
    assert_eq!(state.holds[&read.id].hold, read);
    assert_eq!(state.holds[&old_recovery.id].hold, old_recovery);
    assert_eq!(state.lease_end(first), Some(1_100));
    assert_eq!(
        at(&mut state, 210, old, Command::Lease { grant: old_grant }),
        Err(Refusal::Stale)
    );
    assert!(matches!(
        at(
            &mut state,
            210,
            Principal::Worker(second),
            Command::Lease { grant: new_grant }
        ),
        Ok(Outcome::Leased {
            lease_end: 1_210,
            ..
        })
    ));
    let dispose = Command::DisposeExpired { enrollment: first };
    assert!(state.withdrawn_hold_owners(None, 64).next().is_none());
    assert_eq!(
        at(&mut state, 300, Principal::Administrator, dispose.clone()),
        Err(Refusal::Stale)
    );
    round_trips(&state);

    let checkpoint = Checkpoint {
        cut: appended.cut,
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 2,
            provider: [4; 32],
        },
    };
    let preparation = CheckpointPreparation {
        erasure: false,
        checkpoint: checkpoint.cut,
        root: checkpoint.root,
        source: new_grant,
        base: initial.checkpoint,
        custody: checkpoint.custody,
        usable_bytes: 64,
        descriptor: [5; 32],
    };
    assert!(matches!(
        at(
            &mut state,
            300,
            Principal::Custodian,
            Command::PrepareCheckpoint {
                preparation,
                references: None
            }
        ),
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        at(
            &mut state,
            300,
            Principal::Custodian,
            Command::Publish { checkpoint }
        ),
        Ok(Outcome::Published(checkpoint))
    );
    assert_eq!(
        at(
            &mut state,
            300,
            Principal::Worker(second),
            Command::Release { hold: new_recovery }
        ),
        Ok(Outcome::Released)
    );
    let trim = Command::Trim {
        selected: checkpoint,
        through: checkpoint.cut,
    };
    assert_eq!(
        at(&mut state, 300, Principal::Custodian, trim.clone()),
        Err(Refusal::Unavailable)
    );

    // Withdrawal alone does not dispose: the lease plus drift must pass.
    assert_eq!(
        at(
            &mut state,
            300,
            Principal::Administrator,
            Command::Withdraw { enrollment: first }
        ),
        Ok(Outcome::Withdrawn)
    );
    assert_eq!(state.lease_end(first), Some(1_100));
    round_trips(&state);
    let recovered = State::decode_base(&initial, state.encode_base()).unwrap();
    assert_eq!(
        recovered
            .withdrawn_hold_owners(None, 64)
            .collect::<Vec<_>>(),
        [first]
    );
    assert_eq!(recovered.expiry_disposal_time(first), Some(1_200));
    assert_eq!(
        at(&mut state, 1_199, Principal::Custodian, dispose.clone()),
        Err(Refusal::Unavailable)
    );
    assert_eq!(
        at(&mut state, 1_199, old, dispose.clone()),
        Err(Refusal::Unauthorized)
    );
    assert_eq!(
        at(&mut state, 1_199, Principal::Custodian, trim.clone()),
        Err(Refusal::Unavailable)
    );
    assert_eq!(
        at(&mut state, 1_200, Principal::Custodian, dispose.clone()),
        Ok(Outcome::WorkerDisposed(first))
    );
    assert!(state.holds.values().all(|entry| entry.hold.owner != first));
    assert!(state.withdrawn_hold_owners(None, 64).next().is_none());
    assert_eq!(state.lease_end(first), None);
    round_trips(&state);
    assert!(matches!(
        at(&mut state, 1_200, Principal::Custodian, trim),
        Ok(Outcome::Trimmed(_))
    ));

    // A worker that was never leased never served: it is disposable once
    // withdrawn.
    let unleased = enroll_at(&mut state, 1_300);
    grant_at(&mut state, 1_300, unleased);
    assert_eq!(
        at(
            &mut state,
            1_300,
            Principal::Administrator,
            Command::Withdraw {
                enrollment: unleased
            }
        ),
        Ok(Outcome::Withdrawn)
    );
    assert_eq!(
        state.withdrawn_hold_owners(None, 64).collect::<Vec<_>>(),
        [unleased]
    );
    assert_eq!(state.expiry_disposal_time(unleased), Some(0));
    assert_eq!(
        at(
            &mut state,
            1_300,
            Principal::Administrator,
            Command::DisposeExpired {
                enrollment: unleased
            }
        ),
        Ok(Outcome::WorkerDisposed(unleased))
    );
    round_trips(&state);
}

#[test]
fn rotation_fences_the_old_grant_and_preserves_each_record_generation_on_recovery() {
    let initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 2,
            replay_holds: 1,
            retry_positions: 64,
            retained_data_bytes: 1 << 16,
            maintenance_bytes: 1 << 12,
            serving_lease: 1_000,
            clock_drift: 100,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1 << 12,
        },
    )
    .unwrap();
    let mut state = initial.clone();
    let enrollment = enroll(&mut state);
    let worker = Principal::Worker(enrollment);
    let (old, _) = grant(&mut state, enrollment);
    assert_eq!(old.key_generation, 1);

    let append = |state: &mut State, grant| {
        let expected_next = state.head().next_lsn;
        apply(
            state,
            worker,
            Command::Append {
                references: None,
                class: AppendClass::Data,
                grant,
                expected_next,
                timestamp: 1,
                payload: Bytes::from_static(b"ciphertext"),
            },
        )
        .outcome
    };
    assert!(matches!(append(&mut state, old), Ok(Outcome::Appended(_))));
    let Ok(Outcome::Barrier { read, .. }) =
        apply(&mut state, worker, Command::Barrier).outcome
    else {
        panic!("old view was refused");
    };
    let checkpoint = Checkpoint {
        cut: state.head(),
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 2,
            provider: [4; 32],
        },
    };
    let rotate = Command::PublishAndRotate {
        grant: old,
        checkpoint,
    };
    assert_eq!(
        apply(&mut state, worker, rotate.clone()).outcome,
        Err(Refusal::Unauthorized)
    );

    let preparation = CheckpointPreparation {
        erasure: true,
        checkpoint: checkpoint.cut,
        root: checkpoint.root,
        source: old,
        base: initial.checkpoint(),
        custody: checkpoint.custody,
        usable_bytes: 64,
        descriptor: [5; 32],
    };
    let custodian = Principal::Custodian;
    assert_eq!(
        apply(&mut state, custodian, rotate.clone()).outcome,
        Err(Refusal::Unavailable)
    );
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::PrepareCheckpoint {
                preparation,
                references: None
            }
        )
        .outcome,
        Ok(Outcome::CheckpointPrepared(preparation))
    );
    assert_eq!(
        apply(&mut state, custodian, Command::Publish { checkpoint }).outcome,
        Err(Refusal::Conflict)
    );
    assert_eq!(
        apply(&mut state, Principal::RouteReader, rotate.clone()).outcome,
        Err(Refusal::Unauthorized)
    );
    let mut advanced = state.clone();
    assert!(matches!(
        append(&mut advanced, old),
        Ok(Outcome::Appended(_))
    ));
    assert_eq!(
        apply(&mut advanced, custodian, rotate.clone()).outcome,
        Err(Refusal::Stale)
    );

    assert_eq!(advanced.checkpoint(), initial.checkpoint());

    let request = Request {
        placement: state.placement(),
        principal: custodian,
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        command: rotate,
    };
    let frame = service::wire::Operation::Execute(request.clone()).encode(state.placement());
    let (_, service::wire::Operation::Execute(decoded)) =
        service::wire::Operation::decode(frame).unwrap()
    else {
        panic!("not a rotation request");
    };
    assert_eq!(decoded, request);
    let receipt = state
        .apply(state.position() + 1, state.time(), decoded)
        .unwrap();
    let reply = service::wire::Reply::Decision(service::wire::Decision {
        receipt,
        barrier: None,
        rotation: None,
    });
    let service::wire::Reply::Decision(decision) =
        service::wire::Reply::decode(reply.encode()).unwrap()
    else {
        panic!("not a decision reply");
    };
    let Ok(Outcome::Granted {
        grant: new,
        recovery,
    }) = decision.receipt.outcome
    else {
        panic!("rotation was refused");
    };
    assert_eq!(
        new,
        Grant {
            enrollment,
            epoch: old.epoch + 1,
            key_generation: 2
        }
    );
    assert_eq!(state.checkpoint(), checkpoint);
    assert_eq!(state.erasure_floor(), checkpoint.cut.next_lsn);
    assert_eq!(
        apply(
            &mut state,
            worker,
            Command::ProtectRange {
                from: 0,
                through: checkpoint.cut.next_lsn,
            }
        )
        .outcome,
        Err(Refusal::Unavailable)
    );
    assert_eq!(recovery.checkpoint, checkpoint);
    assert_eq!(
        (recovery.start, recovery.through),
        (checkpoint.cut, checkpoint.cut)
    );
    assert_eq!(
        state
            .apply(state.position() + 1, state.time(), request)
            .unwrap(),
        receipt
    );

    assert_eq!(append(&mut state, old), Err(Refusal::Stale));
    let forged = Grant {
        key_generation: old.key_generation,
        ..new
    };
    assert_eq!(append(&mut state, forged), Err(Refusal::Stale));
    assert!(matches!(append(&mut state, new), Ok(Outcome::Appended(_))));

    let image = state.encode_base();
    let mut obsolete = image.to_vec();
    obsolete[..8].copy_from_slice(b"LKBASE04");
    assert!(matches!(
        State::decode_base(&initial, obsolete.into()),
        Err(Refusal::Invalid)
    ));
    let mut recovered = State::decode_base(&initial, image.clone()).unwrap();
    assert_eq!(recovered.encode_base(), image);
    assert_eq!(recovered.erasure_floor(), checkpoint.cut.next_lsn);
    let held = recovered.held_replay(worker, read).unwrap();
    assert_eq!(
        held.records()
            .map(|record| record.grant)
            .collect::<Vec<_>>(),
        [old]
    );
    let suffix = recovered.record(checkpoint.cut.next_lsn).unwrap().clone();
    let reply = service::wire::Reply::Replay(service::ReplayPage {
        checkpoint,
        through: suffix.result.cut,
        records: vec![suffix],
    });
    let service::wire::Reply::Replay(page) = service::wire::Reply::decode(reply.encode()).unwrap()
    else {
        panic!("not a replay reply");
    };
    assert_eq!(page.records[0].grant, new);

    assert_eq!(
        apply(&mut recovered, worker, Command::Vacate { grant: new }).outcome,
        Ok(Outcome::Vacated)
    );
    let mut recovered = State::decode_base(&initial, recovered.encode_base()).unwrap();
    let replacement = enroll(&mut recovered);
    let (replacement, recovery) = grant(&mut recovered, replacement);
    assert_eq!(replacement.key_generation, new.key_generation);
    assert_eq!(recovery.checkpoint, checkpoint);
    assert_eq!(recovery.start, checkpoint.cut);
    assert_eq!(recovery.through, recovered.head());
}

#[test]
fn exact_withdrawal_orders_against_the_retained_tail_preparation_and_held_root() {
    let mut initial = State::new(
        Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        },
        Limits {
            enrolled_workers: 1,
            replay_holds: 4,
            retry_positions: 32,
            retained_data_bytes: 1 << 16,
            maintenance_bytes: 1 << 12,
            serving_lease: 1000,
            clock_drift: 100,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1 << 12,
        },
    )
    .unwrap();
    initial.object_control_bytes = WITHDRAWAL_BYTES + 64;
    let mut state = initial.clone();
    let enrollment = enroll(&mut state);
    let worker = Principal::Worker(enrollment);
    let (writer, startup) = grant(&mut state, enrollment);
    let custodian = Principal::Custodian;
    let object = ObjectWithdrawal {
        name: [6; 32],
        version: [7; 32],
    };
    let withdraw = Command::WithdrawObject { object };
    let append = |state: &mut State, references| {
        let expected_next = state.head().next_lsn;
        apply(
            state,
            worker,
            Command::Append {
                class: AppendClass::Data,
                grant: writer,
                expected_next,
                timestamp: 1,
                payload: Bytes::from_static(b"opaque"),
                references,
            },
        )
        .outcome
    };
    let successor = |state: &State| Checkpoint {
        cut: state.head(),
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: state.checkpoint().custody.revision + 1,
            provider: [4; 32],
        },
    };
    let prepare = |state: &mut State, checkpoint: Checkpoint, names| {
        let preparation = CheckpointPreparation {
            erasure: false,
            checkpoint: checkpoint.cut,
            root: checkpoint.root,
            source: writer,
            base: state.checkpoint(),
            custody: checkpoint.custody,
            usable_bytes: 4096,
            descriptor: [5; 32],
        };
        apply(
            state,
            custodian,
            Command::PrepareCheckpoint {
                preparation,
                references: Some(names),
            },
        )
        .outcome
    };
    assert!(matches!(
        append(&mut state, Some(vec![object.name])),
        Ok(Outcome::Appended(_))
    ));
    assert_eq!(
        apply(&mut state, custodian, withdraw.clone()).outcome,
        Err(Refusal::Conflict)
    );
    assert_eq!(
        apply(&mut state, worker, Command::Release { hold: startup }).outcome,
        Ok(Outcome::Released)
    );

    let first = successor(&state);
    let mut preparation_only = state.clone();
    preparation_only.records.front_mut().unwrap().references = Some(vec![]);
    assert!(matches!(
        prepare(&mut preparation_only, first, vec![object.name]),
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        apply(&mut preparation_only, custodian, withdraw.clone()).outcome,
        Err(Refusal::Conflict)
    );
    assert!(matches!(
        prepare(&mut state, first, vec![object.name]),
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::Publish { checkpoint: first }
        )
        .outcome,
        Ok(Outcome::Published(first))
    );
    assert!(matches!(
        apply(
            &mut state,
            custodian,
            Command::Trim {
                selected: first,
                through: first.cut
            }
        )
        .outcome,
        Ok(Outcome::Trimmed(_))
    ));
    assert_eq!(
        apply(&mut state, custodian, withdraw.clone()).outcome,
        Err(Refusal::Conflict)
    );

    let Ok(Outcome::Barrier { read, .. }) =
        apply(&mut state, worker, Command::Barrier).outcome
    else {
        panic!("read refused");
    };
    assert!(matches!(
        append(&mut state, Some(vec![])),
        Ok(Outcome::Appended(_))
    ));
    let second = successor(&state);
    assert!(matches!(
        prepare(&mut state, second, vec![]),
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::Publish { checkpoint: second }
        )
        .outcome,
        Ok(Outcome::Published(second))
    );
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::CloseCheckpoint { checkpoint: first }
        )
        .outcome,
        Err(Refusal::Unavailable)
    );
    assert_eq!(
        apply(&mut state, custodian, withdraw.clone()).outcome,
        Err(Refusal::Conflict)
    );

    assert_eq!(
        apply(&mut state, worker, Command::Release { hold: read }).outcome,
        Ok(Outcome::Released)
    );
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::CloseCheckpoint { checkpoint: first }
        )
        .outcome,
        Ok(Outcome::CheckpointClosed(first))
    );
    assert_eq!(
        apply(
            &mut state,
            custodian,
            Command::SettleCheckpoint {
                checkpoint: first,
                disposition: [9; 32]
            }
        )
        .outcome,
        Ok(Outcome::CheckpointSettled(first))
    );
    let request = Request {
        placement: state.placement(),
        principal: custodian,
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        command: withdraw.clone(),
    };
    let encoded = service::wire::Operation::Execute(request.clone()).encode(state.placement());
    let (_, service::wire::Operation::Execute(decoded)) =
        service::wire::Operation::decode(encoded).unwrap()
    else {
        panic!("expected withdrawal command");
    };
    let receipt = state
        .apply(state.position() + 1, state.time(), decoded)
        .unwrap();
    let Ok(Outcome::ObjectWithdrawn(fence)) = receipt.outcome else {
        panic!("withdrawal refused: {receipt:?}");
    };
    let reply = service::wire::Reply::Decision(service::wire::Decision {
        receipt,
        barrier: None,
        rotation: None,
    });
    assert!(
        matches!(service::wire::Reply::decode(reply.encode()).unwrap(), service::wire::Reply::Decision(decision) if decision.receipt == receipt)
    );

    let mut recovered = State::decode_base(&initial, state.encode_base()).unwrap();
    assert_eq!(
        recovered
            .apply(recovered.position() + 1, recovered.time(), request)
            .unwrap(),
        receipt
    );
    assert_eq!(
        append(&mut recovered, Some(vec![object.name])),
        Err(Refusal::Conflict)
    );
    assert_eq!(append(&mut recovered, None), Err(Refusal::Unavailable));
    assert!(matches!(
        append(&mut recovered, Some(vec![])),
        Ok(Outcome::Appended(_))
    ));
    let third = successor(&recovered);
    assert_eq!(
        prepare(&mut recovered, third, vec![object.name]),
        Err(Refusal::Conflict)
    );
    assert_eq!(
        apply(
            &mut recovered,
            custodian,
            Command::WithdrawObject {
                object: ObjectWithdrawal {
                    version: [8; 32],
                    ..object
                },
            }
        )
        .outcome,
        Err(Refusal::Conflict)
    );
    assert_eq!(
        apply(
            &mut recovered,
            custodian,
            Command::WithdrawObject {
                object: ObjectWithdrawal {
                    name: [8; 32],
                    ..object
                },
            }
        )
        .outcome,
        Err(Refusal::Capacity)
    );
    for _ in 0..recovered.limits.retry_positions {
        apply(
            &mut recovered,
            custodian,
            Command::CloseCheckpoint { checkpoint: first },
        );
    }
    let mut recovered = State::decode_base(&initial, recovered.encode_base()).unwrap();
    assert_eq!(
        apply(&mut recovered, custodian, withdraw).outcome,
        Ok(Outcome::ObjectWithdrawn(fence))
    );
}

fn codec_initial_state() -> State {
    State::new(
        Placement {
            deployment: Uuid::from_u128(1),
            incarnation: Uuid::from_u128(2),
            group: Uuid::from_u128(3),
            generation: 1,
        },
        Limits {
            enrolled_workers: 1,
            replay_holds: 3,
            retry_positions: 4,
            retained_data_bytes: 8192,
            maintenance_bytes: 4096,
            serving_lease: 1000,
            clock_drift: 100,
        },
        Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::from_u128(4),
                revision: 1,
                provider: [0; 32],
            },
        },
        Window {
            allocation: Uuid::from_u128(5),
            serial: 1,
            bytes: 4096,
        },
    )
    .unwrap()
}

#[test]
fn compact_image_accepts_explicit_empty_object_control() {
    let initial = codec_initial_state();
    let mut state = initial.clone();
    enroll(&mut state);
    let canonical = state.encode_base();
    assert_eq!(
        State::decode_base(&initial, canonical.clone())
            .unwrap()
            .encode_base(),
        canonical
    );

    let mut explicit = canonical.to_vec();
    explicit.extend_from_slice(&0u64.to_be_bytes());
    assert!(matches!(
        State::decode_base(&initial, explicit.clone().into()),
        Err(Refusal::Invalid)
    ));
    explicit.extend_from_slice(&0u64.to_be_bytes());
    let decoded = State::decode_base(&initial, explicit.clone().into()).unwrap();
    assert_ne!(decoded.encode_base().as_ref(), explicit.as_slice());
    assert_eq!(decoded.encode_base(), canonical);
}

#[test]
fn compact_image_accepts_reordered_old_roots_but_rejects_duplicate_revisions() {
    let initial = codec_initial_state();
    let mut state = initial.clone();
    let enrollment = enroll(&mut state);
    let worker = Principal::Worker(enrollment);
    let custodian = Principal::Custodian;
    let (writer, startup) = grant(&mut state, enrollment);
    assert_eq!(
        apply(&mut state, worker, Command::Release { hold: startup }).outcome,
        Ok(Outcome::Released)
    );

    let checkpoints = [2, 3, 4].map(|revision| {
        let next = state.head().next_lsn;
        let appended = apply(
            &mut state,
            worker,
            Command::Append {
                class: AppendClass::Data,
                grant: writer,
                expected_next: next,
                timestamp: 0,
                payload: Bytes::from_static(b"checkpoint boundary"),
                references: None,
            },
        );
        assert!(matches!(appended.outcome, Ok(Outcome::Appended(_))));
        let checkpoint = Checkpoint {
            cut: state.head(),
            root: [1; 32],
            manifest: [2; 32],
            custody: Custody {
                allocation: Uuid::from_u128(revision as u128),
                revision,
                provider: [3; 32],
            },
        };
        let preparation = CheckpointPreparation {
            erasure: false,
            checkpoint: checkpoint.cut,
            root: checkpoint.root,
            source: writer,
            base: state.checkpoint(),
            custody: checkpoint.custody,
            usable_bytes: 4096,
            descriptor: [4; 32],
        };
        assert_eq!(
            apply(
                &mut state,
                custodian,
                Command::PrepareCheckpoint {
                    preparation,
                    references: None,
                },
            )
            .outcome,
            Ok(Outcome::CheckpointPrepared(preparation))
        );
        assert_eq!(
            apply(&mut state, custodian, Command::Publish { checkpoint }).outcome,
            Ok(Outcome::Published(checkpoint))
        );
        checkpoint
    });

    let canonical = state.encode_base();
    let cut_bytes = |checkpoint: Checkpoint| {
        let mut cut = checkpoint.cut.next_lsn.to_be_bytes().to_vec();
        cut.extend_from_slice(&checkpoint.cut.history);
        cut
    };
    const ROOT_ROW_BYTES: usize = 160 + 1;
    let first = cut_bytes(checkpoints[0]);
    let start = canonical
        .windows(first.len())
        .position(|bytes| bytes == first)
        .unwrap();
    let middle = start + ROOT_ROW_BYTES;
    let end = middle + ROOT_ROW_BYTES;
    assert!(canonical[middle..].starts_with(&cut_bytes(checkpoints[1])));
    let mut reordered = canonical.to_vec();
    reordered[start..end].rotate_left(ROOT_ROW_BYTES);
    assert_ne!(&reordered[..], canonical.as_ref());
    assert_eq!(
        State::decode_base(&initial, reordered.into())
            .unwrap()
            .encode_base(),
        canonical
    );

    let mut duplicate = canonical.to_vec();
    duplicate[middle..end].copy_from_slice(&canonical[start..middle]);
    assert!(matches!(
        State::decode_base(&initial, duplicate.into()),
        Err(Refusal::Invalid)
    ));
}

#[test]
fn compact_image_rejects_a_hold_without_its_exact_admission_receipt() {
    let initial = codec_initial_state();
    let mut valid = initial.clone();
    let enrollment = enroll(&mut valid);
    let (_, startup) = grant(&mut valid, enrollment);
    assert!(State::decode_base(&initial, valid.encode_base()).is_ok());

    let key = (Principal::Worker(enrollment), startup.id);
    let mut missing = valid.clone();
    assert!(missing.outcomes.remove(&key).is_some());
    assert!(matches!(
        State::decode_base(&initial, missing.encode_base()),
        Err(Refusal::Invalid)
    ));

    valid.outcomes.get_mut(&key).unwrap().receipt.outcome = Ok(Outcome::Released);
    assert!(matches!(
        State::decode_base(&initial, valid.encode_base()),
        Err(Refusal::Invalid)
    ));
}

#[test]
fn exact_snapshot_hold_pins_an_older_checkpoint_and_its_suffix() {
    let initial = codec_initial_state();
    let mut state = initial.clone();
    let enrollment = enroll(&mut state);
    let worker = Principal::Worker(enrollment);
    let custodian = Principal::Custodian;
    let (grant, _) = grant(&mut state, enrollment);

    let publish = |state: &mut State, revision: u64| {
        let expected_next = state.head.next_lsn;
        let Ok(Outcome::Appended(boundary)) = apply(state, worker, Command::Append {
            references: Some(Vec::new()),
            class: AppendClass::Data,
            grant,
            expected_next,
            timestamp: revision as i64,
            payload: Bytes::from_static(b"snapshot"),
        }).outcome else { panic!("append failed"); };
        let checkpoint = Checkpoint {
            cut: boundary.cut,
            root: [revision as u8; 32],
            manifest: [9; 32],
            custody: Custody { allocation: Uuid::new_v4(), revision, provider: [7; 32] },
        };
        let preparation = CheckpointPreparation {
            erasure: false,
            checkpoint: checkpoint.cut,
            root: checkpoint.root,
            source: grant,
            base: state.checkpoint(),
            custody: checkpoint.custody,
            usable_bytes: 256,
            descriptor: [11; 32],
        };
        assert_eq!(apply(state, custodian, Command::PrepareCheckpoint {
            preparation, references: Some(Vec::new()),
        }).outcome, Ok(Outcome::CheckpointPrepared(preparation)));
        assert_eq!(apply(state, custodian, Command::Publish { checkpoint }).outcome,
            Ok(Outcome::Published(checkpoint)));
        checkpoint
    };

    let older = publish(&mut state, 2);
    let newer = publish(&mut state, 3);
    let command = Command::ProtectCheckpoint {
        root: older.root, from: older.cut.next_lsn, through: newer.cut.next_lsn,
    };
    assert_eq!(apply(&mut state, Principal::RouteReader, command.clone()).outcome, Err(Refusal::Unauthorized));
    assert_eq!(apply(&mut state, worker, Command::ProtectCheckpoint {
        root: newer.root, from: older.cut.next_lsn, through: newer.cut.next_lsn,
    }).outcome, Err(Refusal::Unavailable));

    let request = Request {
        id: RequestId::fresh(state.position(), state.limits.retry_positions).unwrap(),
        principal: worker, placement: state.placement(), command: command.clone(),
    };
    assert_eq!(Request::decode(request.encode()).unwrap(), request);
    let Ok(Outcome::Protected(hold)) = apply(&mut state, worker, command.clone()).outcome
        else { panic!("the older checkpoint was not protected"); };
    assert_eq!((hold.checkpoint, hold.start, hold.through), (older, older.cut, newer.cut));
    let mut replacement = State::decode_base(&initial, state.encode_base()).unwrap();
    assert_eq!(replacement.held_replay(worker, hold).unwrap().records().count(), 1);
    assert_eq!(apply(&mut replacement, custodian, Command::CloseCheckpoint { checkpoint: older }).outcome,
        Err(Refusal::Unavailable));
    assert_eq!(apply(&mut replacement, worker, Command::Release { hold }).outcome, Ok(Outcome::Released));
    assert_eq!(apply(&mut replacement, custodian, Command::CloseCheckpoint { checkpoint: older }).outcome,
        Ok(Outcome::CheckpointClosed(older)));
    assert_eq!(apply(&mut replacement, worker, command).outcome, Err(Refusal::Unavailable));
}
