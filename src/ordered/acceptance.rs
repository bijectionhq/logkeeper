use super::*;

fn apply(state: &mut State, principal: Principal, command: Command) -> Receipt {
    let id = RequestId::fresh(state.position(), state.limits.retry_positions).unwrap();
    state
        .apply(
            state.position() + 1,
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
            class: AppendClass::Data,
            grant: first_grant,
            expected_next: 0,
            timestamp: 1,
            payload: Bytes::from_static(b"d"),
        },
    };
    let Some(original_receipt) = state
        .apply(state.position() + 1, original.clone())
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
        Command::Barrier {
            grant: first_grant,
            nonce: NonZeroU64::MIN,
        },
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
                grant: successor,
                preparation,
            }
        )
        .outcome,
        Ok(Outcome::CheckpointPrepared(_))
    ));
    assert_eq!(
        apply(
            &mut state,
            Principal::Custodian,
            Command::Publish {
                grant: successor,
                checkpoint
            }
        )
        .outcome,
        Ok(Outcome::Published(checkpoint))
    );
    let trim = Command::Trim {
        grant: successor,
        through: checkpoint.cut,
    };
    assert_eq!(
        apply(&mut state, worker, trim.clone()).outcome,
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
        apply(&mut state, worker, trim).outcome,
        Ok(Outcome::Trimmed(checkpoint.cut))
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
            Command::FundWindow {
                grant: successor,
                window
            }
        )
        .outcome,
        Ok(Outcome::WindowFunded(window))
    );
    assert!(matches!(
        append(&mut recovered, AppendClass::Data),
        Ok(Outcome::Appended(_))
    ));
}
