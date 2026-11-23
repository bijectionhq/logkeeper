use bytes::Bytes;
use logkeeper::ordered::TrimResult;
use logkeeper::ordered::replication::transport::{Connector, RemoteVoter, serve_voter};
use logkeeper::ordered::replication::{DurableVoter, Error, Group, Replica};
use logkeeper::ordered::service::{Coordinator, Session, wire};
use logkeeper::ordered::{
    AppendClass, BarrierClaim, Checkpoint, CheckpointPreparation, Command, Custody, Cut,
    Enrollment, Fingerprint, Limits, Outcome, Placement, Principal, Refusal, Request, RequestId,
    Window,
};
use std::time::Duration;
use uuid::Uuid;

const DEADLINE: Duration = Duration::from_secs(10);

struct LocalPeer {
    voter: DurableVoter,
    group: Fingerprint,
}

impl Connector for LocalPeer {
    type Stream = tokio::io::DuplexStream;

    async fn connect(&self, group: Fingerprint, voter: Uuid) -> Result<Self::Stream, Error> {
        if group != self.group || voter != self.voter.identity() {
            return Err(Error::Group);
        }
        let (client, server) = tokio::io::duplex(4096);
        let voter = self.voter.clone();
        tokio::spawn(async move { serve_voter(&voter, server, group, DEADLINE).await });
        Ok(client)
    }
}

async fn application<R: Replica>(
    coordinator: &Coordinator<R>,
    placement: Placement,
    session: Session,
    operation: wire::Operation,
) -> wire::Reply {
    application_with_frame(coordinator, placement, session, operation, 16_384).await
}

async fn application_with_frame<R: Replica>(
    coordinator: &Coordinator<R>,
    placement: Placement,
    session: Session,
    operation: wire::Operation,
    frame: usize,
) -> wire::Reply {
    let (client, server) = tokio::io::duplex(4096);
    let (reply, served) = tokio::join!(
        wire::exchange(client, placement, operation, frame, DEADLINE),
        wire::serve(coordinator, server, session, frame, DEADLINE, |_| panic!(
            "unexpected barrier in test exchange"
        )),
    );
    served.unwrap();
    reply.unwrap()
}

#[tokio::test]
async fn only_the_custodian_can_page_withdrawn_hold_owners_over_the_application_wire() {
    use logkeeper::ordered::service::WithdrawnWorker;

    let placement = Placement {
        deployment: Uuid::new_v4(),
        incarnation: Uuid::new_v4(),
        group: Uuid::new_v4(),
        generation: 1,
    };
    let limits = Limits {
        enrolled_workers: 1,
        replay_holds: 8,
        retry_positions: 64,
        retained_data_bytes: 8192,
        maintenance_bytes: 1024,
        serving_lease: 100,
        clock_drift: 20,
    };
    let voter_ids = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
    let group = Group::new(
        placement,
        limits,
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
            bytes: 4096,
        },
        voter_ids,
        1 << 20,
    )
    .unwrap();
    let media = voter_ids.map(|_| tempfile::tempdir().unwrap());
    let peers: Vec<_> = voter_ids
        .into_iter()
        .zip(&media)
        .map(|(id, dir)| DurableVoter::initialize(group.clone(), id, dir.path()).unwrap())
        .collect();
    let choose = async |round, principal, command| {
        group
            .choose_at(
                &peers,
                round,
                1_000,
                Request {
                    placement,
                    principal,
                    id: RequestId {
                        nonce: Uuid::new_v4(),
                        expires_at: 64,
                    },
                    command,
                },
            )
            .await
            .unwrap()
    };
    let worker = Uuid::new_v4();
    let mut expected = Vec::new();
    let mut round = 1;
    for serial in 1..=4 {
        let enrollment = Enrollment { worker, serial };
        let admin = Principal::Administrator;
        let enrolled = choose(
            round,
            admin,
            Command::Enroll {
                worker,
                expected: None,
            },
        )
        .await;
        assert_eq!(
            enrolled.receipt().outcome,
            Ok(Outcome::Enrolled(enrollment))
        );
        let principal = Principal::Worker(enrollment);
        let claimed = choose(
            round + 1,
            principal,
            Command::Grant {
                expected: enrolled.state().writer_state(),
                candidate: enrollment,
            },
        )
        .await;
        let Ok(Outcome::Granted { grant, .. }) = claimed.receipt().outcome else {
            panic!("recovery hold was not admitted");
        };
        if serial == 4 {
            break;
        }
        let eligible_at = if serial == 1 {
            let leased = choose(round + 2, principal, Command::Lease { grant }).await;
            assert_eq!(
                leased.receipt().outcome,
                Ok(Outcome::Leased {
                    grant,
                    issued_at: 1_000,
                    lease_end: 1_100,
                })
            );
            1_120
        } else {
            0
        };
        let withdrawn = choose(round + 3, admin, Command::Withdraw { enrollment }).await;
        assert_eq!(withdrawn.receipt().outcome, Ok(Outcome::Withdrawn));
        expected.push(WithdrawnWorker {
            enrollment,
            eligible_at: Some(eligible_at),
        });
        round += 4;
    }
    let coordinator = Coordinator::new(group, peers);
    let query = async |principal, after| {
        application_with_frame(
            &coordinator,
            placement,
            Session::authenticated(placement, principal),
            wire::Operation::WithdrawnWorkers { after },
            82,
        )
        .await
    };
    for principal in [
        Principal::Administrator,
        Principal::RouteReader,
        Principal::Worker(Enrollment { worker, serial: 4 }),
    ] {
        assert!(matches!(
            query(principal, None).await,
            wire::Reply::Refused(Refusal::Unauthorized)
        ));
    }
    let custody = Principal::Custodian;
    let wire::Reply::WithdrawnWorkers(first) = query(custody, None).await else {
        panic!("withdrawn workers were not returned");
    };
    assert_eq!(first, expected[..2]);
    let wire::Reply::WithdrawnWorkers(second) = query(custody, Some(first[1].enrollment)).await
    else {
        panic!("next withdrawn workers were not returned");
    };
    assert_eq!(second, expected[2..]);
    assert!(matches!(
        query(custody, Some(second[0].enrollment)).await,
        wire::Reply::WithdrawnWorkers(last) if last.is_empty()
    ));
}

#[tokio::test]
async fn a_surviving_group_recovers_the_grant_and_preserves_the_paid_append_window() {
    let placement = Placement {
        deployment: Uuid::new_v4(),
        incarnation: Uuid::new_v4(),
        group: Uuid::new_v4(),
        generation: 1,
    };
    let seed = Checkpoint {
        cut: Cut {
            next_lsn: 0,
            history: [1; 32],
        },
        root: [2; 32],
        manifest: [3; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 1,
            provider: [7; 32],
        },
    };
    let window = Window {
        allocation: Uuid::new_v4(),
        serial: 1,
        bytes: 4096,
    };
    let voter_ids = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
    let limits = Limits {
        enrolled_workers: 2,
        replay_holds: 4,
        retry_positions: 64,
        retained_data_bytes: 8192,
        maintenance_bytes: 1024,
        serving_lease: 30_000,
        clock_drift: 1_000,
    };
    let group = Group::new(placement, limits, seed, window, voter_ids, 1 << 20).unwrap();
    let directories = std::array::from_fn::<_, 3, _>(|_| tempfile::tempdir().unwrap());
    let mut peers: Vec<_> = voter_ids
        .into_iter()
        .zip(&directories)
        .map(|(id, dir)| DurableVoter::initialize(group.clone(), id, dir.path()).unwrap())
        .collect();

    let request = |principal, command| Request {
        placement,
        principal,
        id: RequestId {
            nonce: Uuid::new_v4(),
            expires_at: 64,
        },
        command,
    };
    let enroll = |worker| {
        request(
            Principal::Administrator,
            Command::Enroll {
                worker,
                expected: None,
            },
        )
    };

    let first = group
        .choose(&peers[..2], 1, enroll(Uuid::new_v4()))
        .await
        .unwrap();
    let Outcome::Enrolled(first_enrollment) = first.receipt().outcome.unwrap() else {
        panic!("worker was not enrolled");
    };
    let second = group
        .choose(&peers[..2], 2, enroll(Uuid::new_v4()))
        .await
        .unwrap();
    let Outcome::Enrolled(second_enrollment) = second.receipt().outcome.unwrap() else {
        panic!("worker was not enrolled");
    };
    let old = group
        .choose(
            &peers[..2],
            3,
            request(
                Principal::Administrator,
                Command::Grant {
                    expected: second.state().writer_state(),
                    candidate: first_enrollment,
                },
            ),
        )
        .await
        .unwrap();
    let Outcome::Granted {
        grant: first_grant,
        recovery: first_recovery,
    } = old.receipt().outcome.unwrap()
    else {
        panic!("writer was not granted");
    };

    let original_payload = Bytes::from_static(&[0xc7; 2048]);
    let append = request(
        Principal::Worker(first_enrollment),
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: first_grant,
            expected_next: 0,
            timestamp: 11,
            payload: original_payload.clone(),
        },
    );
    let first_append = group.choose(&peers[..2], 4, append.clone()).await.unwrap();
    let Outcome::Appended(original) = first_append.receipt().outcome.unwrap() else {
        panic!("append was not chosen");
    };
    let previous = first_append.state().writer_state();

    // Discard the in-memory voters after the choice and reopen only two of the
    // original durable identities. The original caller lost its reply.
    peers.clear();
    let reopen = |members: [usize; 2]| {
        members
            .into_iter()
            .map(|index| {
                let identity = voter_ids[index];
                let voter =
                    DurableVoter::recover(group.clone(), identity, directories[index].path())
                        .unwrap();
                let connector = LocalPeer {
                    voter,
                    group: group.identity(),
                };
                RemoteVoter::new(&group, identity, connector, DEADLINE).unwrap()
            })
            .collect::<Vec<_>>()
    };
    let peers = reopen([1, 2]);

    let replacement_request = request(
        Principal::Worker(second_enrollment),
        Command::Grant {
            expected: previous,
            candidate: second_enrollment,
        },
    );
    let replacement = group
        .choose(&peers, 5, replacement_request.clone())
        .await
        .unwrap();
    let Outcome::Granted {
        grant: second_grant,
        recovery,
    } = replacement.receipt().outcome.unwrap()
    else {
        panic!("replacement was not granted");
    };
    assert_eq!(recovery.checkpoint, seed);
    assert_eq!(recovery.through, original.cut);
    assert_eq!(replacement.state().window(), window);
    assert_eq!(replacement.state().spent_bytes(), original.byte_end);
    assert_eq!(replacement.state().reconcile_append(&append), Ok(original));

    let mut rival = append.clone();
    let Command::Append { payload, .. } = &mut rival.command else {
        unreachable!()
    };
    *payload = Bytes::from_static(b"rival");
    assert_eq!(
        replacement.state().reconcile_append(&rival),
        Err(Refusal::Conflict)
    );
    let retry = group.choose(&peers, 6, replacement_request).await.unwrap();
    assert_eq!(retry.receipt(), replacement.receipt());
    assert_eq!(retry.prefix(), replacement.prefix());

    let delayed = group
        .choose(
            &peers,
            7,
            request(
                Principal::Worker(first_enrollment),
                Command::Append {
                    references: None,
                    class: AppendClass::Data,
                    grant: first_grant,
                    expected_next: 1,
                    timestamp: 12,
                    payload: Bytes::from_static(b"stale"),
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(delayed.receipt().outcome, Err(Refusal::Stale));
    let mut barrier_request = request(
        Principal::Worker(second_enrollment),
        Command::Barrier,
    );
    barrier_request.id.expires_at = 8;
    let barrier = group
        .choose(&peers, 8, barrier_request.clone())
        .await
        .unwrap();
    let Outcome::Barrier { read } = barrier.receipt().outcome.unwrap() else {
        panic!("fresh barrier was refused");
    };
    assert_eq!(read.owner, second_enrollment);
    assert_eq!(read.through, original.cut);
    assert_eq!(read.checkpoint, seed);
    let claim = barrier.barrier_claim().unwrap();
    assert_eq!(BarrierClaim::decode(claim.encode()).unwrap(), claim);
    let reader = Principal::Worker(second_enrollment);
    let replay = barrier.state().held_replay(reader, read).unwrap();
    assert_eq!(replay.checkpoint(), seed);
    assert_eq!(replay.through(), original.cut);
    let records: Vec<_> = replay.records().collect();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].result, original);
    assert_eq!(records[0].payload, original_payload);

    let next = group
        .choose(
            &peers,
            9,
            request(
                Principal::Worker(second_enrollment),
                Command::Append {
                    references: None,
                    class: AppendClass::Data,
                    grant: second_grant,
                    expected_next: 1,
                    timestamp: 13,
                    payload: Bytes::from_static(b"next"),
                },
            ),
        )
        .await
        .unwrap();
    let Outcome::Appended(next) = next.receipt().outcome.unwrap() else {
        panic!("successor could not append");
    };
    assert_eq!(next.lsn, 1);
    assert_eq!(next.window, original.window);
    assert_eq!(next.byte_start, original.byte_end);
    // A read has no exact lost-reply recovery. Its retry is a new admission
    // at the same grant, observing at or after the original cut.
    let retry = request(
        Principal::Worker(second_enrollment),
        Command::Barrier,
    );
    let retried = group.choose(&peers, 10, retry).await.unwrap();
    let retried_claim = retried.barrier_claim().unwrap();
    let retried = retried_claim.read();
    assert_eq!(retried.owner, second_enrollment);
    assert_ne!(retried.id, read.id);
    assert!(retried.admitted_at > read.admitted_at);
    assert!(retried.through.next_lsn >= read.through.next_lsn);
    assert_eq!(retried.through, next.cut);
    // The original identity is spent: the exact reissue is never answered
    // with the original receipt and never admits a second hold.
    let reissued = group.choose(&peers, 11, barrier_request).await.unwrap();
    assert_eq!(reissued.receipt().outcome, Err(Refusal::Conflict));
    assert_eq!(reissued.barrier_claim(), None);
    let still = reissued.state().held_replay(reader, read).unwrap();
    assert_eq!(still.through(), original.cut);

    let published = Checkpoint {
        cut: next.cut,
        root: [4; 32],
        manifest: [5; 32],
        custody: Custody {
            allocation: Uuid::new_v4(),
            revision: 2,
            provider: [7; 32],
        },
    };
    let worker = Principal::Worker(second_enrollment);
    let preparation = CheckpointPreparation {
        erasure: false,
        checkpoint: published.cut,
        root: published.root,
        source: second_grant,
        base: seed,
        custody: published.custody,
        usable_bytes: 1 << 20,
        descriptor: [6; 32],
    };
    let prepare = group
        .choose(
            &peers,
            13,
            request(
                Principal::Custodian,
                Command::PrepareCheckpoint {
                    preparation,
                    references: None,
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(
        prepare.receipt().outcome,
        Ok(Outcome::CheckpointPrepared(preparation))
    );
    let publication = group
        .choose(
            &peers,
            14,
            request(
                Principal::Custodian,
                Command::Publish {
                    checkpoint: published,
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(
        publication.receipt().outcome,
        Ok(Outcome::Published(published))
    );
    let trim = || {
        request(
            Principal::Custodian,
            Command::Trim {
                selected: published,
                through: published.cut,
            },
        )
    };
    let blocked = group.choose(&peers, 15, trim()).await.unwrap();
    assert_eq!(blocked.receipt().outcome, Err(Refusal::Unavailable));
    let medium = || {
        ["ordered.slot-a", "ordered.slot-b"]
            .map(|file| std::fs::read(directories[1].path().join(file)).unwrap())
    };
    let retained = medium();
    assert!(retained.iter().any(|slot| {
        slot.windows(original_payload.len())
            .any(|range| range == original_payload.as_ref())
    }));

    for (round, hold) in [
        (16, first_recovery),
        (17, recovery),
        (18, read),
        (19, retried),
    ] {
        let release = request(Principal::Worker(hold.owner), Command::Release { hold });
        let released = group.choose(&peers, round, release).await.unwrap();
        assert_eq!(released.receipt().outcome, Ok(Outcome::Released));
    }
    let trimmed = group.choose(&peers, 20, trim()).await.unwrap();
    assert_eq!(
        trimmed.receipt().outcome,
        Ok(Outcome::Trimmed(TrimResult {
            from: seed.cut,
            through: published.cut,
            ordinary_bytes: (original.byte_end - original.byte_start)
                + (next.byte_end - next.byte_start),
            maintenance_bytes: 0,
        }))
    );
    assert_eq!(trimmed.state().reconcile_append(&append), Ok(original));
    assert!(matches!(
        trimmed.state().held_replay(reader, read),
        Err(Refusal::Unavailable)
    ));
    assert_eq!(trimmed.state().spent_bytes(), next.byte_end);
    group.compact(&peers, 21).await.unwrap();
    let reclaimed = medium();
    assert!(
        reclaimed
            .iter()
            .zip(retained)
            .all(|(current, previous)| current.len() == previous.len())
    );
    assert!(reclaimed.iter().all(|slot| {
        !slot
            .windows(original_payload.len())
            .any(|range| range == original_payload.as_ref())
    }));

    drop(peers);
    let peers = reopen([0, 1]);
    let reopened = group.recover(&peers, 22).await.unwrap();
    assert_eq!(reopened.position(), trimmed.state().position());
    assert_eq!(
        reopened.command_history(),
        trimmed.state().command_history()
    );
    assert_eq!(reopened.writer_state(), trimmed.state().writer_state());
    assert_eq!(reopened.floor(), published.cut);
    assert_eq!(reopened.window(), window);
    assert_eq!(reopened.reconcile_append(&append), Ok(original));

    // A refused read takes no state: there is nothing to abandon, and its
    // exact reissue is decided afresh at a later position.
    let deposed = request(
        Principal::Worker(Enrollment { worker: Uuid::new_v4(), serial: 1 }),
        Command::Barrier,
    );
    let blocked = group.choose(&peers, 23, deposed.clone()).await.unwrap();
    assert_eq!(blocked.receipt().outcome, Err(Refusal::Stale));
    let again = group.choose(&peers, 24, deposed).await.unwrap();
    assert_eq!(again.receipt().outcome, Err(Refusal::Stale));
    assert!(again.receipt().position > blocked.receipt().position);
    let admitted = group
        .choose(
            &peers,
            25,
            request(
                reader,
                Command::Barrier,
            ),
        )
        .await
        .unwrap();
    let proof = admitted.barrier_claim().unwrap();
    assert_eq!(proof.read().through, published.cut);

    let unsupported = group
        .choose(
            &peers,
            26,
            request(
                worker,
                Command::Publish {
                    checkpoint: published,
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(unsupported.receipt().outcome, Err(Refusal::Unauthorized));

    let next_window = Window {
        allocation: Uuid::new_v4(),
        serial: 2,
        bytes: 4096,
    };
    let funded = group
        .choose(
            &peers,
            27,
            request(
                Principal::Custodian,
                Command::FundWindow {
                    window: next_window,
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(
        funded.receipt().outcome,
        Ok(Outcome::WindowFunded(next_window))
    );
    assert_eq!(funded.state().head(), published.cut);
    assert_eq!(funded.state().spent_bytes(), 0);
    let newest = request(
        worker,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: second_grant,
            expected_next: published.cut.next_lsn,
            timestamp: 14,
            payload: Bytes::from_static(b"after funding"),
        },
    );
    let appended = group.choose(&peers, 28, newest.clone()).await.unwrap();
    let Outcome::Appended(result) = appended.receipt().outcome.unwrap() else {
        panic!("the next funded allocation was refused");
    };
    assert_eq!(result.window, next_window);
    assert_eq!(result.byte_start, 0);

    let coordinator = Coordinator::new(group.clone(), peers);
    let session = Session::authenticated(placement, worker);
    let route = application(&coordinator, placement, session, wire::Operation::Route).await;
    let wire::Reply::Route(route) = route else {
        panic!("the installed writer unrouteable");
    };
    assert_eq!(route.writer.grant, Some(second_grant));
    assert_eq!(route.head, result.cut);
    let reply = application(
        &coordinator,
        placement,
        session,
        wire::Operation::Reconcile {
            grant: second_grant,
            original: newest.clone(),
        },
    )
    .await;
    assert!(matches!(reply, wire::Reply::Reconciled(prior) if prior == result));

    let forged = request(
        Principal::Custodian,
        Command::Publish {
            checkpoint: published,
        },
    );
    let refusal = application(
        &coordinator,
        placement,
        session,
        wire::Operation::Execute(forged),
    )
    .await;
    assert!(matches!(
        refusal,
        wire::Reply::Refused(Refusal::Unauthorized)
    ));

    let historic = application(
        &coordinator,
        placement,
        session,
        wire::Operation::Replay {
            hold: proof.read(),
            from: proof.read().checkpoint.cut,
            maximum_bytes: 4096,
        },
    )
    .await;
    assert!(
        matches!(historic, wire::Reply::Replay(page) if page.records.is_empty() && page.through == published.cut)
    );

    let replacement_id = Uuid::new_v4();
    let repaired = Group::new(
        placement,
        limits,
        seed,
        window,
        [voter_ids[0], voter_ids[1], replacement_id],
        1 << 20,
    )
    .unwrap()
    .successor(group.identity())
    .unwrap();
    let new_media = [tempfile::tempdir().unwrap(), tempfile::tempdir().unwrap()];
    let surviving_ids = [voter_ids[1], replacement_id];
    for (dir, voter) in new_media.iter().zip(surviving_ids) {
        DurableVoter::reserve_repair(&repaired, voter, dir.path()).unwrap();
        assert!(matches!(
            DurableVoter::recover(repaired.clone(), voter, dir.path()),
            Err(Error::Stopped)
        ));
    }

    drop(coordinator);
    let old_peers = reopen([0, 1]);
    let seal = request(
        Principal::Administrator,
        Command::SealCohort {
            expected: group.identity(),
            successor: repaired.identity(),
        },
    );
    // A proposer cannot stamp a decision below the chosen journal time.
    assert!(matches!(
        group.choose_at(&old_peers, 100, 0, seal.clone()).await,
        Err(Error::Time)
    ));
    let chosen = group.choose(&old_peers, 101, seal).await.unwrap();
    assert_eq!(
        chosen.receipt().outcome,
        Ok(Outcome::CohortSealed(repaired.identity()))
    );
    let old_append = request(
        worker,
        Command::Append {
            references: None,
            class: AppendClass::Data,
            grant: second_grant,
            expected_next: result.cut.next_lsn,
            timestamp: 15,
            payload: Bytes::from_static(b"old voter scope"),
        },
    );
    assert!(matches!(
        group.choose(&old_peers, 102, old_append).await,
        Err(Error::Sealed)
    ));

    let inherited = group.repair_seed(&old_peers, 103, &repaired).await.unwrap();
    let new_peers: Vec<_> = new_media
        .iter()
        .zip(surviving_ids)
        .map(|(dir, voter)| {
            DurableVoter::initialize_repaired(repaired.clone(), voter, dir.path(), &inherited)
                .unwrap()
        })
        .collect();
    let state = repaired.recover(&new_peers, 2).await.unwrap();
    assert_eq!(state.writer_state().grant, Some(second_grant));
    assert_eq!(state.head(), result.cut);
    assert_eq!(state.window(), next_window);
    assert_eq!(state.reconcile_append(&newest), Ok(result));
    assert_eq!(state.command_history(), chosen.state().command_history());
}

#[tokio::test]
async fn exact_object_withdrawal_survives_compaction_and_cohort_repair() {
    use logkeeper::ordered::ObjectWithdrawal;

    let placement = Placement {
        deployment: Uuid::new_v4(),
        incarnation: Uuid::new_v4(),
        group: Uuid::new_v4(),
        generation: 1,
    };
    let limits = Limits {
        enrolled_workers: 1,
        replay_holds: 2,
        retry_positions: 64,
        retained_data_bytes: 1 << 16,
        maintenance_bytes: 1 << 12,
        serving_lease: 30_000,
        clock_drift: 1_000,
    };
    let initial = Checkpoint {
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
    };
    let window = Window {
        allocation: Uuid::new_v4(),
        serial: 1,
        bytes: 1 << 12,
    };
    let peers = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
    let group = Group::new(placement, limits, initial, window, peers, 1 << 20).unwrap();
    let disks = std::array::from_fn::<_, 3, _>(|_| tempfile::tempdir().unwrap());
    let voters: Vec<_> = disks
        .iter()
        .zip(peers)
        .map(|(disk, id)| DurableVoter::initialize(group.clone(), id, disk.path()).unwrap())
        .collect();
    let request = |principal, command| Request {
        placement,
        principal,
        id: RequestId {
            nonce: Uuid::new_v4(),
            expires_at: 64,
        },
        command,
    };
    let administrator = Principal::Administrator;
    let custodian = Principal::Custodian;
    let enrolled = group
        .choose(
            &voters,
            1,
            request(
                administrator,
                Command::Enroll {
                    worker: Uuid::new_v4(),
                    expected: None,
                },
            ),
        )
        .await
        .unwrap();
    let Ok(Outcome::Enrolled(enrollment)) = enrolled.receipt().outcome else {
        panic!("enrollment refused");
    };
    let worker = Principal::Worker(enrollment);
    let installed = group
        .choose(
            &voters,
            2,
            request(
                worker,
                Command::Grant {
                    expected: enrolled.state().writer_state(),
                    candidate: enrollment,
                },
            ),
        )
        .await
        .unwrap();
    let Ok(Outcome::Granted { grant, .. }) = installed.receipt().outcome else {
        panic!("grant refused");
    };
    let object = ObjectWithdrawal {
        name: [6; 32],
        version: [7; 32],
    };
    let withdrawal = request(custodian, Command::WithdrawObject { object });
    let original = group
        .choose(&voters, 3, withdrawal.clone())
        .await
        .unwrap()
        .receipt();
    assert!(
        matches!(original.outcome, Ok(Outcome::ObjectWithdrawn(fence)) if fence.object == object)
    );

    let mut before = [0; 32];
    for round in 4..20 {
        let refused = group
            .choose(
                &voters,
                round,
                request(Principal::RouteReader, Command::Barrier),
            )
            .await
            .unwrap();
        assert_eq!(refused.receipt().outcome, Err(Refusal::Unauthorized));
        before = refused.prefix();
    }
    group.compact(&voters, 20).await.unwrap();
    let recovered = group.choose(&voters, 21, withdrawal.clone()).await.unwrap();
    assert_eq!(recovered.receipt(), original);
    assert_ne!(recovered.prefix(), before);

    let target_ids = [peers[1], peers[2], Uuid::new_v4()];
    let successor = Group::new(placement, limits, initial, window, target_ids, 1 << 20)
        .unwrap()
        .successor(group.identity())
        .unwrap();
    group
        .choose(
            &voters,
            22,
            request(
                administrator,
                Command::SealCohort {
                    expected: group.identity(),
                    successor: successor.identity(),
                },
            ),
        )
        .await
        .unwrap();
    let seed = group.repair_seed(&voters, 23, &successor).await.unwrap();
    let media = std::array::from_fn::<_, 3, _>(|_| tempfile::tempdir().unwrap());
    let repaired: Vec<_> = media
        .iter()
        .zip(target_ids)
        .map(|(disk, id)| {
            DurableVoter::reserve_repair(&successor, id, disk.path()).unwrap();
            DurableVoter::initialize_repaired(successor.clone(), id, disk.path(), &seed).unwrap()
        })
        .collect();
    let recovered = successor
        .choose(&repaired, 1, withdrawal)
        .await
        .unwrap()
        .receipt();
    assert_eq!(recovered, original);
    let late = successor
        .choose(
            &repaired,
            2,
            request(
                worker,
                Command::Append {
                    class: AppendClass::Data,
                    grant,
                    expected_next: 0,
                    timestamp: 1,
                    payload: Bytes::from_static(b"late"),
                    references: Some(vec![object.name]),
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(late.receipt().outcome, Err(Refusal::Conflict));

    let names = (10..18).map(|index| [index; 32]).collect::<Vec<_>>();
    let appended = successor
        .choose(
            &repaired,
            3,
            request(
                worker,
                Command::Append {
                    class: AppendClass::Data,
                    grant,
                    expected_next: 0,
                    timestamp: 2,
                    payload: Bytes::from_static(b"references"),
                    references: Some(names.clone()),
                },
            ),
        )
        .await
        .unwrap();
    let Ok(Outcome::Appended(row)) = appended.receipt().outcome else {
        panic!("unfenced references refused");
    };
    let chosen = successor
        .choose(
            &repaired,
            4,
            request(
                worker,
                Command::Protect {
                    grant,
                    through: row.cut,
                },
            ),
        )
        .await
        .unwrap();
    let Ok(Outcome::Protected(hold)) = chosen.receipt().outcome else {
        panic!("replay hold refused");
    };
    let coordinator = Coordinator::new(successor, repaired);
    let session = Session::authenticated(placement, worker);
    let head = application(
        &coordinator,
        placement,
        session,
        wire::Operation::ReplayHead {
            hold,
            from: initial.cut,
        },
    )
    .await;
    let wire::Reply::ReplayHead(Some(head)) = head else {
        panic!("replay head absent");
    };
    assert_eq!(head.payload_bytes, 10);
    assert_eq!(
        head.record_bytes,
        head.payload_bytes
            + logkeeper::ordered::APPEND_RECORD_CHARGE_BYTES
            + 4
            + 32 * names.len() as u64
    );
    for maximum_bytes in [head.record_bytes - 1, head.record_bytes] {
        let reply = application(
            &coordinator,
            placement,
            session,
            wire::Operation::Replay {
                hold,
                from: initial.cut,
                maximum_bytes,
            },
        )
        .await;
        if maximum_bytes == head.record_bytes {
            assert!(
                matches!(reply, wire::Reply::Replay(page) if page.records.len() == 1 && page.records[0].references.as_ref() == Some(&names))
            );
        } else {
            assert!(matches!(reply, wire::Reply::Refused(Refusal::Capacity)));
        }
    }
}
