use bytes::Bytes;
use logkeeper::ordered::TrimResult;
use logkeeper::ordered::replication::transport::{Connector, RemoteVoter, serve_voter};
use logkeeper::ordered::replication::{DurableVoter, Error, Group, Replica};
use logkeeper::ordered::service::{Coordinator, Session, wire};
use logkeeper::ordered::{
    AppendClass, BarrierClaim, Checkpoint, CheckpointPreparation, Command, Custody, Cut,
    Fingerprint, Limits, Outcome, Placement, Principal, Refusal, Request, RequestId, Window,
};
use std::num::NonZeroU64;
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
    let (client, server) = tokio::io::duplex(4096);
    let (reply, served) = tokio::join!(
        wire::exchange(client, placement, operation, 16_384, DEADLINE),
        wire::serve(coordinator, server, session, 16_384, DEADLINE, |_| panic!(
            "unexpected barrier in test exchange"
        )),
    );
    served.unwrap();
    reply.unwrap()
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
        Command::Barrier {
            grant: second_grant,
            nonce: NonZeroU64::MIN,
        },
    );
    barrier_request.id.expires_at = 8;
    let barrier = group
        .choose(&peers, 8, barrier_request.clone())
        .await
        .unwrap();
    let Outcome::Barrier { grant, nonce, read } = barrier.receipt().outcome.unwrap() else {
        panic!("fresh barrier was refused");
    };
    assert_eq!(grant, second_grant);
    assert_eq!(nonce, NonZeroU64::MIN);
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
    let reissued = group.choose(&peers, 10, barrier_request).await.unwrap();
    assert_eq!(reissued.receipt(), barrier.receipt());
    assert_eq!(reissued.barrier_claim(), Some(claim));

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
            11,
            request(
                Principal::Custodian,
                Command::PrepareCheckpoint { preparation },
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
            12,
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
    let blocked = group.choose(&peers, 13, trim()).await.unwrap();
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

    for (round, hold) in [(14, first_recovery), (15, recovery), (16, read)] {
        let release = request(Principal::Worker(hold.owner), Command::Release { hold });
        let released = group.choose(&peers, round, release).await.unwrap();
        assert_eq!(released.receipt().outcome, Ok(Outcome::Released));
    }
    let trimmed = group.choose(&peers, 17, trim()).await.unwrap();
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
    group.compact(&peers, 18).await.unwrap();
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
    let reopened = group.recover(&peers, 19).await.unwrap();
    assert_eq!(reopened.position(), trimmed.state().position());
    assert_eq!(
        reopened.command_history(),
        trimmed.state().command_history()
    );
    assert_eq!(reopened.writer_state(), trimmed.state().writer_state());
    assert_eq!(reopened.floor(), published.cut);
    assert_eq!(reopened.window(), window);
    assert_eq!(reopened.reconcile_append(&append), Ok(original));

    let marker = |nonce| {
        request(
            reader,
            Command::Barrier {
                grant: second_grant,
                nonce,
            },
        )
    };
    let spent = group
        .choose(&peers, 20, marker(NonZeroU64::MIN))
        .await
        .unwrap();
    assert_eq!(spent.receipt().outcome, Err(Refusal::Stale));

    let pending = marker(NonZeroU64::new(3).unwrap());
    let ahead = group.choose(&peers, 21, pending.clone()).await.unwrap();
    assert_eq!(ahead.receipt().outcome, Err(Refusal::ReadPending));
    let abandoned = group
        .choose(
            &peers,
            22,
            request(
                reader,
                Command::AbandonRead {
                    grant: second_grant,
                    nonce: NonZeroU64::new(2).unwrap(),
                },
            ),
        )
        .await
        .unwrap();
    assert_eq!(abandoned.receipt().outcome, Ok(Outcome::ReadAbandoned));
    let admitted = group.choose(&peers, 23, pending).await.unwrap();
    let proof = admitted.barrier_claim().unwrap();
    assert_eq!(proof.nonce().get(), 3);
    assert_eq!(proof.read().through, published.cut);

    let unsupported = group
        .choose(
            &peers,
            24,
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
            25,
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
            class: AppendClass::Data,
            grant: second_grant,
            expected_next: published.cut.next_lsn,
            timestamp: 14,
            payload: Bytes::from_static(b"after funding"),
        },
    );
    let appended = group.choose(&peers, 26, newest.clone()).await.unwrap();
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
    let chosen = group.choose(&old_peers, 100, seal).await.unwrap();
    assert_eq!(
        chosen.receipt().outcome,
        Ok(Outcome::CohortSealed(repaired.identity()))
    );
    let old_append = request(
        worker,
        Command::Append {
            class: AppendClass::Data,
            grant: second_grant,
            expected_next: result.cut.next_lsn,
            timestamp: 15,
            payload: Bytes::from_static(b"old voter scope"),
        },
    );
    assert!(matches!(
        group.choose(&old_peers, 101, old_append).await,
        Err(Error::Sealed)
    ));

    let inherited = group.repair_seed(&old_peers, 102, &repaired).await.unwrap();
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
