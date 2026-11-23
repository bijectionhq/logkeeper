use bytes::Bytes;
use logkeeper::ordered::replication::transport::{Connector, RemoteVoter, serve_voter};
use logkeeper::ordered::replication::{DurableVoter, Error, Group, Replica};
use logkeeper::ordered::{
    BarrierClaim, Checkpoint, Command, Cut, Fingerprint, Limits, Outcome, Placement, Principal,
    Refusal, Request, RequestId, Window,
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
    };
    let window = Window {
        allocation: Uuid::new_v4(),
        bytes: 4096,
    };
    let voter_ids = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
    let group = Group::new(
        placement,
        Limits {
            enrolled_workers: 2,
            replay_holds: 4,
            retry_positions: 64,
        },
        seed,
        window,
        voter_ids,
        1 << 20,
    )
    .unwrap();
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

    let append = request(
        Principal::Worker(first_enrollment),
        Command::Append {
            grant: first_grant,
            expected_next: 0,
            timestamp: 11,
            payload: Bytes::from_static(b"chosen"),
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
    let peers: Vec<_> = [1, 2]
        .into_iter()
        .map(|index| {
            let identity = voter_ids[index];
            let voter =
                DurableVoter::recover(group.clone(), identity, directories[index].path()).unwrap();
            let connector = LocalPeer {
                voter,
                group: group.identity(),
            };
            RemoteVoter::new(&group, identity, connector, DEADLINE).unwrap()
        })
        .collect();

    let replacement_request = request(
        Principal::Administrator,
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
        },
    );
    barrier_request.id.expires_at = 8;
    let barrier = group
        .choose(&peers, 8, barrier_request.clone())
        .await
        .unwrap();
    let Outcome::Barrier { grant, read } = barrier.receipt().outcome.unwrap() else {
        panic!("fresh barrier was refused");
    };
    assert_eq!(grant, second_grant);
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
    assert_eq!(records[0].payload, Bytes::from_static(b"chosen"));

    let next = group
        .choose(
            &peers,
            9,
            request(
                Principal::Worker(second_enrollment),
                Command::Append {
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
    assert_eq!(next.allocation, original.allocation);
    assert_eq!(next.byte_start, original.byte_end);
    let reissued = group.choose(&peers, 10, barrier_request).await.unwrap();
    assert_eq!(reissued.receipt(), barrier.receipt());
    assert_eq!(reissued.barrier_claim(), Some(claim));

    let published = Checkpoint {
        cut: next.cut,
        root: [4; 32],
        manifest: [5; 32],
    };
    let worker = Principal::Worker(second_enrollment);
    let publication = group
        .choose(
            &peers,
            11,
            request(
                worker,
                Command::Publish {
                    grant: second_grant,
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
            worker,
            Command::Trim {
                grant: second_grant,
                through: published.cut,
            },
        )
    };
    let blocked = group.choose(&peers, 12, trim()).await.unwrap();
    assert_eq!(blocked.receipt().outcome, Err(Refusal::Unavailable));

    for (round, hold) in [(13, first_recovery), (14, recovery), (15, read)] {
        let release = request(Principal::Worker(hold.owner), Command::Release { hold });
        let released = group.choose(&peers, round, release).await.unwrap();
        assert_eq!(released.receipt().outcome, Ok(Outcome::Released));
    }
    let trimmed = group.choose(&peers, 16, trim()).await.unwrap();
    assert_eq!(
        trimmed.receipt().outcome,
        Ok(Outcome::Trimmed(published.cut))
    );
    assert_eq!(
        trimmed.state().reconcile_append(&append),
        Err(Refusal::Unavailable)
    );
    assert!(matches!(
        trimmed.state().held_replay(reader, read),
        Err(Refusal::Unavailable)
    ));
    assert_eq!(trimmed.state().spent_bytes(), next.byte_end);
}
