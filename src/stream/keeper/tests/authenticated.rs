//! Keeper ledger: signing committed prefixes, durability across trim and
//! restart, and seeding a replacement keeper that never held the trimmed prefix.

use ring::signature::{Ed25519KeyPair, KeyPair};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use crate::stream::authenticated::{
    Head, HeadSignature, KeeperKeys as Installed, Leaf, SignedHead, Signer, Tree, TrustedKeeper,
    protocol::{AuthReply, AuthRequest, decode, encode},
};

use super::*;

const JOURNAL: Uuid = Uuid::from_u128(77);
const RECORDS: [&[u8]; 4] = [b"one", b"two", b"three", b"four"];

fn pair(keeper: KeeperId) -> Ed25519KeyPair {
    Ed25519KeyPair::from_seed_unchecked(&[keeper.0 as u8; 32]).unwrap()
}

fn installed() -> Installed {
    Installed {
        journal: JOURNAL,
        keepers: [1, 2, 3, 4]
            .map(|id| TrustedKeeper {
                identity: Uuid::from_u128(id),
                keys: vec![pair(KeeperId(id)).public_key().as_ref().try_into().unwrap()],
            })
            .to_vec(),
    }
}

fn open(dir: &std::path::Path, keeper: KeeperId) -> Engine {
    let mut engine = Engine::open(dir, keeper, Limits::default(), Arc::new(Allow)).unwrap();
    let authentication = Authentication {
        signer: Signer::new(keeper, JOURNAL, pair(keeper)),
        keys: Arc::new(installed()),
    };
    engine.ledger = Some(ledger::Ledger::open(dir, authentication).unwrap());
    engine
}

fn send(engine: &mut Engine, request: Request) -> Reply {
    let (work, mut result) = work(&CLIENT, request);
    engine.process(VecDeque::from([work])).unwrap();
    result.try_recv().unwrap().0.unwrap()
}

fn ask(engine: &mut Engine, request: AuthRequest) -> Result<AuthReply, Refusal> {
    let request = Request::Authenticated {
        stream: A,
        request: encode(&request).unwrap(),
    };
    match send(engine, request) {
        Reply::Authenticated(body) => Ok(decode(&body).unwrap()),
        Reply::Refused(refusal) => Err(refusal),
        other => panic!("unexpected reply {other:?}"),
    }
}

fn leaf(at: u64) -> Leaf {
    Leaf {
        stream: A,
        at: Lsn(at),
        writer_epoch: Epoch(1),
        payload_sha256: Sha256::digest(RECORDS[at as usize - 1]).into(),
        timing: None,
    }
}

fn expected(size: u64) -> Tree {
    let mut tree = Tree::default();
    tree.extend((1..=size).map(leaf)).unwrap();
    tree
}

/// A voting member of `MEMBERS` that committed all four records and trimmed two.
fn member(dir: &std::path::Path, keeper: KeeperId) -> Engine {
    let mut engine = open(dir, keeper);
    assert_eq!(send(&mut engine, create(A)), Reply::Created);
    assert!(matches!(send(&mut engine, seal(A, 1)), Reply::Sealed(_)));
    assert!(matches!(
        send(&mut engine, sync(A, 1, 1, &[], 0, true)),
        Reply::Synced { .. }
    ));
    assert_eq!(
        send(&mut engine, append(A, 1, 1, &RECORDS, 0)),
        Reply::Appended { tail: Lsn(4) }
    );
    assert_eq!(
        send(&mut engine, append(A, 1, 5, &[], 4)),
        Reply::Appended { tail: Lsn(4) }
    );
    assert_eq!(
        send(&mut engine, trim(A, 1, 2)),
        Reply::Trimmed { floor: Lsn(3) }
    );
    engine
}

fn signature(engine: &mut Engine, size: u64) -> (Head, HeadSignature) {
    match ask(engine, AuthRequest::Sign { size }) {
        Ok(AuthReply::Signed { head, signature }) => (head, signature),
        other => panic!("no signature: {other:?}"),
    }
}

#[test]
fn two_members_certify_the_committed_prefix_after_trim_and_restart() {
    let (first_dir, second_dir) = (tempdir().unwrap(), tempdir().unwrap());
    let mut first = member(first_dir.path(), MEMBERS[0]);
    let mut second = member(second_dir.path(), MEMBERS[1]);
    let tree = expected(4);
    for size in [0, 2, 4] {
        let (head, one) = signature(&mut first, size);
        let (other, two) = signature(&mut second, size);
        assert_eq!(head, other);
        assert_eq!(head.root, tree.root_at(size).unwrap());
        assert_eq!(head.ensemble, MEMBERS);
        let signed = SignedHead {
            head,
            signatures: vec![one.clone(), two],
        };
        assert_eq!(signed.verify(&installed()), Ok(()));
        let alone = SignedHead {
            head,
            signatures: vec![one],
        };
        assert!(alone.verify(&installed()).is_err());
    }
    // A keeper never signs beyond its head.
    assert_eq!(
        ask(&mut first, AuthRequest::Sign { size: 5 }),
        Err(Refusal::AboveHead { head: Lsn(4) })
    );

    // The trimmed leaves were durable before the trim: a restarted keeper still
    // signs and serves them although it no longer holds records 1 and 2.
    drop(first);
    let mut first = open(first_dir.path(), MEMBERS[0]);
    let (head, _) = signature(&mut first, 4);
    assert_eq!(head.root, tree.root());
    assert_eq!(
        ask(
            &mut first,
            AuthRequest::Leaves {
                from: Lsn(1),
                through: 4
            }
        ),
        Ok(AuthReply::Leaves(tree.leaves().to_vec()))
    );
    let Ok(AuthReply::Path { leaf: proved, path }) = ask(
        &mut first,
        AuthRequest::Path {
            at: Lsn(1),
            size: 4,
        },
    ) else {
        panic!("no inclusion path");
    };
    assert_eq!(
        (proved, path),
        (leaf(1), tree.inclusion(Lsn(1), 4).unwrap())
    );
    assert_eq!(
        ask(&mut first, AuthRequest::Status),
        Ok(AuthReply::Status {
            ingested: 4,
            floor: Lsn(3),
            complete: true
        })
    );
}

/// Keeper 3 is replaced by keeper 4, which receives only the retained records
/// 3 and 4. It cannot sign until seeded with leaves 1 and 2 and a head the two
/// survivors signed. A tampered seed is refused.
#[test]
fn a_replacement_keeper_signs_after_a_verified_seed() {
    let dirs = [tempdir().unwrap(), tempdir().unwrap(), tempdir().unwrap()];
    let mut first = member(dirs[0].path(), MEMBERS[0]);
    let mut second = member(dirs[1].path(), MEMBERS[1]);
    let replacement = KeeperId(4);
    let moved = [MEMBERS[0], MEMBERS[1], replacement];

    // The repairer installs the retained suffix on the learner at epoch 2,
    // then moves it into the new ensemble.
    let mut learner = open(dirs[2].path(), replacement);
    assert_eq!(send(&mut learner, create(A)), Reply::Created);
    assert!(matches!(send(&mut learner, seal(A, 2)), Reply::Sealed(_)));
    let installed_suffix = Request::Sync {
        stream: A,
        epoch: Epoch(2),
        floor: Lsn(3),
        from: Lsn(3),
        records: RECORDS[2..]
            .iter()
            .map(|record| Bytes::from_static(record))
            .collect(),
        runs: vec![EpochRun {
            epoch: Epoch(1),
            first: Lsn(3),
            last: Lsn(4),
        }],
        head: Lsn(4),
        complete: true,
    };
    assert!(matches!(
        send(&mut learner, installed_suffix),
        Reply::Synced { .. }
    ));
    assert_eq!(
        send(
            &mut learner,
            Request::Replace {
                stream: A,
                epoch: Epoch(2),
                from: MEMBERS,
                to: moved,
            }
        ),
        Reply::Replaced
    );

    assert_eq!(
        ask(&mut learner, AuthRequest::Sign { size: 4 }),
        Ok(AuthReply::Missing {
            ingested: 0,
            floor: Lsn(3)
        })
    );

    let (head, one) = signature(&mut first, 4);
    let (_, two) = signature(&mut second, 4);
    let signed = SignedHead {
        head,
        signatures: vec![one.clone(), two],
    };
    let Ok(AuthReply::Leaves(leaves)) = ask(
        &mut first,
        AuthRequest::Leaves {
            from: Lsn(1),
            through: 2,
        },
    ) else {
        panic!("no leaves");
    };

    // A forged leaf, or a head with only one signature, is refused.
    let mut forged = leaves.clone();
    forged[1].payload_sha256 = [9; 32];
    assert_eq!(
        ask(
            &mut learner,
            AuthRequest::Seed {
                from: Lsn(1),
                leaves: forged,
                head: Some(signed.clone()),
            }
        ),
        Err(Refusal::Conflict { head: Lsn(0) })
    );
    let under_quorum = SignedHead {
        head,
        signatures: vec![one],
    };
    assert_eq!(
        ask(
            &mut learner,
            AuthRequest::Seed {
                from: Lsn(1),
                leaves: leaves.clone(),
                head: Some(under_quorum),
            }
        ),
        Err(Refusal::Conflict { head: Lsn(0) })
    );

    // Two pages: the first stages, the second carries the head and installs.
    assert_eq!(
        ask(
            &mut learner,
            AuthRequest::Seed {
                from: Lsn(1),
                leaves: leaves[..1].to_vec(),
                head: None,
            }
        ),
        Ok(AuthReply::Seeded { ingested: 0 })
    );
    assert_eq!(
        ask(
            &mut learner,
            AuthRequest::Seed {
                from: Lsn(2),
                leaves: leaves[1..].to_vec(),
                head: Some(signed),
            }
        ),
        Ok(AuthReply::Seeded { ingested: 4 })
    );

    // The replacement now certifies the same root under the new ensemble.
    let (moved_head, three) = signature(&mut learner, 4);
    assert_eq!(moved_head.root, head.root);
    assert_eq!(moved_head.ensemble, moved);
    assert!(installed().verify_one(&moved_head.statement(), &three));
}

/// Authenticated keepers behind a transport that can take keepers down.
struct Fleet {
    keepers: HashMap<KeeperId, Keeper>,
    down: parking_lot::Mutex<Vec<KeeperId>>,
}

impl Transport for Fleet {
    fn identity(&self) -> &Identity {
        &CLIENT
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        Box::pin(async move {
            if self.down.lock().contains(&keeper) {
                return Err(TransportError::Unreachable);
            }
            self.keepers
                .get(&keeper)
                .ok_or(TransportError::Unreachable)?
                .call(&CLIENT, request)
                .await
        })
    }
}

impl Fleet {
    async fn status(&self, keeper: KeeperId) -> AuthReply {
        let request = Request::Authenticated {
            stream: A,
            request: encode(&AuthRequest::Status).unwrap(),
        };
        match self.call(keeper, request).await.unwrap() {
            Reply::Authenticated(body) => decode(&body).unwrap(),
            other => panic!("unexpected reply {other:?}"),
        }
    }

    async fn until(&self, keeper: KeeperId, done: impl Fn(&StreamView) -> bool) {
        for _ in 0..500 {
            if let Ok(Reply::Checked(view)) = self.call(keeper, check(A)).await
                && done(&view)
            {
                return;
            }
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        panic!("{keeper:?} never reached the expected view");
    }
}

/// The repairer moves a trimmed stream to a spare and seeds the spare's ledger, so
/// the spare co-signs heads with one survivor while the other survivor is down.
#[tokio::test]
async fn the_repairer_seeds_the_spares_ledger_after_moving_a_trimmed_stream() {
    use bytes::Bytes;
    use journal_contract::{Journal, JournalError};

    use crate::stream::{
        repair::{Member, Outcome, Roster, repair_lost, seed_repaired},
        writer::Writer,
    };

    let ids = [1, 2, 3, 4].map(KeeperId);
    let [first, second, lost, spare] = ids;
    let directories: Vec<_> = ids.iter().map(|_| tempdir().unwrap()).collect();
    let keepers = ids
        .iter()
        .zip(&directories)
        .map(|(&id, dir)| {
            let authentication = Authentication {
                signer: Signer::new(id, JOURNAL, pair(id)),
                keys: Arc::new(installed()),
            };
            let keeper = Keeper::open_authenticated(
                dir.path(),
                id,
                Limits::default(),
                Arc::new(Allow),
                None,
                authentication,
            )
            .unwrap();
            (id, keeper)
        })
        .collect();
    let fleet = Arc::new(Fleet {
        keepers,
        down: parking_lot::Mutex::default(),
    });
    let client = || {
        Writer::new(fleet.clone(), ids)
            .unwrap()
            .with_authentication(installed())
            .unwrap()
    };

    // Commit four records on the first three keepers and trim two on the survivors.
    let writer = client();
    writer.create(A).await.unwrap();
    for id in [first, second, lost] {
        fleet.until(id, |_| true).await;
    }
    assert_eq!(writer.seal(A, Epoch(1)).await, Ok(Lsn(0)));
    for (index, record) in RECORDS.iter().enumerate() {
        let at = Lsn(index as u64 + 1);
        assert_eq!(
            writer
                .append(A, Epoch(1), at, Bytes::from_static(record))
                .await,
            Ok(at)
        );
    }
    writer.trim(A, Epoch(1), Lsn(2)).await.unwrap();
    for id in [first, second] {
        fleet.until(id, |view| view.floor == Lsn(3)).await;
    }
    writer.require_authenticated(A).await.unwrap();

    // Zone c loses its keeper for good; the repairer moves the stream to the spare.
    fleet.down.lock().push(lost);
    let roster = Roster::new(
        ids.iter()
            .zip(["a", "b", "c", "c"])
            .map(|(&id, zone)| Member {
                id,
                zone: zone.into(),
            }),
    );
    let report = repair_lost(&*fleet, &roster, lost, &[]).await;
    let moved = match report.outcomes[..] {
        [(stream, Outcome::Repaired { ensemble, .. })] if stream == A => ensemble,
        _ => panic!("{report:?}"),
    };
    assert_eq!(moved, [first, second, spare]);
    // The spare received only the retained records, so it cannot sign yet.
    assert!(matches!(
        fleet.status(spare).await,
        AuthReply::Status {
            complete: false,
            ..
        }
    ));

    // Negative control: before the seed, one survivor and the spare cannot certify.
    let repairer = client();
    fleet.down.lock().push(first);
    assert_eq!(
        repairer.authenticated_head(A, None).await,
        Err(JournalError::Unavailable)
    );
    fleet.down.lock().retain(|&id| id != first);

    assert_eq!(seed_repaired(&repairer, &report).await, []);
    assert!(matches!(
        fleet.status(spare).await,
        AuthReply::Status {
            ingested: 4,
            complete: true,
            ..
        }
    ));

    // With one survivor down, the other survivor and the spare certify the stream.
    fleet.down.lock().push(first);
    let signed = repairer.authenticated_head(A, None).await.unwrap();
    signed.verify(&installed()).unwrap();
    assert_eq!(signed.head.size, 4);
    assert_eq!(signed.head.root, expected(4).root_at(4).unwrap());
    assert_eq!(signed.head.ensemble, moved);
    let signers: Vec<_> = signed.signatures.iter().map(|s| s.keeper).collect();
    assert_eq!(signers, [second, spare]);
}
