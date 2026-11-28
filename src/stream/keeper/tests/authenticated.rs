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
