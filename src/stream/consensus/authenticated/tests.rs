use std::collections::BTreeMap;

use ring::signature::{Ed25519KeyPair, KeyPair};

use super::*;

const STREAM: StreamId = StreamId(17);
const CATALOG: Uuid = Uuid::from_u128(11);

fn leaf(at: u64) -> Leaf {
    Leaf {
        stream: STREAM,
        at: Lsn(at),
        writer_epoch: Epoch(1),
        payload_sha256: Sha256::digest(at.to_be_bytes()).into(),
        quorum_durable_upper_micros: i64::try_from(at).unwrap(),
        timing: None,
    }
}

fn reference_root(leaves: &[Leaf]) -> Hash {
    match leaves {
        [] => Sha256::digest([]).into(),
        [leaf] => leaf.hash(),
        _ => {
            let (left, right) = leaves.split_at(leaves.len().next_power_of_two() / 2);
            let mut bytes = vec![1];
            bytes.extend(reference_root(left));
            bytes.extend(reference_root(right));
            Sha256::digest(bytes).into()
        }
    }
}

fn key(seed: u8) -> Ed25519KeyPair {
    Ed25519KeyPair::from_seed_unchecked(&[seed; 32]).unwrap()
}

fn keeper(ordinal: u8) -> Uuid {
    Uuid::from_u128(u128::from(ordinal))
}

fn roster(entries: &[(u8, u8)]) -> VoterKeys {
    VoterKeys::Stable(
        entries
            .iter()
            .map(|(id, seed)| {
                (
                    keeper(*id),
                    key(*seed).public_key().as_ref().try_into().unwrap(),
                )
            })
            .collect(),
    )
}

fn signatures(entries: &[(u8, u8)], statement: &[u8]) -> Vec<QuorumSignature> {
    entries
        .iter()
        .map(|(id, seed)| QuorumSignature {
            keeper: keeper(*id),
            signature: key(*seed).sign(statement).as_ref().to_vec(),
        })
        .collect()
}

fn genesis() -> CatalogAuthority {
    let membership = roster(&[(1, 1), (2, 2), (3, 3)]);
    CatalogAuthority {
        catalog: CATALOG,
        revision: 0,
        predecessor_sha256: None,
        catalog_voters: membership.clone(),
        stream_voters: BTreeMap::from([(STREAM, membership)]),
    }
}

fn sign_head(
    size: u64,
    root: Hash,
    authority: &CatalogAuthority,
    signers: &[(u8, u8)],
) -> SignedHead {
    let head = Head {
        catalog: CATALOG,
        stream: STREAM,
        size,
        root,
        timestamp_micros: 100,
        authority_sha256: authority.digest(),
    };
    SignedHead {
        head,
        signatures: signatures(signers, &head.statement()),
    }
}

fn advance(
    history: &mut CatalogHistory,
    catalog_voters: VoterKeys,
    stream_voters: BTreeMap<StreamId, VoterKeys>,
    signers: &[(u8, u8)],
) {
    let previous = history.latest();
    let authority = CatalogAuthority {
        catalog: CATALOG,
        revision: previous.revision + 1,
        predecessor_sha256: Some(previous.digest()),
        catalog_voters,
        stream_voters,
    };
    let signatures = signatures(signers, &authority.statement());
    history.transitions.push(SignedAuthority {
        authority,
        signatures,
    });
}

#[test]
fn authenticated_tree_proves_every_prefix() {
    let mut tree = Tree::default();
    tree.extend((1..=17).map(leaf)).unwrap();
    for size in 0..=tree.size() {
        let root = tree.root_at(size).unwrap();
        assert_eq!(root, reference_root(&tree.leaves()[..size as usize]));
        for at in 1..=size {
            let path = tree.inclusion(Lsn(at), size).unwrap();
            tree::verify_inclusion(Lsn(at), leaf(at).hash(), size, root, &path).unwrap();
        }
        for prior in 0..=size {
            let path = tree.consistency(prior, size).unwrap();
            let old_root = tree.root_at(prior).unwrap();
            tree::verify_consistency(prior, size, old_root, root, &path).unwrap();
        }
    }
}

#[test]
fn authenticated_tree_rejects_invalid_batches_atomically() {
    let mut tree = Tree::default();
    tree.append(leaf(1)).unwrap();
    assert_eq!(tree.extend([leaf(2), leaf(4)]), Err(ProofError::Position));
    assert_eq!(tree.size(), 1);
    let wrong_stream = Leaf {
        stream: StreamId(7),
        ..leaf(2)
    };
    assert_eq!(tree.append(wrong_stream), Err(ProofError::Leaf));
    assert_eq!(tree.root(), leaf(1).hash());
}

#[test]
fn authenticated_archive_produces_offline_proofs() {
    let mut tree = Tree::default();
    let timed = Leaf {
        timing: Some(Timing {
            exclusive_cutoff_micros: 3,
            receiver_certificate_sha256: [7; 32],
        }),
        ..leaf(2)
    };
    tree.extend([leaf(1), timed, leaf(3)]).unwrap();
    let genesis = genesis();
    let root = genesis.root();
    let signed_head = sign_head(tree.size(), tree.root(), &genesis, &[(1, 1), (3, 3)]);
    let history = CatalogHistory {
        genesis,
        transitions: Vec::new(),
    };
    let archive = Archive {
        tree,
        signed_head,
        history,
    };
    let bytes = crate::stream::consensus::encode(&archive).unwrap();
    let mut framed = Vec::new();
    archive.write_to(&mut framed).unwrap();
    assert_eq!(Archive::read_from(&mut framed.as_slice()).unwrap(), archive);
    let mut truncated = &framed[..framed.len() - 1];
    assert!(Archive::read_from(&mut truncated).is_err());
    framed.push(0);
    assert!(Archive::read_from(&mut framed.as_slice()).is_err());

    let archive: Archive = crate::stream::consensus::decode(&bytes).unwrap();
    archive.verify(root).unwrap();
    let mut proof = archive.inclusion(timed.at).unwrap();
    assert_eq!(proof.verify(root), Ok(&timed));
    proof.path.push([1; 32]);
    assert_eq!(proof.verify(root), Err(ProofError::Path));

    let mut cut = archive.clone();
    cut.tree = cut.tree.prefix(2).unwrap();
    assert_eq!(cut.verify(root), Err(ProofError::Head));
}

#[test]
fn authenticated_inclusion_refuses_cutoff_equality_even_with_a_signed_root() {
    let late = Leaf {
        timing: Some(Timing {
            exclusive_cutoff_micros: 1,
            receiver_certificate_sha256: [7; 32],
        }),
        ..leaf(1)
    };
    assert_eq!(Tree::default().append(late), Err(ProofError::Leaf));
    let genesis = genesis();
    let root = genesis.root();
    let signed_head = sign_head(1, late.hash(), &genesis, &[(1, 1), (3, 3)]);
    let proof = Inclusion {
        leaf: late,
        path: Vec::new(),
        signed_head,
        history: CatalogHistory {
            genesis,
            transitions: Vec::new(),
        },
    };
    assert_eq!(proof.verify(root), Err(ProofError::Leaf));
}

#[test]
fn authenticated_history_verifies_replaced_and_rotated_quorums() {
    let genesis = genesis();
    let root = genesis.root();
    let mut history = CatalogHistory {
        genesis,
        transitions: Vec::new(),
    };
    let mut tree = Tree::default();
    tree.append(leaf(1)).unwrap();
    let earlier = sign_head(1, tree.root(), history.latest(), &[(1, 1), (3, 3)]);

    let replacement = roster(&[(1, 1), (3, 3), (4, 4)]);
    advance(
        &mut history,
        replacement.clone(),
        BTreeMap::from([(STREAM, replacement)]),
        &[(1, 1), (3, 3)],
    );
    let rotated = roster(&[(1, 1), (3, 3), (4, 5)]);
    advance(
        &mut history,
        rotated.clone(),
        BTreeMap::from([(STREAM, rotated)]),
        &[(3, 3), (4, 4)],
    );
    let unchanged = history.latest().catalog_voters.clone();
    advance(&mut history, unchanged, BTreeMap::new(), &[(3, 3), (4, 5)]);

    tree.append(leaf(2)).unwrap();
    let later = sign_head(2, tree.root(), history.latest(), &[(3, 3), (4, 5)]);
    let mut proof = Consistency {
        earlier,
        later,
        path: tree.consistency(1, 2).unwrap(),
        history,
    };
    proof.verify(root).unwrap();
    assert_eq!(
        proof.verify(CatalogRoot([1; 32])),
        Err(ProofError::CatalogHistory)
    );
    proof.later.signatures = signatures(&[(3, 3), (4, 4)], &proof.later.head.statement());
    assert_eq!(proof.verify(root), Err(ProofError::Signature));
    proof.history.transitions.remove(0);
    assert_eq!(proof.verify(root), Err(ProofError::CatalogHistory));
}

#[test]
fn authenticated_joint_roster_requires_both_distinct_majorities() {
    let VoterKeys::Stable(previous) = roster(&[(1, 1), (2, 2), (3, 3)]) else {
        unreachable!()
    };
    let VoterKeys::Stable(next) = roster(&[(2, 2), (3, 3), (4, 4)]) else {
        unreachable!()
    };
    let joint = VoterKeys::Joint { previous, next };
    let statement = b"committed head";
    assert_eq!(
        joint.verify(statement, &signatures(&[(2, 2), (3, 3)], statement)),
        Ok(())
    );
    for signers in [&[(1, 1), (2, 2)][..], &[(2, 2), (2, 2)], &[(3, 3), (4, 4)]] {
        assert_eq!(
            joint.verify(statement, &signatures(signers, statement)),
            Err(ProofError::Signature)
        );
    }
}

#[test]
fn authenticated_replaced_roster_cannot_certify_a_head() {
    let genesis = genesis();
    let root = genesis.root();
    let mut history = CatalogHistory {
        genesis,
        transitions: Vec::new(),
    };
    let mut tree = Tree::default();
    tree.append(leaf(1)).unwrap();
    let retired = history.latest().clone();
    let rotated = roster(&[(1, 1), (2, 2), (3, 6)]);
    advance(
        &mut history,
        rotated.clone(),
        BTreeMap::from([(STREAM, rotated)]),
        &[(1, 1), (2, 2)],
    );

    let mut forged = Tree::default();
    forged.append(Leaf { writer_epoch: Epoch(9), ..leaf(1) }).unwrap();
    let equivocation = sign_head(1, forged.root(), &retired, &[(1, 1), (3, 3)]);
    assert_eq!(
        equivocation.verify(root, &history),
        Err(ProofError::CatalogHistory)
    );
    sign_head(1, tree.root(), history.latest(), &[(1, 1), (3, 6)])
        .verify(root, &history)
        .unwrap();

    let unchanged = history.latest().catalog_voters.clone();
    advance(&mut history, unchanged, BTreeMap::new(), &[(2, 2), (3, 6)]);
    sign_head(1, tree.root(), &history.transitions[0].authority, &[(1, 1), (2, 2)])
        .verify(root, &history)
        .unwrap();
}

#[test]
fn authenticated_abandoned_catalog_move_is_settled_by_the_side_it_keeps() {
    let genesis = genesis();
    let root = genesis.root();
    let mut history = CatalogHistory {
        genesis,
        transitions: Vec::new(),
    };
    let original = roster(&[(1, 1), (2, 2), (3, 3)]);
    let abandoned = original.joining(&roster(&[(4, 4), (5, 5), (6, 6)]));
    advance(&mut history, abandoned, BTreeMap::new(), &[(1, 1), (2, 2)]);
    let retargeted = original.joining(&roster(&[(7, 7), (8, 8), (9, 9)]));
    advance(&mut history, retargeted.clone(), BTreeMap::new(), &[(1, 1), (3, 3)]);
    history.verify(root).unwrap();

    let mut stranded = history.clone();
    advance(
        &mut stranded,
        roster(&[(4, 4), (5, 5), (6, 6)]),
        BTreeMap::new(),
        &[(4, 4), (5, 5)],
    );
    assert_eq!(stranded.verify(root), Err(ProofError::CatalogHistory));

    let target = retargeted
        .settles_to(&[keeper(7), keeper(8), keeper(9)])
        .unwrap();
    advance(&mut history, target, BTreeMap::new(), &[(8, 8), (9, 9)]);
    history.verify(root).unwrap();
}
