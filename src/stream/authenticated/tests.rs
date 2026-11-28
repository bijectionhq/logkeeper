use ring::signature::{Ed25519KeyPair, KeyPair};

use super::*;

const STREAM: StreamId = StreamId(17);
const JOURNAL: Uuid = Uuid::from_u128(11);

fn keeper(ordinal: u8) -> KeeperId {
    KeeperId(u128::from(ordinal))
}

fn pair(seed: u8) -> Ed25519KeyPair {
    Ed25519KeyPair::from_seed_unchecked(&[seed; 32]).unwrap()
}

fn public(seed: u8) -> [u8; 32] {
    pair(seed).public_key().as_ref().try_into().unwrap()
}

/// A signer for keeper `ordinal` using the key derived from `seed`.
fn signer(ordinal: u8, seed: u8) -> Signer {
    Signer::new(keeper(ordinal), JOURNAL, pair(seed))
}

/// Installed keys: `(keeper, [key seeds])`.
fn installed(entries: Vec<(u8, Vec<u8>)>) -> KeeperKeys {
    KeeperKeys {
        journal: JOURNAL,
        keepers: entries
            .into_iter()
            .map(|(ordinal, seeds)| TrustedKeeper {
                identity: Uuid::from_u128(u128::from(ordinal)),
                keys: seeds.into_iter().map(public).collect(),
            })
            .collect(),
    }
}

fn fleet() -> KeeperKeys {
    installed(vec![(1, vec![1]), (2, vec![2]), (3, vec![3]), (4, vec![4])])
}

fn leaf(at: u64) -> Leaf {
    Leaf {
        stream: STREAM,
        at: Lsn(at),
        writer_epoch: Epoch(1),
        payload_sha256: Sha256::digest(at.to_be_bytes()).into(),
        timing: None,
    }
}

fn tree(size: u64) -> Tree {
    let mut tree = Tree::default();
    tree.extend((1..=size).map(leaf)).unwrap();
    tree
}

fn head(tree: &Tree, ensemble: [u8; 3]) -> Head {
    Head {
        journal: JOURNAL,
        stream: STREAM,
        size: tree.size(),
        root: tree.root(),
        ensemble: ensemble.map(keeper),
    }
}

fn sign(head: Head, signers: &[Signer]) -> SignedHead {
    SignedHead {
        head,
        signatures: signers.iter().map(|signer| signer.sign(&head)).collect(),
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

#[test]
fn shared_tree_and_frontier_agree_on_every_prefix() {
    let tree = tree(37);
    let mut frontier = Frontier::default();
    assert_eq!(frontier.root(), merkle::empty_root());
    for size in 0..=tree.size() {
        let root = tree.root_at(size).unwrap();
        assert_eq!(root, reference_root(&tree.leaves()[..size as usize]));
        assert_eq!(frontier.size(), size);
        assert_eq!(frontier.root(), root, "frontier root at {size}");
        for at in 1..=size {
            let path = tree.inclusion(Lsn(at), size).unwrap();
            merkle::verify_inclusion(Lsn(at), leaf(at).hash(), size, root, &path).unwrap();
        }
        for prior in 0..=size {
            let path = tree.consistency(prior, size).unwrap();
            let old = tree.root_at(prior).unwrap();
            merkle::verify_consistency(prior, size, old, root, &path).unwrap();
        }
        if size < tree.size() {
            frontier.push(leaf(size + 1).hash());
        }
    }
}

#[test]
fn a_head_verifies_with_two_or_three_ensemble_signatures() {
    let keys = fleet();
    let tree = tree(5);
    let head = head(&tree, [1, 2, 3]);
    for signers in [
        vec![signer(1, 1), signer(2, 2)],
        vec![signer(3, 3), signer(1, 1)],
        vec![signer(1, 1), signer(2, 2), signer(3, 3)],
    ] {
        assert_eq!(sign(head, &signers).verify(&keys), Ok(()));
    }
    // The empty prefix is certifiable too.
    let empty = Tree::default();
    let head = Head {
        size: 0,
        root: empty.root(),
        ..head
    };
    assert_eq!(
        sign(head, &[signer(1, 1), signer(2, 2)]).verify(&keys),
        Ok(())
    );
}

#[test]
fn under_quorum_duplicate_and_outsider_signatures_are_rejected() {
    let keys = fleet();
    let tree = tree(5);
    let head = head(&tree, [1, 2, 3]);
    let refused = |signed: SignedHead| assert_eq!(signed.verify(&keys), Err(ProofError::Signature));
    // One keeper alone, even repeated, is not a quorum.
    refused(sign(head, &[signer(1, 1)]));
    refused(sign(head, &[signer(1, 1), signer(1, 1)]));
    // Keeper 4 is installed but outside the ensemble the head names.
    refused(sign(head, &[signer(1, 1), signer(4, 4)]));
    // No signatures at all.
    refused(SignedHead {
        head,
        signatures: Vec::new(),
    });
    // More signatures than ensemble members.
    let mut extra = sign(head, &[signer(1, 1), signer(2, 2), signer(3, 3)]);
    extra.signatures.push(signer(1, 1).sign(&head));
    refused(extra);
}

#[test]
fn forged_signatures_and_heads_are_rejected() {
    let keys = fleet();
    let tree = tree(5);
    let head = head(&tree, [1, 2, 3]);
    let honest = sign(head, &[signer(1, 1), signer(2, 2)]);

    // A changed root, size or ensemble invalidates the signatures.
    for forged in [
        Head {
            root: [9; 32],
            ..head
        },
        Head { size: 4, ..head },
        Head {
            ensemble: [1, 2, 4].map(keeper),
            ..head
        },
    ] {
        let signed = SignedHead {
            head: forged,
            signatures: honest.signatures.clone(),
        };
        assert!(signed.verify(&keys).is_err(), "accepted {forged:?}");
    }

    // A flipped signature bit.
    let mut flipped = honest.clone();
    flipped.signatures[1].signature[0] ^= 1;
    assert_eq!(flipped.verify(&keys), Err(ProofError::Signature));

    // A truncated signature.
    let mut short = honest.clone();
    short.signatures[1].signature.pop();
    assert_eq!(short.verify(&keys), Err(ProofError::Signature));

    // An uninstalled key claiming to be keeper 2.
    let impostor = sign(head, &[signer(1, 1), signer(2, 99)]);
    assert_eq!(impostor.verify(&keys), Err(ProofError::Signature));

    // Keeper 3's installed key relabelled as keeper 2.
    let mut relabelled = sign(head, &[signer(1, 1), signer(3, 3)]);
    relabelled.signatures[1].keeper = keeper(2);
    assert_eq!(relabelled.verify(&keys), Err(ProofError::Signature));

    // Another journal's keys, or a head naming another journal.
    let other = KeeperKeys {
        journal: Uuid::from_u128(12),
        ..keys.clone()
    };
    assert_eq!(honest.verify(&other), Err(ProofError::Head));
    let foreign = Head {
        journal: Uuid::from_u128(12),
        ..head
    };
    assert_eq!(
        sign(foreign, &[signer(1, 1), signer(2, 2)]).verify(&keys),
        Err(ProofError::Head)
    );

    // A head whose size and root disagree about emptiness is malformed.
    let malformed = Head {
        size: 0,
        root: tree.root(),
        ..head
    };
    assert_eq!(
        sign(malformed, &[signer(1, 1), signer(2, 2)]).verify(&keys),
        Err(ProofError::Head)
    );
}

#[test]
fn a_key_set_rejects_shared_zero_or_missing_keys() {
    assert!(fleet().valid());
    for invalid in [
        installed(vec![(1, vec![1]), (2, vec![1])]),
        installed(vec![(1, vec![1]), (2, vec![])]),
        installed(vec![(1, vec![1])]),
        installed(vec![(1, vec![1]), (1, vec![2])]),
        KeeperKeys {
            journal: Uuid::nil(),
            ..fleet()
        },
        KeeperKeys {
            keepers: vec![
                TrustedKeeper {
                    identity: Uuid::from_u128(1),
                    keys: vec![[0; 32]],
                },
                TrustedKeeper {
                    identity: Uuid::from_u128(2),
                    keys: vec![public(2)],
                },
            ],
            ..fleet()
        },
    ] {
        assert!(!invalid.valid(), "accepted {invalid:?}");
        let tree = tree(1);
        let signed = sign(head(&tree, [1, 2, 3]), &[signer(1, 1), signer(2, 2)]);
        assert!(signed.verify(&invalid).is_err());
    }
}

#[test]
fn archives_prove_inclusion_offline_and_survive_framing() {
    let keys = fleet();
    let timed = Leaf {
        timing: Some(Timing {
            exclusive_cutoff_micros: 30,
            receiver_certificate_sha256: [7; 32],
            quorum_sync_upper_micros: 29,
            evidence_sha256: [8; 32],
        }),
        ..leaf(2)
    };
    let mut tree = Tree::default();
    tree.extend([leaf(1), timed, leaf(3)]).unwrap();
    let signed_head = sign(head(&tree, [1, 2, 3]), &[signer(2, 2), signer(3, 3)]);
    let archive = Archive { tree, signed_head };
    archive.verify(&keys).unwrap();

    let mut framed = Vec::new();
    archive.write_to(&mut framed).unwrap();
    assert_eq!(Archive::read_from(&mut framed.as_slice()).unwrap(), archive);
    assert!(Archive::read_from(&mut &framed[..framed.len() - 1]).is_err());
    let mut trailing = framed.clone();
    trailing.push(0);
    assert!(Archive::read_from(&mut trailing.as_slice()).is_err());
    let mut consensus_magic = framed.clone();
    consensus_magic[..8].copy_from_slice(b"LKAARCH1");
    assert!(Archive::read_from(&mut consensus_magic.as_slice()).is_err());

    let mut proof = archive.inclusion(Lsn(2)).unwrap();
    assert_eq!(proof.verify(&keys), Ok(&timed));
    proof.leaf.timing = None;
    assert_eq!(proof.verify(&keys), Err(ProofError::Path));

    let mut cut = archive.clone();
    cut.tree = cut.tree.prefix(2).unwrap();
    assert_eq!(cut.verify(&keys), Err(ProofError::Head));
}

#[test]
fn a_timed_leaf_must_end_before_its_cutoff() {
    let late = Leaf {
        timing: Some(Timing {
            exclusive_cutoff_micros: 5,
            receiver_certificate_sha256: [7; 32],
            quorum_sync_upper_micros: 5,
            evidence_sha256: [8; 32],
        }),
        ..leaf(1)
    };
    assert!(!late.valid());
    assert_eq!(Tree::default().append(late), Err(ProofError::Leaf));
    // Even a quorum-signed root over the late leaf does not make it verify.
    let head = Head {
        journal: JOURNAL,
        stream: STREAM,
        size: 1,
        root: late.hash(),
        ensemble: [1, 2, 3].map(keeper),
    };
    let proof = Inclusion {
        leaf: late,
        path: Vec::new(),
        signed_head: sign(head, &[signer(1, 1), signer(2, 2)]),
    };
    assert_eq!(proof.verify(&fleet()), Err(ProofError::Leaf));
}

/// Keeper 3 is replaced by keeper 4. Heads before and after the move name
/// different ensembles, and one consistency proof spans them.
#[test]
fn proofs_stay_valid_across_a_keeper_replacement() {
    let keys = fleet();
    let full = tree(9);
    let earlier_tree = full.prefix(4).unwrap();
    let earlier = sign(
        head(&earlier_tree, [1, 2, 3]),
        &[signer(1, 1), signer(3, 3)],
    );
    let later = sign(head(&full, [1, 2, 4]), &[signer(2, 2), signer(4, 4)]);
    let proof = Consistency {
        earlier: earlier.clone(),
        later: later.clone(),
        path: full.consistency(4, 9).unwrap(),
    };
    assert_eq!(proof.verify(&keys), Ok(()));

    // An archive certified before the move still verifies after it.
    let archive = Archive {
        tree: earlier_tree.clone(),
        signed_head: earlier.clone(),
    };
    assert_eq!(archive.verify(&keys), Ok(()));
    let inclusion = Archive {
        tree: full.clone(),
        signed_head: later.clone(),
    }
    .inclusion(Lsn(3))
    .unwrap();
    assert_eq!(inclusion.verify(&keys).map(|leaf| leaf.at), Ok(Lsn(3)));

    // The replacement cannot co-sign a head for the ensemble it was not in.
    let mixed = sign(head(&full, [1, 2, 3]), &[signer(1, 1), signer(4, 4)]);
    assert_eq!(mixed.verify(&keys), Err(ProofError::Signature));

    // A history that diverges after the move fails the consistency check.
    let mut forked = full.prefix(4).unwrap();
    forked
        .extend((5..=9).map(|at| Leaf {
            payload_sha256: [3; 32],
            ..leaf(at)
        }))
        .unwrap();
    let fork = sign(head(&forked, [1, 2, 4]), &[signer(2, 2), signer(4, 4)]);
    let bad = Consistency {
        earlier,
        later: fork,
        path: full.consistency(4, 9).unwrap(),
    };
    assert_eq!(bad.verify(&keys), Err(ProofError::Path));

    // Retiring keeper 3 from the installed set invalidates heads it signed,
    // until the archive is recertified by the current ensemble.
    let retired = installed(vec![(1, vec![1]), (2, vec![2]), (4, vec![4])]);
    let mut archive = archive;
    assert_eq!(archive.verify(&retired), Err(ProofError::Signature));
    let refreshed = sign(
        head(&earlier_tree, [1, 2, 4]),
        &[signer(2, 2), signer(4, 4)],
    );
    archive.recertify(refreshed).unwrap();
    assert_eq!(archive.verify(&retired), Ok(()));
}

/// Keeper 1 rotates from key 1 to key 21. Both verify while both are installed.
/// Removing the old key rejects heads that depend on it; recertifying restores them.
#[test]
fn a_keeper_key_rotation_keeps_old_proofs_until_the_old_key_is_removed() {
    let tree = tree(6);
    let old = sign(head(&tree, [1, 2, 3]), &[signer(1, 1), signer(2, 2)]);
    let new = sign(head(&tree, [1, 2, 3]), &[signer(1, 21), signer(2, 2)]);

    let before = fleet();
    assert_eq!(old.verify(&before), Ok(()));
    assert_eq!(new.verify(&before), Err(ProofError::Signature));

    let during = installed(vec![
        (1, vec![1, 21]),
        (2, vec![2]),
        (3, vec![3]),
        (4, vec![4]),
    ]);
    assert_eq!(old.verify(&during), Ok(()));
    assert_eq!(new.verify(&during), Ok(()));
    // A head may carry both keys of the rotating keeper only once per keeper.
    let doubled = SignedHead {
        head: old.head,
        signatures: vec![signer(1, 1).sign(&old.head), signer(1, 21).sign(&old.head)],
    };
    assert_eq!(doubled.verify(&during), Err(ProofError::Signature));

    let after = installed(vec![
        (1, vec![21]),
        (2, vec![2]),
        (3, vec![3]),
        (4, vec![4]),
    ]);
    assert_eq!(old.verify(&after), Err(ProofError::Signature));
    assert_eq!(new.verify(&after), Ok(()));

    let mut archive = Archive {
        tree: tree.clone(),
        signed_head: old,
    };
    assert!(archive.verify(&after).is_err());
    // A head over another prefix cannot recertify the archive.
    let other = sign(
        head(&tree.prefix(5).unwrap(), [1, 2, 3]),
        &[signer(1, 21), signer(2, 2)],
    );
    assert_eq!(archive.recertify(other), Err(ProofError::Head));
    archive.recertify(new).unwrap();
    assert_eq!(archive.verify(&after), Ok(()));
    assert_ne!(before.digest(), after.digest());
}

#[test]
fn protocol_messages_round_trip() {
    let tree = tree(2);
    let signed = sign(head(&tree, [1, 2, 3]), &[signer(1, 1), signer(2, 2)]);
    for request in [
        protocol::AuthRequest::Status,
        protocol::AuthRequest::Sign { size: 2 },
        protocol::AuthRequest::Leaves {
            from: Lsn(1),
            through: 2,
        },
        protocol::AuthRequest::Path {
            at: Lsn(1),
            size: 2,
        },
        protocol::AuthRequest::Consistency {
            earlier: 1,
            later: 2,
        },
        protocol::AuthRequest::Seed {
            from: Lsn(1),
            leaves: tree.leaves().to_vec(),
            head: Some(signed.clone()),
        },
    ] {
        let bytes = protocol::encode(&request).unwrap();
        assert_eq!(
            protocol::decode::<protocol::AuthRequest>(&bytes).unwrap(),
            request
        );
        assert!(protocol::decode::<protocol::AuthRequest>(&bytes[..bytes.len() - 1]).is_err());
    }
    let reply = protocol::AuthReply::Signed {
        head: signed.head,
        signature: signed.signatures[0].clone(),
    };
    let bytes = protocol::encode(&reply).unwrap();
    assert_eq!(
        protocol::decode::<protocol::AuthReply>(&bytes).unwrap(),
        reply
    );
}
