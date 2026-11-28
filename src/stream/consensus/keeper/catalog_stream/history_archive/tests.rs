use std::collections::BTreeMap;

use ring::signature::{Ed25519KeyPair, KeyPair};

use super::*;
use crate::stream::consensus::authenticated::{QuorumSignature, VoterKeys};

#[test]
fn authenticated_catalog_archive_keeps_incremental_history_across_compaction() {
    let signing_keys: Vec<_> = (1u8..=3)
        .map(|id| {
            let key = Ed25519KeyPair::from_seed_unchecked(&[id; 32]).unwrap();
            (Uuid::from_u128(u128::from(id)), key)
        })
        .collect();
    let catalog = Uuid::from_u128(4);
    let catalog_voters = VoterKeys::Stable(
        signing_keys
            .iter()
            .map(|(id, key)| (*id, key.public_key().as_ref().try_into().unwrap()))
            .collect(),
    );
    let genesis = CatalogAuthority {
        catalog,
        revision: 0,
        predecessor_sha256: None,
        catalog_voters,
        stream_voters: BTreeMap::new(),
    };
    let mut history = CatalogHistory {
        genesis: genesis.clone(),
        transitions: Vec::new(),
    };
    let append = |history: &mut CatalogHistory| {
        let previous = history.latest();
        let authority = CatalogAuthority {
            revision: previous.revision + 1,
            predecessor_sha256: Some(previous.digest()),
            ..genesis.clone()
        };
        let statement = authority.statement();
        let signatures = signing_keys[..2]
            .iter()
            .map(|(keeper, key)| QuorumSignature {
                keeper: *keeper,
                signature: key.sign(&statement).as_ref().to_vec(),
            })
            .collect();
        history.transitions.push(SignedAuthority {
            authority,
            signatures,
        });
    };

    let directory = tempfile::tempdir().unwrap();
    let mount = directory.path();
    append(&mut history);
    let earlier = Reference::save(mount, &history, None).unwrap();
    let earlier_history = history.clone();
    append(&mut history);
    append(&mut history);
    let later = Reference::save(mount, &history, Some(earlier)).unwrap();

    let pages = super::directory(mount, catalog);
    assert_eq!(fs::read_dir(&pages).unwrap().count(), 2);
    let added: Page = decode(&read_page(&pages, later.tail.unwrap()).unwrap()).unwrap();
    assert_eq!(added.previous, earlier.tail);
    assert_eq!(added.transitions, history.transitions[1..]);
    assert_eq!(later.load(mount, genesis.clone()).unwrap(), history);
    assert_eq!(
        Reference::save(mount, &history, Some(later)).unwrap(),
        later
    );

    fs::write(page_path(&pages, later.tail.unwrap()), b"damaged page").unwrap();
    assert_eq!(
        later.load(mount, genesis.clone()).unwrap_err().kind(),
        io::ErrorKind::InvalidData,
    );
    assert_eq!(earlier.load(mount, genesis).unwrap(), earlier_history);
}
