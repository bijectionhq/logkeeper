//! The example configurations under `deploy/consensus` parse as the keeper
//! and the journal client read them, and agree with each other.
#![cfg(feature = "stream")]

use std::path::{Path, PathBuf};

use logkeeper::stream::consensus::{Config, JournalConfig};
use serde_json::Value;

fn deploy(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("deploy/consensus")
        .join(path)
}

fn json(path: &str) -> Value {
    serde_json::from_slice(&std::fs::read(deploy(path)).unwrap()).unwrap()
}

/// Checks what `Config::validate` checks without the enrollment registry:
/// inventories, distinct addresses, the catalog and its voters.
fn check_keeper(config: &Config) {
    assert!(config.keepers.len() >= 3);
    assert!(config.keepers.contains_key(&config.keeper));
    assert!(config.keepers.contains_key(&config.catalog));
    assert!(config.keepers.keys().eq(config.peers.keys()));
    assert!(config.keepers.keys().eq(config.bulk.keys()));
    assert!(config.keepers.keys().eq(config.domains.keys()));
    let addresses = config
        .keepers
        .values()
        .chain(config.peers.values())
        .chain(config.bulk.values())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(addresses.len(), config.keepers.len() * 3);
    assert_eq!(config.listen, config.keepers[&config.keeper]);
    let voters = config
        .catalog_voters
        .expect("production runs a replicated catalog");
    assert!(voters.is_sorted() && voters.contains(&config.catalog));
    let domains = voters
        .iter()
        .map(|voter| &config.domains[voter])
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(domains.len(), 3);
    for uri in config
        .readers
        .iter()
        .chain(&config.writers)
        .chain(&config.administrators)
    {
        assert!(uri.starts_with("urn:logkeeper:client:"), "{uri}");
    }
    assert!(!config.data.starts_with(&config.enrollment));
    assert!(!config.enrollment.starts_with(&config.data));
}

fn check_authority(config: &Config, placement: &Value, provision: &Value) {
    assert_eq!(placement["catalog"], config.catalog.to_string());
    assert_eq!(
        placement["domains"],
        serde_json::to_value(&config.domains).unwrap()
    );
    assert_eq!(provision["keeper"], config.keeper.to_string());
    assert_eq!(provision["data"], config.data.to_str().unwrap());
    assert_eq!(provision["domain"], config.domains[&config.keeper]);
    assert_eq!(provision["certificate_sha256"].as_str().unwrap().len(), 64);
}

#[test]
fn keeper_example_parses_and_matches_its_authority() {
    let config = Config::read(&deploy("keeper.example.json")).unwrap();
    check_keeper(&config);
    check_authority(
        &config,
        &json("placement.example.json"),
        &json("provision.example.json"),
    );
}

#[test]
fn kubernetes_keepers_share_one_inventory() {
    let placement = json("kubernetes/keepers/placement.json");
    let configs = (0..3)
        .map(|n| {
            let config =
                Config::read(&deploy(&format!("kubernetes/keepers/keeper-{n}.json"))).unwrap();
            check_keeper(&config);
            check_authority(
                &config,
                &placement,
                &json(&format!("kubernetes/keepers/keeper-{n}.provision.json")),
            );
            let id = std::fs::read_to_string(deploy(&format!("kubernetes/keepers/keeper-{n}.id")))
                .unwrap();
            assert_eq!(id.trim(), config.keeper.to_string());
            config
        })
        .collect::<Vec<_>>();
    for config in &configs[1..] {
        assert_eq!(config.keepers, configs[0].keepers);
        assert_eq!(config.peers, configs[0].peers);
        assert_eq!(config.bulk, configs[0].bulk);
        assert_eq!(config.domains, configs[0].domains);
        assert_eq!(config.catalog, configs[0].catalog);
        assert_eq!(config.catalog_voters, configs[0].catalog_voters);
        assert_eq!(config.writers, configs[0].writers);
        assert_eq!(config.administrators, configs[0].administrators);
    }
    let ids = configs
        .iter()
        .map(|config| config.keeper)
        .collect::<Vec<_>>();
    assert_eq!(ids.len(), 3);
    assert!(ids.iter().all(|id| configs[0].keepers.contains_key(id)));
}

#[test]
fn rtdb_journal_example_matches_the_keepers() {
    let journal = JournalConfig::read(&deploy("rtdb-journal.example.json")).unwrap();
    let keeper = Config::read(&deploy("keeper.example.json")).unwrap();
    assert_eq!(journal.keepers, keeper.keepers);
    assert_eq!(journal.catalog, keeper.catalog);
    assert_eq!(journal.catalog_voters, keeper.catalog_voters);
    assert_eq!(journal.placement.as_ref(), Some(&keeper.domains));
    assert!(journal.voters.is_none());
    let domain = journal.domain.as_ref().unwrap();
    assert!(keeper.domains.values().any(|known| known == domain));
    // RTDB both creates and moves streams (administrator) and writes them.
    for role in [&keeper.writers, &keeper.administrators] {
        assert!(role.iter().any(|uri| uri == "urn:logkeeper:client:rtdb"));
    }
}
