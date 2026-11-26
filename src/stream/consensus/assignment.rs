//! Voter placement for streams a consumer creates and maintains.
//!
//! A stream's voters are three eligible keepers in distinct failure domains,
//! chosen by rendezvous ranking of the stream and keeper identities. Every
//! consumer with the same eligible set derives the same voters, so a retried
//! create proposes the same genesis. When eligibility changes, a stream keeps
//! every voter that is still eligible and replaces one other voter at a time.

use std::collections::BTreeSet;

use journal_contract::StreamId;
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::Domains;

/// The rendezvous score of `keeper` for `stream`. Higher ranks first.
fn score(stream: StreamId, keeper: Uuid) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.voter-rank.v1");
    hash.update(stream.0.to_be_bytes());
    hash.update(keeper.as_bytes());
    hash.finalize().into()
}

/// Eligible keepers ranked for `stream`, best first.
fn ranked(stream: StreamId, eligible: &Domains) -> Vec<Uuid> {
    let mut keepers = eligible.keys().copied().collect::<Vec<_>>();
    keepers.sort_by_key(|keeper| std::cmp::Reverse(score(stream, *keeper)));
    keepers
}

fn sorted(mut voters: [Uuid; 3]) -> [Uuid; 3] {
    voters.sort_unstable();
    voters
}

/// The best-ranked roster of three eligible keepers in distinct domains, or
/// `None` when the eligible keepers span fewer than three domains.
pub fn choose(stream: StreamId, eligible: &Domains) -> Option<[Uuid; 3]> {
    let mut chosen = Vec::with_capacity(3);
    let mut domains = BTreeSet::new();
    for keeper in ranked(stream, eligible) {
        if domains.insert(&eligible[&keeper]) {
            chosen.push(keeper);
            if chosen.len() == 3 {
                return Some(sorted([chosen[0], chosen[1], chosen[2]]));
            }
        }
    }
    None
}

/// The next roster for a stream whose voters are `current`. Returns `None`
/// when every current voter is eligible in a distinct domain, or when no
/// eligible keeper can replace an ineligible voter. Otherwise it replaces
/// exactly one voter: the first voter that is ineligible or repeats a kept
/// voter's domain, with the best-ranked eligible keeper whose domain differs
/// from the two voters it keeps.
pub fn next_roster(stream: StreamId, current: [Uuid; 3], eligible: &Domains) -> Option<[Uuid; 3]> {
    let mut kept: Vec<Uuid> = Vec::with_capacity(3);
    let mut leaving = None;
    for voter in current {
        let fits = eligible
            .get(&voter)
            .is_some_and(|domain| kept.iter().all(|other| eligible[other] != *domain));
        if fits {
            kept.push(voter);
        } else if leaving.is_none() {
            leaving = Some(voter);
        } else {
            kept.push(voter);
        }
    }
    let leaving = leaving?;
    let staying = current
        .into_iter()
        .filter(|voter| *voter != leaving)
        .collect::<Vec<_>>();
    let taken = staying
        .iter()
        .filter_map(|voter| eligible.get(voter))
        .collect::<BTreeSet<_>>();
    let replacement = ranked(stream, eligible)
        .into_iter()
        .find(|keeper| !current.contains(keeper) && !taken.contains(&eligible[keeper]))?;
    Some(sorted([staying[0], staying[1], replacement]))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn domains(entries: &[(u128, &str)]) -> Domains {
        entries
            .iter()
            .map(|(id, domain)| (Uuid::from_u128(*id), (*domain).to_owned()))
            .collect()
    }

    fn distinct(voters: [Uuid; 3], eligible: &Domains) -> bool {
        voters
            .iter()
            .map(|voter| &eligible[voter])
            .collect::<BTreeSet<_>>()
            .len()
            == 3
    }

    #[test]
    fn choose_spreads_streams_over_distinct_domains_deterministically() {
        let eligible = domains(&[
            (1, "a"),
            (2, "a"),
            (3, "b"),
            (4, "b"),
            (5, "c"),
            (6, "c"),
            (7, "d"),
        ]);
        let mut used = BTreeSet::new();
        for stream in 0..200u128 {
            let voters = choose(StreamId(stream), &eligible).unwrap();
            assert!(voters[0] < voters[1] && voters[1] < voters[2]);
            assert!(distinct(voters, &eligible));
            assert_eq!(choose(StreamId(stream), &eligible), Some(voters));
            used.extend(voters);
        }
        assert_eq!(
            used.len(),
            eligible.len(),
            "every eligible keeper carries some stream"
        );
        assert_eq!(
            choose(StreamId(1), &domains(&[(1, "a"), (2, "a"), (3, "b")])),
            None
        );
    }

    #[test]
    fn next_roster_replaces_one_ineligible_voter_and_keeps_the_rest() {
        let all = domains(&[(1, "a"), (2, "b"), (3, "c"), (4, "a"), (5, "b"), (6, "c")]);
        let stream = StreamId(42);
        let current = choose(stream, &all).unwrap();
        assert_eq!(next_roster(stream, current, &all), None);

        let mut draining = all.clone();
        draining.remove(&current[1]);
        let next = next_roster(stream, current, &draining).unwrap();
        assert!(distinct(next, &draining));
        assert!(next.contains(&current[0]) && next.contains(&current[2]));
        assert!(!next.contains(&current[1]));
        assert_eq!(next_roster(stream, next, &draining), None);

        // Two ineligible voters move one at a time.
        let mut two = all.clone();
        two.remove(&current[0]);
        two.remove(&current[2]);
        let first = next_roster(stream, current, &two).unwrap();
        assert_eq!(
            first.iter().filter(|voter| current.contains(voter)).count(),
            2
        );
        let second = next_roster(stream, first, &two).unwrap();
        assert!(distinct(second, &two));
        assert!(second.iter().all(|voter| two.contains_key(voter)));
        assert_eq!(next_roster(stream, second, &two), None);

        // Without a keeper in the missing domain the roster stays.
        let stuck = domains(&[(1, "a"), (2, "b"), (4, "a")]);
        assert_eq!(
            next_roster(
                StreamId(9),
                sorted([Uuid::from_u128(1), Uuid::from_u128(2), Uuid::from_u128(3)]),
                &stuck
            ),
            None
        );
    }
}
