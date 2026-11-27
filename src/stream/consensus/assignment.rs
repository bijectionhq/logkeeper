//! Voter placement for streams a consumer creates and maintains.
//!
//! A stream's voters are three eligible keepers in distinct failure domains,
//! chosen by rendezvous ranking of the stream and keeper identities. Every
//! consumer with the same eligible set derives the same voters, so a retried
//! create proposes the same genesis. When eligibility changes, a stream keeps
//! every voter that is still eligible and replaces one other voter at a time.

use std::collections::{BTreeMap, BTreeSet};

use journal_contract::StreamId;
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{Domains, decisions};

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

/// What a placer knows about a keeper beyond its failure domain. A keeper with
/// no entry counts as live, accepting, and carrying an average load.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Health {
    /// False once the keeper has been unreachable past the repair delay, or
    /// its replica is quarantined.
    pub live: bool,
    /// False when the keeper's disk is full or it takes no new streams.
    pub accepting: bool,
    /// Streams with an open group on the keeper.
    pub streams: u32,
}

/// Eligible keepers with their domains and whatever health is known.
pub struct View<'a> {
    pub eligible: &'a Domains,
    pub health: &'a BTreeMap<Uuid, Health>,
}

impl View<'_> {
    fn live(&self, keeper: &Uuid) -> bool {
        self.health.get(keeper).is_none_or(|health| health.live)
    }

    fn accepting(&self, keeper: &Uuid) -> bool {
        self.health
            .get(keeper)
            .is_none_or(|health| health.live && health.accepting)
    }

    /// The stream count above which an eligible keeper takes no new voter:
    /// a quarter above the eligible average, and at least one above it.
    fn ceiling(&self) -> Option<u32> {
        let known = self
            .eligible
            .keys()
            .filter_map(|keeper| self.health.get(keeper))
            .map(|health| u64::from(health.streams))
            .collect::<Vec<_>>();
        decisions::load_ceiling(known.iter().sum::<u64>(), known.len() as u64)
    }

    fn roomy(&self, keeper: &Uuid, ceiling: Option<u32>) -> bool {
        decisions::roomy(
            ceiling,
            self.health.get(keeper).map(|health| health.streams),
        )
    }

    /// Eligible keepers that accept streams, first those under the load
    /// ceiling and then, as a fallback, all of them.
    fn tiers(&self) -> [Domains; 2] {
        let ceiling = self.ceiling();
        let accepting = self
            .eligible
            .iter()
            .filter(|(keeper, _)| self.accepting(keeper))
            .map(|(keeper, domain)| (*keeper, domain.clone()))
            .collect::<Domains>();
        let roomy = accepting
            .iter()
            .filter(|(keeper, _)| self.roomy(keeper, ceiling))
            .map(|(keeper, domain)| (*keeper, domain.clone()))
            .collect();
        [roomy, accepting]
    }
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

/// Like `choose`, but skips keepers that are down, full or loaded more than
/// a quarter above the eligible average. Falls back to every accepting
/// keeper when that leaves fewer than three domains. Two placers with
/// different views may choose different rosters; the catalog's first genesis
/// claim decides.
pub fn choose_balanced(stream: StreamId, view: &View<'_>) -> Option<[Uuid; 3]> {
    view.tiers()
        .iter()
        .find_map(|candidates| choose(stream, candidates))
}

/// The next roster for a stream whose voters are `current`. Returns `None`
/// when every current voter is eligible in a distinct domain, or when no
/// eligible keeper can replace an ineligible voter. Otherwise it replaces
/// exactly one voter: the first voter that is ineligible or repeats a kept
/// voter's domain, with the best-ranked eligible keeper whose domain differs
/// from the two voters it keeps.
#[cfg(test)]
pub fn next_roster(stream: StreamId, current: [Uuid; 3], eligible: &Domains) -> Option<[Uuid; 3]> {
    repair_roster(
        stream,
        current,
        &View {
            eligible,
            health: &BTreeMap::new(),
        },
    )
}

/// `next_roster` with keeper health. A voter also leaves when its keeper is
/// down past the repair delay, quarantined, or full. The replacement must be
/// live and accepting, and under the load ceiling when one exists. Nothing
/// moves unless two current voters are live, since a membership change needs
/// a quorum and the third voter may still hold the only copy of recent
/// records.
pub fn repair_roster(stream: StreamId, current: [Uuid; 3], view: &View<'_>) -> Option<[Uuid; 3]> {
    if !decisions::repair_allowed(current.iter().filter(|voter| view.live(voter)).count()) {
        return None;
    }
    let eligible = view.eligible;
    let mut kept: Vec<Uuid> = Vec::with_capacity(3);
    let mut leaving = None;
    for voter in current {
        let fits = view.accepting(&voter)
            && eligible
                .get(&voter)
                .is_some_and(|domain| kept.iter().all(|other| eligible.get(other) != Some(domain)));
        if fits || leaving.is_some() {
            kept.push(voter);
        } else {
            leaving = Some(voter);
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
    let replacement = view.tiers().iter().find_map(|candidates| {
        ranked(stream, candidates)
            .into_iter()
            .find(|keeper| !current.contains(keeper) && !taken.contains(&candidates[keeper]))
    })?;
    Some(sorted([staying[0], staying[1], replacement]))
}

/// The roster of an operator recovery from `survivor`: the survivor and the
/// two best-ranked live, accepting keepers outside the lost configuration
/// `current`, in domains distinct from each other and from the survivor's.
/// Prefers keepers under the load ceiling. `None` when no such pair exists.
pub fn recovery_roster(
    stream: StreamId,
    survivor: Uuid,
    current: [Uuid; 3],
    view: &View<'_>,
) -> Option<[Uuid; 3]> {
    let survivor_domain = view.eligible.get(&survivor)?;
    view.tiers().iter().find_map(|candidates| {
        let mut chosen = vec![survivor];
        let mut domains = BTreeSet::from([survivor_domain]);
        for keeper in ranked(stream, candidates) {
            if current.contains(&keeper) || !view.live(&keeper) {
                continue;
            }
            if domains.insert(&candidates[&keeper]) {
                chosen.push(keeper);
                if chosen.len() == 3 {
                    return Some(sorted([chosen[0], chosen[1], chosen[2]]));
                }
            }
        }
        None
    })
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

    fn health(entries: &[(u128, bool, bool, u32)]) -> BTreeMap<Uuid, Health> {
        entries
            .iter()
            .map(|(id, live, accepting, streams)| {
                (
                    Uuid::from_u128(*id),
                    Health {
                        live: *live,
                        accepting: *accepting,
                        streams: *streams,
                    },
                )
            })
            .collect()
    }

    #[test]
    fn balanced_choice_skips_down_full_and_loaded_keepers() {
        let eligible = domains(&[(1, "a"), (2, "a"), (3, "b"), (4, "b"), (5, "c"), (6, "c")]);
        // Keeper 1 is down, 3 is full and 5 carries far more than average.
        let known = health(&[
            (1, false, true, 10),
            (2, true, true, 10),
            (3, true, false, 10),
            (4, true, true, 10),
            (5, true, true, 60),
            (6, true, true, 10),
        ]);
        let view = View {
            eligible: &eligible,
            health: &known,
        };
        for stream in 0..64u128 {
            let voters = choose_balanced(StreamId(stream), &view).unwrap();
            assert_eq!(voters, sorted([2, 4, 6].map(Uuid::from_u128)));
        }
        // When the load ceiling leaves fewer than three domains, a loaded but
        // accepting keeper still serves.
        let crowded = health(&[(1, true, true, 90), (3, true, true, 1), (5, true, true, 1)]);
        let small = domains(&[(1, "a"), (3, "b"), (5, "c")]);
        let view = View {
            eligible: &small,
            health: &crowded,
        };
        assert_eq!(
            choose_balanced(StreamId(7), &view),
            Some(sorted([1, 3, 5].map(Uuid::from_u128)))
        );
    }

    #[test]
    fn repair_replaces_a_dead_or_full_voter_only_with_two_live_voters() {
        let eligible = domains(&[(1, "a"), (2, "b"), (3, "c"), (4, "a"), (5, "b"), (6, "c")]);
        let stream = StreamId(11);
        let current = choose(stream, &eligible).unwrap();
        let no_health = BTreeMap::new();
        let view = View {
            eligible: &eligible,
            health: &no_health,
        };
        assert_eq!(repair_roster(stream, current, &view), None);

        for (live, accepting) in [(false, true), (true, false)] {
            let known = BTreeMap::from([(
                current[0],
                Health {
                    live,
                    accepting,
                    streams: 0,
                },
            )]);
            let view = View {
                eligible: &eligible,
                health: &known,
            };
            let next = repair_roster(stream, current, &view).unwrap();
            assert!(!next.contains(&current[0]));
            assert!(next.contains(&current[1]) && next.contains(&current[2]));
            assert_eq!(repair_roster(stream, next, &view), None);
        }

        // With two voters down nothing moves: the change needs a quorum.
        let two_down = BTreeMap::from([current[0], current[1]].map(|voter| {
            (
                voter,
                Health {
                    live: false,
                    accepting: true,
                    streams: 0,
                },
            )
        }));
        let view = View {
            eligible: &eligible,
            health: &two_down,
        };
        assert_eq!(repair_roster(stream, current, &view), None);
    }

    #[test]
    fn recovery_keeps_the_survivor_and_takes_two_live_keepers_in_free_domains() {
        let eligible = domains(&[
            (1, "a"),
            (2, "b"),
            (3, "c"),
            (4, "a"),
            (5, "b"),
            (6, "d"),
            (7, "e"),
        ]);
        let stream = StreamId(3);
        let current = sorted([1, 2, 3].map(Uuid::from_u128));
        let survivor = Uuid::from_u128(1);
        // The lost voters 2 and 3 do not answer; keeper 7 is down.
        let known = health(&[
            (2, false, false, 0),
            (3, false, false, 0),
            (4, true, true, 1),
            (5, true, true, 1),
            (6, true, true, 1),
            (7, false, true, 1),
        ]);
        let view = View {
            eligible: &eligible,
            health: &known,
        };
        let roster = recovery_roster(stream, survivor, current, &view).unwrap();
        assert!(roster.contains(&survivor));
        assert!(distinct(roster, &eligible));
        assert!(
            !roster.contains(&Uuid::from_u128(4)),
            "4 shares the survivor's domain"
        );
        assert!(!roster.contains(&Uuid::from_u128(7)), "7 is down");
        assert_eq!(roster, sorted([1, 5, 6].map(Uuid::from_u128)));
        // Without two free live domains there is no recovery roster.
        let few = health(&[
            (2, false, false, 0),
            (3, false, false, 0),
            (4, true, true, 1),
            (5, false, true, 1),
            (6, true, true, 1),
            (7, false, true, 1),
        ]);
        let view = View {
            eligible: &eligible,
            health: &few,
        };
        assert_eq!(recovery_roster(stream, survivor, current, &view), None);
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

        // Two leading ineligible voters must not panic the domain check.
        let mut first_two = all.clone();
        first_two.remove(&current[0]);
        first_two.remove(&current[1]);
        let moved = next_roster(stream, current, &first_two).unwrap();
        assert_eq!(
            moved.iter().filter(|voter| current.contains(voter)).count(),
            2
        );

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
