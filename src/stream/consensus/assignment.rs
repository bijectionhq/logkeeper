//! Voter placement for streams a consumer creates and maintains.
//!
//! A stream's voters are three eligible keepers in distinct failure domains,
//! chosen by rendezvous ranking of the stream and keeper identities. Every
//! consumer with the same eligible set derives the same voters, so a retried
//! create proposes the same genesis. When eligibility changes, a stream keeps
//! every voter that is still eligible and replaces one other voter at a time.

use std::collections::BTreeMap;

use journal_contract::StreamId;
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{Domains, decisions};
use crate::stream::consensus::Voters;

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

/// Completes `fixed` to `factor` voters from `ranked`, best first, skipping
/// keepers `skip` rejects. Each pass admits one more voter per failure
/// domain, so a roster takes free domains first and shares a domain only
/// when it must, never past what `decisions::spread_allows` lets one domain
/// hold: one of three, two of five. `None` when no such roster exists.
fn complete(
    fixed: &[Uuid],
    ranked: &[Uuid],
    domains: &Domains,
    factor: usize,
    skip: impl Fn(&Uuid) -> bool,
) -> Option<Voters> {
    if !decisions::replication_factor(factor) {
        return None;
    }
    let mut chosen = fixed.to_vec();
    let mut counts = BTreeMap::<&String, usize>::new();
    // A kept voter that is no longer eligible holds no domain; repair moves
    // it on a later step.
    for domain in fixed.iter().filter_map(|voter| domains.get(voter)) {
        *counts.entry(domain).or_default() += 1;
    }
    let most = factor - decisions::quorum(factor);
    for allowed in 1..=most {
        for keeper in ranked {
            if chosen.len() == factor {
                break;
            }
            if chosen.contains(keeper) || skip(keeper) {
                continue;
            }
            let Some(domain) = domains.get(keeper) else {
                continue;
            };
            let count = counts.entry(domain).or_default();
            if *count < allowed {
                *count += 1;
                chosen.push(*keeper);
            }
        }
    }
    let spread = counts.into_values().fold(0, decisions::largest_domain);
    (chosen.len() == factor && decisions::spread_allows(factor, spread))
        .then(|| Voters::sorted(&chosen))
        .flatten()
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

/// The best-ranked roster of `factor` eligible keepers, three or five,
/// in distinct failure domains when there are enough, and otherwise spread
/// so that no domain holds more than `decisions::spread_allows` lets it
/// (five voters over three domains as 2+2+1). `None` when the eligible
/// keepers cannot be spread that way.
pub fn choose(stream: StreamId, eligible: &Domains, factor: usize) -> Option<Voters> {
    complete(&[], &ranked(stream, eligible), eligible, factor, |_| false)
}

/// Like `choose`, but skips keepers that are down, full or loaded more than
/// a quarter above the eligible average. Falls back to every accepting
/// keeper when that leaves too few domains. Two placers with different
/// views may choose different rosters; the catalog's first genesis claim
/// decides.
pub fn choose_balanced(stream: StreamId, view: &View<'_>, factor: usize) -> Option<Voters> {
    view.tiers()
        .iter()
        .find_map(|candidates| choose(stream, candidates, factor))
}

/// The next roster for a stream whose voters are `current`. Returns `None`
/// when every current voter is eligible and spread, or when no eligible
/// keeper can replace an ineligible voter. Otherwise it replaces exactly
/// one voter: the first voter that is ineligible or crowds a domain the
/// voters before it fill, with the best-ranked eligible keeper in the
/// emptiest domain the kept voters leave room in.
#[cfg(test)]
pub fn next_roster(stream: StreamId, current: Voters, eligible: &Domains) -> Option<Voters> {
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
/// moves unless a quorum of the current voters is live (two of three, three
/// of five), since a membership change needs a quorum and the silent
/// voters may hold the only copies of recent records.
pub fn repair_roster(stream: StreamId, current: Voters, view: &View<'_>) -> Option<Voters> {
    let live = current.iter().filter(|voter| view.live(voter)).count();
    if !decisions::repair_allowed(live, current.len()) {
        return None;
    }
    let eligible = view.eligible;
    let most = current.tolerated();
    let mut kept: Vec<Uuid> = Vec::with_capacity(current.len());
    let mut leaving = None;
    for voter in current {
        let fits = view.accepting(&voter)
            && eligible.get(&voter).is_some_and(|domain| {
                kept.iter()
                    .filter(|other| eligible.get(other) == Some(domain))
                    .count()
                    < most
            });
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
    view.tiers().iter().find_map(|candidates| {
        let mut domains = candidates.clone();
        for voter in &staying {
            if let Some(domain) = eligible.get(voter) {
                domains.insert(*voter, domain.clone());
            }
        }
        complete(
            &staying,
            &ranked(stream, candidates),
            &domains,
            current.len(),
            |keeper| current.contains(keeper),
        )
    })
}

/// The roster of an operator recovery from `survivors`, the voters of the
/// lost configuration `current` that keep their copies: one of three, one
/// or two of five. The survivors keep their seats, and the best-ranked
/// live, accepting keepers outside `current` fill the rest, in free
/// failure domains first and never crowding a domain past what
/// `decisions::spread_allows` lets it hold. Prefers keepers under the load
/// ceiling. `None` when no such roster exists.
pub fn recovery_roster(
    stream: StreamId,
    survivors: &[Uuid],
    current: Voters,
    view: &View<'_>,
) -> Option<Voters> {
    if survivors
        .iter()
        .any(|survivor| !view.eligible.contains_key(survivor))
    {
        return None;
    }
    view.tiers().iter().find_map(|candidates| {
        let mut domains = candidates.clone();
        for survivor in survivors {
            domains.insert(*survivor, view.eligible[survivor].clone());
        }
        complete(
            survivors,
            &ranked(stream, candidates),
            &domains,
            current.len(),
            |keeper| current.contains(keeper) || !view.live(keeper),
        )
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    fn sorted<const N: usize>(voters: [Uuid; N]) -> Voters {
        Voters::sorted(&voters).unwrap()
    }

    fn domains(entries: &[(u128, &str)]) -> Domains {
        entries
            .iter()
            .map(|(id, domain)| (Uuid::from_u128(*id), (*domain).to_owned()))
            .collect()
    }

    fn distinct(voters: Voters, eligible: &Domains) -> bool {
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
            let voters = choose(StreamId(stream), &eligible, 3).unwrap();
            assert!(voters[0] < voters[1] && voters[1] < voters[2]);
            assert!(distinct(voters, &eligible));
            assert_eq!(choose(StreamId(stream), &eligible, 3), Some(voters));
            used.extend(voters);
        }
        assert_eq!(
            used.len(),
            eligible.len(),
            "every eligible keeper carries some stream"
        );
        assert_eq!(
            choose(StreamId(1), &domains(&[(1, "a"), (2, "a"), (3, "b")]), 3),
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
            let voters = choose_balanced(StreamId(stream), &view, 3).unwrap();
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
            choose_balanced(StreamId(7), &view, 3),
            Some(sorted([1, 3, 5].map(Uuid::from_u128)))
        );
    }

    #[test]
    fn repair_replaces_a_dead_or_full_voter_only_with_two_live_voters() {
        let eligible = domains(&[(1, "a"), (2, "b"), (3, "c"), (4, "a"), (5, "b"), (6, "c")]);
        let stream = StreamId(11);
        let current = choose(stream, &eligible, 3).unwrap();
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
        let roster = recovery_roster(stream, &[survivor], current, &view).unwrap();
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
        assert_eq!(recovery_roster(stream, &[survivor], current, &view), None);
    }

    #[test]
    fn next_roster_replaces_one_ineligible_voter_and_keeps_the_rest() {
        let all = domains(&[(1, "a"), (2, "b"), (3, "c"), (4, "a"), (5, "b"), (6, "c")]);
        let stream = StreamId(42);
        let current = choose(stream, &all, 3).unwrap();
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

    fn spread(voters: Voters, eligible: &Domains) -> Vec<usize> {
        let mut counts = BTreeMap::<&String, usize>::new();
        for voter in &voters {
            *counts.entry(&eligible[voter]).or_default() += 1;
        }
        let mut counts = counts.into_values().collect::<Vec<_>>();
        counts.sort_unstable_by(|a, b| b.cmp(a));
        counts
    }

    #[test]
    fn five_voters_take_distinct_domains_when_there_are_five() {
        let eligible = domains(&[
            (1, "a"),
            (2, "a"),
            (3, "b"),
            (4, "c"),
            (5, "d"),
            (6, "e"),
            (7, "e"),
        ]);
        for stream in 0..100u128 {
            let voters = choose(StreamId(stream), &eligible, 5).unwrap();
            assert!(voters.ascending());
            assert_eq!(spread(voters, &eligible), [1, 1, 1, 1, 1]);
            assert_eq!(choose(StreamId(stream), &eligible, 5), Some(voters));
        }
    }

    #[test]
    fn five_voters_over_fewer_domains_never_give_one_a_quorum() {
        // Three domains: 2+2+1.
        let three = domains(&[(1, "a"), (2, "a"), (3, "b"), (4, "b"), (5, "c"), (6, "c")]);
        for stream in 0..100u128 {
            let voters = choose(StreamId(stream), &three, 5).unwrap();
            assert_eq!(spread(voters, &three), [2, 2, 1]);
        }
        // Four domains: 2+1+1+1.
        let four = domains(&[(1, "a"), (2, "a"), (3, "b"), (4, "b"), (5, "c"), (6, "d")]);
        for stream in 0..100u128 {
            let voters = choose(StreamId(stream), &four, 5).unwrap();
            assert_eq!(spread(voters, &four), [2, 1, 1, 1]);
        }
        // Two domains cannot hold five voters without one holding three.
        let two = domains(&[(1, "a"), (2, "a"), (3, "a"), (4, "b"), (5, "b"), (6, "b")]);
        assert_eq!(choose(StreamId(1), &two, 5), None);
        // Nor can three domains when one has a single keeper and another
        // two: 2+2 fill and the third adds one, but here c is missing.
        let short = domains(&[(1, "a"), (2, "a"), (3, "b"), (4, "c")]);
        assert_eq!(choose(StreamId(1), &short, 5), None);
        assert!(choose(StreamId(1), &short, 3).is_some());
        // Neither 4 nor 6 is a replication factor.
        assert_eq!(choose(StreamId(1), &three, 4), None);
    }

    #[test]
    fn five_voters_repair_two_lost_voters_one_at_a_time_and_three_never() {
        let eligible = domains(&[
            (1, "a"),
            (2, "b"),
            (3, "c"),
            (4, "d"),
            (5, "e"),
            (6, "f"),
            (7, "g"),
            (8, "a"),
        ]);
        let stream = StreamId(5);
        let current = choose(stream, &eligible, 5).unwrap();
        let down = |count: usize| {
            current[..count]
                .iter()
                .map(|voter| {
                    (
                        *voter,
                        Health {
                            live: false,
                            accepting: true,
                            streams: 0,
                        },
                    )
                })
                .collect::<BTreeMap<_, _>>()
        };
        let two = down(2);
        let view = View {
            eligible: &eligible,
            health: &two,
        };
        let first = repair_roster(stream, current, &view).unwrap();
        assert_eq!(first.len(), 5);
        assert_eq!(first.iter().filter(|id| current.contains(id)).count(), 4);
        let second = repair_roster(stream, first, &view).unwrap();
        assert!(!second.contains(&current[0]) && !second.contains(&current[1]));
        assert_eq!(spread(second, &eligible), [1, 1, 1, 1, 1]);
        assert_eq!(repair_roster(stream, second, &view), None);

        // With three of five down nothing moves: the change needs a quorum.
        let three = down(3);
        let view = View {
            eligible: &eligible,
            health: &three,
        };
        assert_eq!(repair_roster(stream, current, &view), None);
    }

    #[test]
    fn a_five_voter_repair_prefers_a_free_domain_and_shares_one_only_when_it_must() {
        // Voters in a, a, b, b, c; keeper 1 in a dies. The replacement goes
        // to the free domain d rather than a second keeper of a.
        let eligible = domains(&[
            (1, "a"),
            (2, "a"),
            (3, "b"),
            (4, "b"),
            (5, "c"),
            (6, "a"),
            (7, "d"),
        ]);
        let current = sorted([1, 2, 3, 4, 5].map(Uuid::from_u128));
        let dead = health(&[(1, false, true, 0)]);
        let view = View {
            eligible: &eligible,
            health: &dead,
        };
        let next = repair_roster(StreamId(9), current, &view).unwrap();
        assert_eq!(next, sorted([2, 3, 4, 5, 7].map(Uuid::from_u128)));
        // Without d, the replacement shares a: still 2+2+1.
        let mut no_free = eligible.clone();
        no_free.remove(&Uuid::from_u128(7));
        let view = View {
            eligible: &no_free,
            health: &dead,
        };
        let next = repair_roster(StreamId(9), current, &view).unwrap();
        assert_eq!(next, sorted([2, 3, 4, 5, 6].map(Uuid::from_u128)));
    }

    #[test]
    fn a_five_voter_recovery_keeps_both_survivors_and_fills_three_seats() {
        let eligible = domains(&[
            (1, "a"),
            (2, "b"),
            (3, "c"),
            (4, "d"),
            (5, "e"),
            (6, "f"),
            (7, "g"),
            (8, "h"),
            (9, "a"),
        ]);
        let current = sorted([1, 2, 3, 4, 5].map(Uuid::from_u128));
        let lost = health(&[
            (3, false, false, 0),
            (4, false, false, 0),
            (5, false, false, 0),
        ]);
        let view = View {
            eligible: &eligible,
            health: &lost,
        };
        let survivors = [1, 2].map(Uuid::from_u128);
        let roster = recovery_roster(StreamId(3), &survivors, current, &view).unwrap();
        assert_eq!(roster, sorted([1, 2, 6, 7, 8].map(Uuid::from_u128)));
        // One survivor of five takes four replacements.
        let roster = recovery_roster(StreamId(3), &survivors[..1], current, &view).unwrap();
        assert_eq!(roster.len(), 5);
        assert!(roster.contains(&survivors[0]));
        assert_eq!(roster.iter().filter(|id| current.contains(id)).count(), 1);
    }
}
