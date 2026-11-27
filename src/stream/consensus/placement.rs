use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::Arc,
};

use openraft::BasicNode;
use uuid::Uuid;

use super::{Genesis, Keepers, NodeId, Stage, Voters, decisions, invalid};

/// Operator-certified failure domains, keyed by keeper incarnation.
pub type Domains = BTreeMap<Uuid, String>;

#[derive(Clone)]
pub(super) struct Placement {
    /// Active (non-retired) keepers eligible for new geneses and stage targets.
    eligible: Arc<Domains>,
    /// All keepers with addresses in the inventory (active plus draining
    /// retired keepers), used for liveness pings and peer routing.
    all_domains: Arc<Domains>,
    /// All known keeper identities (active or retired) that may legally appear
    /// in historical genesis, membership, or stage records.
    known: Arc<BTreeSet<Uuid>>,
    /// Explicitly retired keeper identities.
    retired: Arc<BTreeSet<Uuid>>,
}

impl Placement {
    pub fn new(keepers: &Keepers, domains: Domains, retired: BTreeSet<Uuid>) -> io::Result<Self> {
        if !keepers.keys().eq(domains.keys())
            || retired.iter().any(Uuid::is_nil)
            || domains
                .values()
                .any(|domain| domain.trim() != domain || domain.is_empty() || domain.len() > 256)
        {
            return Err(invalid("every keeper needs a declared failure domain"));
        }
        let known = keepers
            .keys()
            .copied()
            .chain(retired.iter().copied())
            .collect::<BTreeSet<_>>();
        let eligible = domains
            .iter()
            .filter(|(id, _)| !retired.contains(id))
            .map(|(id, domain)| (*id, domain.clone()))
            .collect::<Domains>();
        Ok(Self {
            eligible: Arc::new(eligible),
            all_domains: Arc::new(domains),
            known: Arc::new(known),
            retired: Arc::new(retired),
        })
    }

    /// Eligible (non-retired) keepers and their failure domains.
    pub fn domains(&self) -> &Domains {
        &self.eligible
    }

    /// All keepers present in the configured inventory (including draining
    /// retired keepers).
    pub fn all_domains(&self) -> &Domains {
        &self.all_domains
    }

    pub fn is_retired(&self, keeper: Uuid) -> bool {
        self.retired.contains(&keeper)
    }

    pub fn known(&self, keeper: Uuid) -> bool {
        self.known.contains(&keeper)
    }

    /// Strict placement check for new geneses: every voter must be active
    /// (non-retired) and in a distinct failure domain.
    pub fn genesis(&self, genesis: &Genesis) -> bool {
        genesis.stream.0 != 0 && genesis.quota_bytes > 0 && self.roster(&genesis.voters)
    }

    /// Structural check for existing/historical geneses: three sorted known
    /// keepers (active or retired), without quarantining on domain changes.
    pub fn structural_genesis(&self, genesis: &Genesis) -> bool {
        genesis.stream.0 != 0 && genesis.quota_bytes > 0 && self.structural_roster(&genesis.voters)
    }

    /// Strict placement check: three or five sorted active (non-retired)
    /// keepers spread so that losing any one failure domain leaves a
    /// quorum (`decisions::spread_allows`). Three voters take three
    /// distinct domains; five take at least three, at most two per domain.
    pub fn roster(&self, voters: &Voters) -> bool {
        if !voters.ascending() {
            return false;
        }
        let mut counts = BTreeMap::<&String, usize>::new();
        for voter in voters {
            match self.eligible.get(voter) {
                Some(domain) => *counts.entry(domain).or_default() += 1,
                None => return false,
            }
        }
        decisions::spread_allows(voters.len(), counts.into_values().max().unwrap_or(0))
    }

    /// Structural check: three or five sorted known keepers (active or
    /// retired).
    pub fn structural_roster(&self, voters: &Voters) -> bool {
        voters.ascending() && voters.iter().all(|voter| self.known(*voter))
    }

    /// Strict check for a new stage: the old roster only needs to be
    /// structurally valid (so a placement-violating or retired-voter stream can
    /// move), while the target roster must satisfy current strict placement.
    pub fn stage(&self, stage: &Stage) -> bool {
        stage.old != stage.target
            && stage.old.len() == stage.target.len()
            && self.structural_roster(&stage.old)
            && self.roster(&stage.target)
    }

    /// Structural check for historical/replayed stage records.
    pub fn structural_stage(&self, stage: &Stage) -> bool {
        stage.old != stage.target
            && stage.old.len() == stage.target.len()
            && self.structural_roster(&stage.old)
            && self.structural_roster(&stage.target)
    }

    #[cfg(test)]
    pub fn membership(&self, membership: &openraft::Membership<NodeId, BasicNode>) -> bool {
        let configs = membership.get_joint_config();
        (1..=2).contains(&configs.len())
            && membership
                .nodes()
                .all(|(id, _)| self.eligible.contains_key(&Uuid::from_u128(*id)))
            && configs.iter().all(|voters| {
                roster_of(voters)
                    .is_some_and(|voters| voters.len() == configs[0].len() && self.roster(&voters))
            })
    }

    /// Structural check for existing, replayed, or in-flight Raft memberships.
    /// Does not reject streams whose voters now share a domain or include a
    /// retired keeper; repair moves them to a compliant roster instead.
    pub fn structural_membership(
        &self,
        membership: &openraft::Membership<NodeId, BasicNode>,
    ) -> bool {
        let configs = membership.get_joint_config();
        (1..=2).contains(&configs.len())
            && membership
                .nodes()
                .all(|(id, _)| self.known(Uuid::from_u128(*id)))
            && configs.iter().all(|voters| {
                roster_of(voters).is_some_and(|voters| {
                    voters.len() == configs[0].len() && self.structural_roster(&voters)
                })
            })
    }
}

/// The roster of one side of a Raft membership, in ascending order, or
/// `None` unless it holds three or five voters.
fn roster_of(voters: &BTreeSet<NodeId>) -> Option<Voters> {
    Voters::new(
        &voters
            .iter()
            .map(|id| Uuid::from_u128(*id))
            .collect::<Vec<_>>(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loss_of_any_declared_domain_leaves_both_joint_majorities() {
        let ids = [1, 2, 3, 4, 5].map(Uuid::from_u128);
        let keepers = ids
            .into_iter()
            .enumerate()
            .map(|(i, id)| {
                (
                    id,
                    std::net::SocketAddr::from(([127, 0, 0, 1], 6000 + i as u16)).into(),
                )
            })
            .collect();
        let domains = ids
            .into_iter()
            .zip(["a", "b", "c", "a", "c"].map(String::from))
            .collect();
        let placement = Placement::new(&keepers, domains, BTreeSet::new()).unwrap();
        let [a, b, c, d, e] = ids.map(|id| id.as_u128());
        let configs = vec![BTreeSet::from([a, b, c]), BTreeSet::from([b, d, e])];
        let nodes = ids
            .into_iter()
            .map(|id| (id.as_u128(), BasicNode::default()))
            .collect::<BTreeMap<_, _>>();
        assert!(
            placement
                .membership(&openraft::Membership::new(configs.clone(), nodes.clone()).unwrap())
        );
        let invalid = vec![configs[0].clone(), BTreeSet::from([a, b, d])];
        assert!(!placement.membership(&openraft::Membership::new(invalid, nodes).unwrap()));
        for lost in ["a", "b", "c"] {
            for side in &configs {
                assert_eq!(
                    side.iter()
                        .filter(|id| placement.eligible[&Uuid::from_u128(**id)] != lost)
                        .count(),
                    2
                );
            }
        }
    }

    #[test]
    fn five_voters_may_share_a_domain_but_never_hand_one_a_quorum() {
        let ids = [1, 2, 3, 4, 5, 6, 7].map(Uuid::from_u128);
        let keepers = ids
            .into_iter()
            .enumerate()
            .map(|(i, id)| {
                (
                    id,
                    std::net::SocketAddr::from(([127, 0, 0, 1], 6000 + i as u16)).into(),
                )
            })
            .collect();
        let domains = ids
            .into_iter()
            .zip(["a", "a", "b", "b", "c", "a", "d"].map(String::from))
            .collect();
        let placement = Placement::new(&keepers, domains, BTreeSet::new()).unwrap();
        let roster = |ids: &[u128]| {
            Voters::sorted(&ids.iter().copied().map(Uuid::from_u128).collect::<Vec<_>>()).unwrap()
        };
        assert!(placement.roster(&roster(&[1, 2, 3, 4, 5])), "2+2+1");
        assert!(placement.roster(&roster(&[1, 3, 4, 5, 7])), "1+2+1+1");
        assert!(
            !placement.roster(&roster(&[1, 2, 6, 3, 5])),
            "a holds three"
        );
        assert!(
            !placement.roster(&roster(&[1, 2, 3])),
            "three voters need three domains"
        );
        assert!(placement.roster(&roster(&[1, 3, 5])));
        // A move keeps the replication factor.
        let stage = Stage {
            stream: journal_contract::StreamId(1),
            source: 1,
            old: roster(&[1, 3, 5]),
            target: roster(&[1, 2, 3, 4, 5]),
        };
        assert!(!placement.stage(&stage));
        // Both sides of a five-voter joint configuration have five voters.
        let nodes = ids
            .into_iter()
            .map(|id| (id.as_u128(), BasicNode::default()))
            .collect::<BTreeMap<_, _>>();
        let joint = vec![
            BTreeSet::from([1, 2, 3, 4, 5]),
            BTreeSet::from([2, 3, 4, 5, 7]),
        ];
        assert!(placement.membership(&openraft::Membership::new(joint, nodes.clone()).unwrap()));
        let mixed = vec![BTreeSet::from([1, 3, 5]), BTreeSet::from([2, 3, 4, 5, 7])];
        assert!(!placement.membership(&openraft::Membership::new(mixed, nodes).unwrap()));
    }
}
