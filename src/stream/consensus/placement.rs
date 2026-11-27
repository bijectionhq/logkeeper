use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::Arc,
};

use openraft::BasicNode;
use uuid::Uuid;

use super::{Genesis, Keepers, NodeId, Stage, invalid};

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

    /// Strict placement check: three sorted active (non-retired) keepers in
    /// distinct failure domains.
    pub fn roster(&self, voters: &[Uuid; 3]) -> bool {
        let [a, b, c] = *voters;
        if !(a < b && b < c) {
            return false;
        }
        match (
            self.eligible.get(&a),
            self.eligible.get(&b),
            self.eligible.get(&c),
        ) {
            (Some(a), Some(b), Some(c)) => a != b && b != c && a != c,
            _ => false,
        }
    }

    /// Structural check: three sorted known keepers (active or retired).
    pub fn structural_roster(&self, voters: &[Uuid; 3]) -> bool {
        let [a, b, c] = *voters;
        a < b && b < c && self.known(a) && self.known(b) && self.known(c)
    }

    /// Strict check for a new stage: the old roster only needs to be
    /// structurally valid (so a placement-violating or retired-voter stream can
    /// move), while the target roster must satisfy current strict placement.
    pub fn stage(&self, stage: &Stage) -> bool {
        stage.old != stage.target
            && self.structural_roster(&stage.old)
            && self.roster(&stage.target)
    }

    /// Structural check for historical/replayed stage records.
    pub fn structural_stage(&self, stage: &Stage) -> bool {
        stage.old != stage.target
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
                if voters.len() != 3 {
                    return false;
                }
                let mut voters = voters.iter().map(|id| Uuid::from_u128(*id));
                self.roster(&std::array::from_fn(|_| voters.next().unwrap()))
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
                if voters.len() != 3 {
                    return false;
                }
                let mut voters = voters.iter().map(|id| Uuid::from_u128(*id));
                self.structural_roster(&std::array::from_fn(|_| voters.next().unwrap()))
            })
    }
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
}
