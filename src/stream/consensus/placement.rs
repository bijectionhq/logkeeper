use std::{collections::BTreeMap, io, sync::Arc};

use openraft::BasicNode;
use uuid::Uuid;

use super::{Genesis, Keepers, NodeId, Stage, invalid};

/// Operator-certified failure domains, keyed by keeper incarnation.
pub type Domains = BTreeMap<Uuid, String>;

#[derive(Clone)]
pub(super) struct Placement(Arc<Domains>);

impl Placement {
    pub fn new(keepers: &Keepers, domains: Domains) -> io::Result<Self> {
        if !keepers.keys().eq(domains.keys())
            || domains
                .values()
                .any(|domain| domain.trim() != domain || domain.is_empty() || domain.len() > 256)
        {
            return Err(invalid("every keeper needs a declared failure domain"));
        }
        Ok(Self(Arc::new(domains)))
    }

    pub fn genesis(&self, genesis: &Genesis) -> bool {
        genesis.stream.0 != 0 && genesis.quota_bytes > 0 && self.roster(&genesis.voters)
    }

    pub fn roster(&self, voters: &[Uuid; 3]) -> bool {
        let [a, b, c] = *voters;
        if !(a < b && b < c) {
            return false;
        }
        match (self.0.get(&a), self.0.get(&b), self.0.get(&c)) {
            (Some(a), Some(b), Some(c)) => a != b && b != c && a != c,
            _ => false,
        }
    }

    pub fn stage(&self, stage: &Stage) -> bool {
        stage.old != stage.target && self.roster(&stage.old) && self.roster(&stage.target)
    }

    pub fn membership(&self, membership: &openraft::Membership<NodeId, BasicNode>) -> bool {
        let configs = membership.get_joint_config();
        (1..=2).contains(&configs.len())
            && membership
                .nodes()
                .all(|(id, _)| self.0.contains_key(&Uuid::from_u128(*id)))
            && configs.iter().all(|voters| {
                if voters.len() != 3 {
                    return false;
                }
                let mut voters = voters.iter().map(|id| Uuid::from_u128(*id));
                self.roster(&std::array::from_fn(|_| voters.next().unwrap()))
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn loss_of_any_declared_domain_leaves_both_joint_majorities() {
        let ids = [1, 2, 3, 4, 5].map(Uuid::from_u128);
        let keepers = ids
            .into_iter()
            .enumerate()
            .map(|(i, id)| (id, ([127, 0, 0, 1], 6000 + i as u16).into()))
            .collect();
        let domains = ids
            .into_iter()
            .zip(["a", "b", "c", "a", "c"].map(String::from))
            .collect();
        let placement = Placement::new(&keepers, domains).unwrap();
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
                        .filter(|id| placement.0[&Uuid::from_u128(**id)] != lost)
                        .count(),
                    2
                );
            }
        }
    }
}
