//! Releases exact slot evidence for a fresh or retained rotation receipt.

use super::{Chosen, Command, Request, RotationSlots};

#[cfg(verus_keep_ghost)]
use super::{agrees_with_rotation, covers_rotation, suffix_matches};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Chosen {
    /// A retained rotation can be attested again while the recovered head
    /// still serves from its exact clean checkpoint and generation.
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out matches Some(evidence) ==> agrees_with_rotation(self, request, &evidence),
    ))]
    pub(crate) fn rotation_slots(&self, request: &Request) -> Option<RotationSlots> {
        let Command::PublishAndRotate { grant, checkpoint } = request.command else {
            return None;
        };
        if request.placement != self.receipt.placement
            || request.principal != self.receipt.principal
            || request.id != self.receipt.request
            || grant.key_generation.checked_add(1) != Some(self.state.authority.key_generation)
            || checkpoint != self.state.checkpoint()
            || !self.rotation_suffix_matches(checkpoint.cut.next_lsn)
        {
            return None;
        }
        let evidence = RotationSlots {
            group: self.group,
            cohort_size: self.cohort_size,
            ballot: self.ballot,
            prefix: self.prefix,
            position: self.state.position(),
            checkpoint,
            key_generation: self.state.authority.key_generation,
            voters: self.images.clone(),
        };
        if evidence.covers(self.receipt) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(evidence.voters@ =~= self.images@);
                assert(covers_rotation(&evidence, self.receipt));
            }
            Some(evidence)
        } else {
            None
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == suffix_matches(self.state.records@, next_lsn, self.state.authority.key_generation, self.state.records@.len() as int),
    ))]
    fn rotation_suffix_matches(&self, next_lsn: u64) -> bool {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant suffix_matches(self.state.records@, next_lsn, self.state.authority.key_generation, index as int),
            decreases self.state.records@.len() - index,
        ))]
        while index < self.state.records.len() {
            let record = &self.state.records[index];
            if record.result.lsn >= next_lsn
                && record.grant.key_generation != self.state.authority.key_generation
            {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(!suffix_matches(self.state.records@, next_lsn, self.state.authority.key_generation,
                        self.state.records@.len() as int));
                }
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i: int| 0 <= i <= index
                    && #[trigger] self.state.records@[i].result.lsn >= next_lsn implies
                    self.state.records@[i].grant.key_generation == self.state.authority.key_generation by {
                    if i == index as int {
                        assert(self.state.records@[i] == *record);
                    }
                }
            }
            index += 1;
        }
        true
    }
}
