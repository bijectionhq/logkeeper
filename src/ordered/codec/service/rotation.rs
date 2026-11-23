//! Encoding shared by rotation replies and the signed evidence transcript.

use super::{BufMut, BytesMut, RotationSlots, checkpoint, uuid};

#[cfg(verus_keep_ghost)]
use super::{rotation_header, voter_wire, voters_wire};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl RotationSlots {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(output).contents@ == old(output).contents@ + rotation_header(self)
            + voters_wire(self.voters@),
    ))]
    pub(crate) fn encode(&self, output: &mut BytesMut) {
        #[cfg(verus_keep_ghost)]
        let original = output.contents;
        output.put_slice(&self.group);
        output.put_u64(self.cohort_size as u64);
        output.put_u64(self.ballot.round);
        uuid(output, self.ballot.nonce);
        output.put_slice(&self.prefix);
        output.put_u64(self.position);
        checkpoint(output, self.checkpoint);
        output.put_u64(self.key_generation);
        output.put_u64(self.voters.len() as u64);
        let mut index = 0;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(output.contents@ =~= original@ + rotation_header(self));
            assert(self.voters@.take(0) =~= Seq::empty());
            assert(voters_wire(self.voters@.take(0)) =~= Seq::empty());
            assert(output.contents@ =~= original@ + rotation_header(self) + voters_wire(self.voters@.take(0)));
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                index <= self.voters@.len(),
                output.contents@ == original@ + rotation_header(self)
                    + voters_wire(self.voters@.take(index as int)),
            decreases self.voters@.len() - index,
        ))]
        while index < self.voters.len() {
            #[cfg(verus_keep_ghost)]
            let prior = output.contents;
            let voter = &self.voters[index];
            uuid(output, voter.voter);
            output.put_u8(voter.slots.selected);
            let [first, second] = voter.slots.images;
            output.put_u64(first.generation);
            output.put_slice(&first.digest);
            output.put_u64(second.generation);
            output.put_slice(&second.digest);
            #[cfg(verus_keep_ghost)]
            proof! {
                let prefix = self.voters@.take(index as int + 1);
                assert(prefix.drop_last() =~= self.voters@.take(index as int));
                assert(prefix.last() == *voter);
                assert(output.contents@ =~= prior@ + voter_wire(*voter));
                assert(voters_wire(prefix) == voters_wire(prefix.drop_last()) + voter_wire(*voter));
                assert(output.contents@ =~= original@ + rotation_header(self) + voters_wire(prefix));
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.voters@.take(index as int) =~= self.voters@); }
    }
}
