#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) struct MirrorBody {
    remaining: usize,
    equal: bool,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl MirrorBody {
        pub(super) closed spec fn bytes_left(&self) -> int { self.remaining as int }
        pub(super) closed spec fn equal_so_far(&self) -> bool { self.equal }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out.bytes_left() == length && out.equal_so_far(),
))]
pub(super) fn mirror_body(length: usize) -> MirrorBody {
    MirrorBody { remaining: length, equal: true }
}

impl MirrorBody {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            final(self).bytes_left() == if expected@.len() <= old(self).bytes_left()
                { old(self).bytes_left() - expected@.len() } else { 0 },
            final(self).equal_so_far() == (old(self).equal_so_far()
                && expected@.len() <= old(self).bytes_left() && observed@ == expected@),
    ))]
    pub(super) fn observe(&mut self, expected: &[u8], observed: &[u8]) {
        if let Some(remaining) = self.remaining.checked_sub(expected.len()) {
            self.remaining = remaining;
            self.equal = self.equal && matches_bytes(expected, observed);
        } else {
            self.remaining = 0;
            self.equal = false;
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
        out == (self.bytes_left() == 0 && self.equal_so_far()),
    ))]
    pub(super) fn matches(&self) -> bool {
        self.remaining == 0 && self.equal
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (expected@ == observed@)))]
fn matches_bytes(expected: &[u8], observed: &[u8]) -> bool {
    let equal = <[u8] as PartialEq>::eq(expected, observed);
    #[cfg(verus_keep_ghost)]
    proof! {
        use vstd::std_specs::cmp::PartialEqSpec;
        assert(<[u8] as PartialEqSpec<[u8]>>::obeys_eq_spec());
        assert(equal == <[u8] as PartialEqSpec<[u8]>>::eq_spec(expected, observed));
        assert(equal == (expected@ =~= observed@));
    }
    equal
}
