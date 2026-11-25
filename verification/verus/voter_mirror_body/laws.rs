use crate::production::mirror_body;
use vstd::prelude::*;

verus! {

pub fn complete_mirror_preserves_original_bytes(
    length: usize, framing: &[u8], body: &[u8], original_framing: &[u8], original_body: &[u8],
) -> (matches: bool)
    ensures matches ==> framing@ + body@ == original_framing@ + original_body@
        && (framing@ + body@).len() == length,
{
    let mut compare = mirror_body(length);
    compare.observe(original_framing, framing);
    compare.observe(original_body, body);
    compare.matches()
}

}
