//! Recovery eligibility checks, between the media reader and the selector.

use super::selection::authenticates_body;
use super::{
    Error, File, Fingerprint, Group, HEADER, Selected, Uuid, decode_header, load_state,
    matches_slot, read_slot_body, read_slot_header,
};

#[cfg(verus_keep_ghost)]
use super::eligible_slot;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires size >= HEADER,
    ensures (*old(file)).snapshot() == final(file).snapshot(),
        out matches Ok((used, Some((selected, digest)))) ==>
            eligible_slot(old(file), group, voter, size, index, used, selected, digest),
))]
pub(crate) fn recover_slot(
    file: &mut File,
    index: usize,
    group: &Group,
    voter: Uuid,
    size: usize,
) -> Result<(usize, Option<(Selected, Fingerprint)>), Error> {
    let raw = read_slot_header(file)?;
    let payload_limit = size - HEADER;
    let Some(header) = decode_header(&raw, payload_limit) else {
        return Ok((payload_limit, None));
    };
    let length = header.length;
    let (body, observed) = read_slot_body(file, &raw, length)?;
    if !authenticates_body(&observed, &header.digest) {
        return Ok((payload_limit, None));
    }
    if !matches_slot(&header, &group.identity, voter.as_bytes()) {
        return Err(Error::Group);
    }
    let state = load_state(group, body)?;
    Ok((
        length,
        Some((
            Selected {
                index,
                generation: header.descriptor.generation,
                state,
            },
            header.digest,
        )),
    ))
}
