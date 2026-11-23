//! Recovery eligibility checks, between the media reader and the selector.

use super::selection::{authenticates_body, slot_body_length, slot_header_matches};
use super::{
    Error, File, Fingerprint, Group, Selected, Uuid, load_state, read_slot_body,
    read_slot_header,
};

pub(crate) const HEADER: usize = 8 + 32 + 16 + 8 + 8 + 32;

#[derive(Clone, Copy)]
pub(super) struct SlotHeader {
    pub raw: [u8; HEADER],
    pub empty: bool,
    pub magic: [u8; 8],
    pub addressed: Fingerprint,
    pub witness: u128,
    pub generation: u64,
    pub length: u64,
    pub digest: Fingerprint,
}

pub(super) fn recover_slot(
    file: &mut File,
    index: usize,
    group: &Group,
    voter: Uuid,
    size: usize,
) -> Result<(usize, Option<(Selected, Fingerprint)>), Error> {
    let header = read_slot_header(file)?;
    let payload_limit = size - HEADER;
    if header.empty {
        return Ok((payload_limit, None));
    }
    let Some(length) = slot_body_length(header.length, payload_limit) else {
        return Ok((payload_limit, None));
    };
    let (body, observed) = read_slot_body(file, &header, length)?;
    if !authenticates_body(&observed, &header.digest) {
        return Ok((payload_limit, None));
    }
    if !slot_header_matches(
        &header.magic,
        &header.addressed,
        &group.identity,
        header.witness,
        voter.as_u128(),
        header.generation,
    ) {
        return Err(Error::Group);
    }
    let state = load_state(group, body)?;
    Ok((
        length,
        Some((
            Selected {
                index,
                generation: header.generation,
                state,
            },
            header.digest,
        )),
    ))
}
