//! Fixed fields of an LKORPC04 voter exchange.

use super::slot_header::{bytes_equal, read_be, read_field, write_be};

pub(super) const TRANSPORT_MAGIC: [u8; 8] = *b"LKORPC04";
pub(super) const PREPARE: u8 = 1;
pub(super) const ACCEPT: u8 = 2;
pub(super) const PROMISE: u8 = 3;
pub(super) const VOTE: u8 = 4;
pub(super) const DEPOSED: u8 = 5;
pub(super) const REJECTED: u8 = 6;

pub(super) struct BallotFields {
    pub(super) round: u64,
    pub(super) nonce: [u8; 16],
}

pub(super) struct ImageFields {
    pub(super) generation: u64,
    pub(super) digest: [u8; 32],
}

pub(super) struct VoteSlots {
    pub(super) selected: u8,
    pub(super) images: [ImageFields; 2],
}

pub(super) enum ResponseKind {
    Expected,
    Deposed,
    Rejected,
    Invalid,
}

pub(super) fn transport_magic_matches(magic: &[u8; 8]) -> bool {
    bytes_equal(magic, &TRANSPORT_MAGIC)
}

pub(super) fn transport_group_matches(
    group: &[u8; 32],
    authorized: &[u8; 32],
    installed: &[u8; 32],
) -> bool {
    bytes_equal(group, authorized) && bytes_equal(group, installed)
}

pub(super) fn transport_voter_matches(voter: &[u8; 16], expected: &[u8; 16]) -> bool {
    bytes_equal(voter, expected)
}

pub(super) fn response_kind(kind: u8, expected: u8) -> ResponseKind {
    match kind {
        kind if kind == expected => ResponseKind::Expected,
        DEPOSED => ResponseKind::Deposed,
        REJECTED => ResponseKind::Rejected,
        _ => ResponseKind::Invalid,
    }
}

pub(super) fn encode_ballot(round: u64, nonce: &[u8; 16]) -> [u8; 24] {
    let mut bytes = [0; 24];
    bytes[..8].copy_from_slice(&write_be(round));
    bytes[8..].copy_from_slice(nonce);
    bytes
}

pub(super) fn decode_ballot(bytes: &[u8]) -> Option<BallotFields> {
    if bytes.len() != 24 {
        return None;
    }
    let round = read_be(read_field(bytes, 0));
    let nonce = read_field(bytes, 8);
    if round == 0 || bytes_equal(&nonce, &[0; 16]) {
        return None;
    }
    Some(BallotFields { round, nonce })
}

pub(super) fn vote_read_back_matches(tag: u8, requested: bool) -> bool {
    tag == u8::from(requested)
}

pub(super) fn decode_vote_slots(bytes: &[u8]) -> Option<VoteSlots> {
    if bytes.len() != 81 {
        return None;
    }
    Some(VoteSlots {
        selected: bytes[0],
        images: [
            ImageFields {
                generation: read_be(read_field(bytes, 1)),
                digest: read_field(bytes, 9),
            },
            ImageFields {
                generation: read_be(read_field(bytes, 41)),
                digest: read_field(bytes, 49),
            },
        ],
    })
}
