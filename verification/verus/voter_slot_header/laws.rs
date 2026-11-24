use crate::production::{
    decodeBE, decode_header, encodeBE, encode_descriptor, encode_header, matches_slot,
    slotHeaderLengthValid, voterSlotMagic,
};
use vstd::prelude::*;

verus! {

proof fn big_endian_round_trips(value: u64)
    ensures decodeBE(encodeBE(value)) == value,
{
    let bytes = encodeBE(value);
    let b0 = bytes[0];
    let b1 = bytes[1];
    let b2 = bytes[2];
    let b3 = bytes[3];
    let b4 = bytes[4];
    let b5 = bytes[5];
    let b6 = bytes[6];
    let b7 = bytes[7];
    assert(
        ((b0 as u64) << 56) | ((b1 as u64) << 48)
        | ((b2 as u64) << 40) | ((b3 as u64) << 32)
        | ((b4 as u64) << 24) | ((b5 as u64) << 16)
        | ((b6 as u64) << 8) | b7 as u64 == value
    ) by (bit_vector)
        requires
            b0 == (value >> 56) as u8, b1 == (value >> 48) as u8,
            b2 == (value >> 40) as u8, b3 == (value >> 32) as u8,
            b4 == (value >> 24) as u8, b5 == (value >> 16) as u8,
            b6 == (value >> 8) as u8, b7 == value as u8,
    ;
}

fn voter_slot_header_round_trips(
    group: &[u8; 32], voter: &[u8; 16], generation: u64, length: usize,
    digest: &[u8; 32], limit: usize,
)
    requires 2 <= length <= limit, generation != 0,
{
    let descriptor = encode_descriptor(group, voter, generation, length as u64);
    let bytes = encode_header(&descriptor, digest);
    proof {
        big_endian_round_trips(generation);
        big_endian_round_trips(length as u64);
        assert(bytes@.subrange(0, 8) =~= voterSlotMagic());
        assert(bytes@.subrange(8, 40) =~= group@);
        assert(bytes@.subrange(40, 56) =~= voter@);
        assert(bytes@.subrange(56, 64) =~= encodeBE(generation));
        assert(bytes@.subrange(64, 72) =~= encodeBE(length as u64));
        assert(bytes@.subrange(72, 104) =~= digest@);
        assert(slotHeaderLengthValid(bytes@, limit));
    }
    let parsed = decode_header(&bytes, limit);
    assert(parsed.is_some());
    if let Some(header) = parsed {
        assert(header.length == length);
        assert(header.descriptor.generation == generation);
        assert(header.digest@ == digest@);
        let matches = matches_slot(&header, group, voter);
        assert(matches);
    }
}

fn voter_slot_header_rejects_inexact_extent(bytes: &[u8], limit: usize)
    requires bytes@.len() != 104,
{
    let parsed = decode_header(bytes, limit);
    assert(parsed.is_none());
}

fn voter_slot_scope_is_exact(bytes: &[u8], limit: usize, group: &[u8; 32], voter: &[u8; 16]) {
    if let Some(header) = decode_header(bytes, limit) {
        let matches = matches_slot(&header, group, voter);
        assert(matches == (
            bytes@.subrange(0, 8) == voterSlotMagic()
            && bytes@.subrange(8, 40) == group@
            && bytes@.subrange(40, 56) == voter@
            && decodeBE(bytes@.subrange(56, 64)) != 0
        ));
    }
}

}
