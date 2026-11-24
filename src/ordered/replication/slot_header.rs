//! Fixed-width descriptor and checksum of an LKORV005 slot.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn voterSlotMagic() -> Seq<u8> {
    seq![76u8, 75, 79, 82, 86, 48, 48, 53]
}

pub(crate) open spec fn decodeBE(bytes: Seq<u8>) -> u64 {
    ((bytes[0] as u64) << 56)
        | ((bytes[1] as u64) << 48)
        | ((bytes[2] as u64) << 40)
        | ((bytes[3] as u64) << 32)
        | ((bytes[4] as u64) << 24)
        | ((bytes[5] as u64) << 16)
        | ((bytes[6] as u64) << 8)
        | bytes[7] as u64
}

pub(super) open spec fn encodeBE(value: u64) -> Seq<u8> {
    seq![
        (value >> 56) as u8, (value >> 48) as u8, (value >> 40) as u8, (value >> 32) as u8,
        (value >> 24) as u8, (value >> 16) as u8, (value >> 8) as u8, value as u8,
    ]
}

pub(super) proof fn big_endian_round_trips(value: u64)
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

pub(super) open spec fn slotDescriptor(group: Seq<u8>, voter: Seq<u8>, generation: u64, length: u64)
    -> Seq<u8>
{
    voterSlotMagic() + group + voter + encodeBE(generation) + encodeBE(length)
}

pub(super) open spec fn slotHeaderLengthValid(bytes: Seq<u8>, payload_limit: usize) -> bool {
    bytes.len() == 104 && 2 <= decodeBE(bytes.subrange(64, 72)) <= payload_limit
}

pub(super) open spec fn slotHeaderMatches(header: SlotHeader, group: Seq<u8>, voter: Seq<u8>) -> bool {
    header.descriptor.magic@ == voterSlotMagic()
        && header.descriptor.group@ == group
        && header.descriptor.voter@ == voter
        && header.descriptor.generation != 0
}

}

const MAGIC: [u8; 8] = [b'L', b'K', b'O', b'R', b'V', b'0', b'0', b'5'];
pub(super) const DESCRIPTOR_BYTES: usize = 72;
pub(crate) const HEADER: usize = DESCRIPTOR_BYTES + 32;

pub(super) struct SlotDescriptor {
    pub(super) magic: [u8; 8],
    pub(super) group: [u8; 32],
    pub(super) voter: [u8; 16],
    pub(super) generation: u64,
}

pub(super) struct SlotHeader {
    pub(super) descriptor: SlotDescriptor,
    pub(super) length: usize,
    pub(super) digest: [u8; 32],
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires offset as int + N as int <= bytes@.len(), offset as int + N as int <= usize::MAX,
    ensures out@ == bytes@.subrange(offset as int, offset as int + N as int),
))]
pub(super) fn read_field<const N: usize>(bytes: &[u8], offset: usize) -> [u8; N] {
    let mut field = [0; N];
    field.copy_from_slice(&bytes[offset..offset + N]);
    field
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == decodeBE(bytes@),))]
pub(super) fn read_be(bytes: [u8; 8]) -> u64 {
    ((bytes[0] as u64) << 56)
        | ((bytes[1] as u64) << 48)
        | ((bytes[2] as u64) << 40)
        | ((bytes[3] as u64) << 32)
        | ((bytes[4] as u64) << 24)
        | ((bytes[5] as u64) << 16)
        | ((bytes[6] as u64) << 8)
        | bytes[7] as u64
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ =~= encodeBE(value),))]
pub(super) fn write_be(value: u64) -> [u8; 8] {
    [
        (value >> 56) as u8,
        (value >> 48) as u8,
        (value >> 40) as u8,
        (value >> 32) as u8,
        (value >> 24) as u8,
        (value >> 16) as u8,
        (value >> 8) as u8,
        value as u8,
    ]
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ =~= slotDescriptor(group@, voter@, generation, length),))]
pub(super) fn encode_descriptor(
    group: &[u8; 32],
    voter: &[u8; 16],
    generation: u64,
    length: u64,
) -> [u8; DESCRIPTOR_BYTES] {
    let mut bytes = [0; DESCRIPTOR_BYTES];
    bytes[..8].copy_from_slice(&MAGIC);
    bytes[8..40].copy_from_slice(group);
    bytes[40..56].copy_from_slice(voter);
    bytes[56..64].copy_from_slice(&write_be(generation));
    bytes[64..72].copy_from_slice(&write_be(length));
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(MAGIC@ =~= voterSlotMagic());
        assert(bytes@ =~= slotDescriptor(group@, voter@, generation, length));
    }
    bytes
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ =~= descriptor@ + digest@,))]
pub(super) fn encode_header(
    descriptor: &[u8; DESCRIPTOR_BYTES],
    digest: &[u8; 32],
) -> [u8; HEADER] {
    let mut bytes = [0; HEADER];
    bytes[..DESCRIPTOR_BYTES].copy_from_slice(descriptor);
    bytes[DESCRIPTOR_BYTES..].copy_from_slice(digest);
    bytes
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out.is_some() == slotHeaderLengthValid(bytes@, payload_limit),
        out matches Some(header) ==> {
            &&& header.descriptor.magic@ == bytes@.subrange(0, 8)
            &&& header.descriptor.group@ == bytes@.subrange(8, 40)
            &&& header.descriptor.voter@ == bytes@.subrange(40, 56)
            &&& header.descriptor.generation == decodeBE(bytes@.subrange(56, 64))
            &&& header.length as u64 == decodeBE(bytes@.subrange(64, 72))
            &&& header.digest@ == bytes@.subrange(72, 104)
        },
))]
pub(super) fn decode_header(bytes: &[u8], payload_limit: usize) -> Option<SlotHeader> {
    if bytes.len() != HEADER {
        return None;
    }
    let length = read_be(read_field(bytes, 64));
    // The two ballot tags are always present, even for an uninitialized voter.
    if length < 2 || length > payload_limit as u64 {
        return None;
    }
    Some(SlotHeader {
        descriptor: SlotDescriptor {
            magic: read_field(bytes, 0),
            group: read_field(bytes, 8),
            voter: read_field(bytes, 40),
            generation: read_be(read_field(bytes, 56)),
        },
        length: length as usize,
        digest: read_field(bytes, DESCRIPTOR_BYTES),
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (left@ == right@),))]
pub(super) fn bytes_equal<const N: usize>(left: &[u8; N], right: &[u8; N]) -> bool {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= N,
            forall|j: int| 0 <= j < i ==> left@[j] == right@[j],
        decreases N - i,
    ))]
    while i < N {
        if left[i] != right[i] {
            return false;
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(left@ =~= right@);
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == slotHeaderMatches(*header, group@, voter@),))]
pub(super) fn matches_slot(header: &SlotHeader, group: &[u8; 32], voter: &[u8; 16]) -> bool {
    let descriptor = &header.descriptor;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(MAGIC@ =~= voterSlotMagic());
    }
    bytes_equal(&descriptor.magic, &MAGIC)
        && bytes_equal(&descriptor.group, group)
        && bytes_equal(&descriptor.voter, voter)
        && descriptor.generation != 0
}
