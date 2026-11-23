//! Fixed-width descriptor and checksum of an LKORV005 slot.

const MAGIC: [u8; 8] = *b"LKORV005";
pub(super) const DESCRIPTOR_BYTES: usize = 72;
pub(super) const HEADER: usize = DESCRIPTOR_BYTES + 32;

pub(super) struct SlotDescriptor {
    magic: [u8; 8],
    group: [u8; 32],
    voter: [u8; 16],
    pub(super) generation: u64,
}

pub(super) struct SlotHeader {
    pub(super) descriptor: SlotDescriptor,
    pub(super) length: usize,
    pub(super) digest: [u8; 32],
}

fn read_field<const N: usize>(bytes: &[u8], offset: usize) -> [u8; N] {
    let mut field = [0; N];
    field.copy_from_slice(&bytes[offset..offset + N]);
    field
}

fn read_be(bytes: [u8; 8]) -> u64 {
    ((bytes[0] as u64) << 56)
        | ((bytes[1] as u64) << 48)
        | ((bytes[2] as u64) << 40)
        | ((bytes[3] as u64) << 32)
        | ((bytes[4] as u64) << 24)
        | ((bytes[5] as u64) << 16)
        | ((bytes[6] as u64) << 8)
        | bytes[7] as u64
}

fn write_be(value: u64) -> [u8; 8] {
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
    bytes
}

pub(super) fn encode_header(
    descriptor: &[u8; DESCRIPTOR_BYTES],
    digest: &[u8; 32],
) -> [u8; HEADER] {
    let mut bytes = [0; HEADER];
    bytes[..DESCRIPTOR_BYTES].copy_from_slice(descriptor);
    bytes[DESCRIPTOR_BYTES..].copy_from_slice(digest);
    bytes
}

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

fn bytes_equal<const N: usize>(left: &[u8; N], right: &[u8; N]) -> bool {
    let mut i = 0;
    while i < N {
        if left[i] != right[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub(super) fn matches_slot(header: &SlotHeader, group: &[u8; 32], voter: &[u8; 16]) -> bool {
    let descriptor = &header.descriptor;
    bytes_equal(&descriptor.magic, &MAGIC)
        && bytes_equal(&descriptor.group, group)
        && bytes_equal(&descriptor.voter, voter)
        && descriptor.generation != 0
}
