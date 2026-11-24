//! Byte codecs shared by WAL and checkpoint storage. Payloads are borrowed or
//! copied verbatim, so framing never requires a second payload-sized allocation.

use super::wal_layout::{checksum_matches, frame_body_fits, stored_length};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) const FRAME_HEADER_BYTES: usize = 8;
pub(super) const FRAGMENT_PREFIX_BYTES: usize = 17;
pub(super) const FRAME_OVERHEAD: usize = FRAME_HEADER_BYTES + FRAGMENT_PREFIX_BYTES;

#[cfg(verus_keep_ghost)]
verus! {

/// The CRC-32/ISO-HDLC value (RFC 1952, §8) of the exact input octets.
pub(super) uninterp spec fn crc32(bytes: Seq<u8>) -> u32;

}

#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == crc32(prefix@ + bytes@)))]
pub(super) fn checksum(prefix: &[u8], bytes: &[u8]) -> u32 {
    // Premise: crc32fast computes the deterministic IEEE CRC-32 of these bytes.
    // https://docs.rs/crc32fast/1.5.0/crc32fast/struct.Hasher.html
    // https://www.rfc-editor.org/rfc/rfc1952#section-8
    #[cfg(not(verus_keep_ghost))]
    {
        let mut crc = crc32fast::Hasher::new();
        if !prefix.is_empty() {
            crc.update(prefix);
        }
        crc.update(bytes);
        crc.finalize()
    }
    #[cfg(verus_keep_ghost)]
    unreachable!()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((field, rest)) =>
            N <= bytes@.len() && field@ == bytes@.take(N as int)
                && rest@ == bytes@.skip(N as int),
        None => bytes@.len() < N,
    }
))]
pub(super) fn take<const N: usize>(bytes: &[u8]) -> Option<([u8; N], &[u8])> {
    let (field, rest) = bytes.split_at_checked(N)?;
    let mut value = [0; N];
    value.copy_from_slice(field);
    Some((value, rest))
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn be32(value: u32) -> Seq<u8> {
    seq![
        ((value >> 24) & 0xff) as u8,
        ((value >> 16) & 0xff) as u8,
        ((value >> 8) & 0xff) as u8,
        (value & 0xff) as u8,
    ]
}

pub(super) open spec fn read_be32(bytes: Seq<u8>) -> u32 {
    ((bytes[0] as u32) << 24)
        | ((bytes[1] as u32) << 16)
        | ((bytes[2] as u32) << 8)
        | (bytes[3] as u32)
}

pub(super) proof fn be32_inverse(value: u32, bytes: Seq<u8>)
    requires bytes.len() == 4,
    ensures read_be32(be32(value)) == value, be32(read_be32(bytes)) == bytes,
{
    assert(value == (((((value >> 24) & 0xff) as u8) as u32) << 24) | (((((value >> 16) & 0xff) as u8) as u32) << 16) | (((((value >> 8) & 0xff) as u8) as u32) << 8) | (((value & 0xff) as u8) as u32)) by (bit_vector);
    assert(read_be32(be32(value)) == value);
    let b0 = bytes[0];
    let b1 = bytes[1];
    let b2 = bytes[2];
    let b3 = bytes[3];
    let word = read_be32(bytes);
    assert(word == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32));
    assert(
        b0 == ((word >> 24) & 0xff) as u8
            && b1 == ((word >> 16) & 0xff) as u8
            && b2 == ((word >> 8) & 0xff) as u8
            && b3 == (word & 0xff) as u8
    ) by (bit_vector) requires word == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    assert(be32(word) =~= bytes);
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == be32(value)))]
pub(super) fn encode_u32(value: u32) -> [u8; 4] {
    let output = [
        ((value >> 24) & 0xff) as u8,
        ((value >> 16) & 0xff) as u8,
        ((value >> 8) & 0xff) as u8,
        (value & 0xff) as u8,
    ];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~= be32(value));
    }
    output
}
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == read_be32(bytes@)))]
pub(super) fn decode_u32(bytes: [u8; 4]) -> u32 {
    ((bytes[0] as u32) << 24)
        | ((bytes[1] as u32) << 16)
        | ((bytes[2] as u32) << 8)
        | bytes[3] as u32
}
#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn be64(value: u64) -> Seq<u8> {
    be32((value >> 32) as u32) + be32(value as u32)
}

pub(super) open spec fn read_be64(bytes: Seq<u8>) -> u64 {
    ((read_be32(bytes.take(4)) as u64) << 32) | read_be32(bytes.skip(4)) as u64
}

pub(super) proof fn be64_inverse(value: u64, bytes: Seq<u8>)
    requires bytes.len() == 8,
    ensures read_be64(be64(value)) == value, be64(read_be64(bytes)) == bytes,
{
    let high = bytes.take(4);
    let low = bytes.skip(4);
    let upper = (value >> 32) as u32;
    let lower = value as u32;
    be32_inverse(upper, high);
    be32_inverse(lower, low);
    assert(be64(value).take(4) =~= be32(upper));
    assert(be64(value).skip(4) =~= be32(lower));
    assert((((value >> 32) as u32) as u64) << 32 | (value as u32) as u64 == value)
        by (bit_vector);
    let x = read_be32(high);
    let y = read_be32(low);
    let word = read_be64(bytes);
    assert((word >> 32) as u32 == x && word as u32 == y) by (bit_vector)
        requires word == ((x as u64) << 32) | y as u64;
    assert(high + low =~= bytes);
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == be64(value)))]
pub(super) fn encode_u64(value: u64) -> [u8; 8] {
    let [a, b, c, d] = encode_u32((value >> 32) as u32);
    let [e, f, g, h] = encode_u32(value as u32);
    let output = [a, b, c, d, e, f, g, h];
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= be64(value)); }
    output
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == read_be64(bytes@)))]
pub(super) fn decode_u64(bytes: [u8; 8]) -> u64 {
    let [a, b, c, d, e, f, g, h] = bytes;
    let high = [a, b, c, d];
    let low = [e, f, g, h];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(high@ =~= bytes@.take(4));
        assert(low@ =~= bytes@.skip(4));
    }
    ((decode_u32(high) as u64) << 32) | decode_u32(low) as u64
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn be128(value: u128) -> Seq<u8> {
    be64((value >> 64) as u64) + be64(value as u64)
}

pub(super) open spec fn read_be128(bytes: Seq<u8>) -> u128 {
    ((read_be64(bytes.take(8)) as u128) << 64) | read_be64(bytes.skip(8)) as u128
}

pub(super) proof fn be128_inverse(value: u128, bytes: Seq<u8>)
    requires bytes.len() == 16,
    ensures read_be128(be128(value)) == value, be128(read_be128(bytes)) == bytes,
{
    let high = bytes.take(8);
    let low = bytes.skip(8);
    let upper = (value >> 64) as u64;
    let lower = value as u64;
    be64_inverse(upper, high);
    be64_inverse(lower, low);
    assert(be128(value).take(8) =~= be64(upper));
    assert(be128(value).skip(8) =~= be64(lower));
    assert((((value >> 64) as u64) as u128) << 64 | (value as u64) as u128 == value)
        by (bit_vector);
    let x = read_be64(high);
    let y = read_be64(low);
    let word = read_be128(bytes);
    assert((word >> 64) as u64 == x && word as u64 == y) by (bit_vector)
        requires word == ((x as u128) << 64) | y as u128;
    assert(high + low =~= bytes);
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == be128(value)))]
pub(super) fn encode_u128(value: u128) -> [u8; 16] {
    let [a, b, c, d, e, f, g, h] = encode_u64((value >> 64) as u64);
    let [i, j, k, l, m, n, o, p] = encode_u64(value as u64);
    let output = [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p];
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= be128(value)); }
    output
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == read_be128(bytes@)))]
pub(super) fn decode_u128(bytes: [u8; 16]) -> u128 {
    let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = bytes;
    let high = [a, b, c, d, e, f, g, h];
    let low = [i, j, k, l, m, n, o, p];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(high@ =~= bytes@.take(8));
        assert(low@ =~= bytes@.skip(8));
    }
    ((decode_u64(high) as u128) << 64) | decode_u64(low) as u128
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out@ == be32(len) + be32(crc)
))]
fn frame_header(len: u32, crc: u32) -> [u8; FRAME_HEADER_BYTES] {
    let [a, b, c, d] = encode_u32(len);
    let [e, f, g, h] = encode_u32(crc);
    let bytes = [a, b, c, d, e, f, g, h];
    #[cfg(verus_keep_ghost)]
    proof! { assert(bytes@ =~= frame_header_spec(len, crc)); }
    bytes
}

/// Encode the header for a body written as a prefix followed by its remaining bytes.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some(header) => prefix@.len() + body@.len() <= u32::MAX
            && header@ == frame_header_spec((prefix@.len() + body@.len()) as u32, crc32(prefix@ + body@)),
        None => prefix@.len() + body@.len() > u32::MAX,
    }
))]
pub(super) fn encode_frame(prefix: &[u8], body: &[u8]) -> Option<[u8; FRAME_HEADER_BYTES]> {
    let length = prefix.len().checked_add(body.len())?;
    let len = stored_length(length)?;
    Some(frame_header(len, checksum(prefix, body)))
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn frame_header_spec(len: u32, crc: u32) -> Seq<u8> {
    be32(len) + be32(crc)
}

pub(super) open spec fn frame_wire(
    word: spec_fn(u32) -> Seq<u8>, crc: spec_fn(Seq<u8>) -> u32, body: Seq<u8>,
) -> Seq<u8> {
    word(body.len() as u32) + word(crc(body)) + body
}

pub(super) open spec fn frame_bytes(body: Seq<u8>) -> Seq<u8> {
    frame_wire(|value| be32(value), |bytes| crc32(bytes), body)
}

pub(super) open spec fn frame_decode_wire(
    bytes: Seq<u8>, body: Seq<u8>, declared: nat, stored: u32, actual: u32, limit: nat,
) -> bool {
    bytes.len() == 8 + declared && declared <= limit && body == bytes.skip(8) && stored == actual
}

pub(super) open spec fn accepts_frame(bytes: Seq<u8>, body: Seq<u8>, max: int) -> bool {
    body.len() <= max && body.len() <= u32::MAX && bytes == frame_bytes(body)
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((len, crc)) => frame_body_fits_spec(remaining, len, max)
            && header@ == frame_header_spec(len, crc),
        None => header@.len() != FRAME_HEADER_BYTES
            || !frame_body_fits_spec(remaining, read_be32(header@.take(4)), max),
    }
))]
pub(super) fn decode_frame_header(header: &[u8], remaining: u64, max: usize) -> Option<(u32, u32)> {
    let (len, rest) = take::<4>(header)?;
    let (crc, rest) = take::<4>(rest)?;
    let len = decode_u32(len);
    if !rest.is_empty() || !frame_body_fits(remaining, len, max) {
        return None;
    }
    let actual = decode_u32(crc);
    #[cfg(verus_keep_ghost)]
    proof! {
        be32_inverse(len, header@.take(4));
        be32_inverse(actual, header@.subrange(4, 8));
        assert(crc@ =~= header@.subrange(4, 8));
        assert(header@ =~= frame_header_spec(len, actual));
    }
    Some((len, actual))
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn frame_body_fits_spec(remaining: u64, len: u32, max: usize) -> bool {
    len as int <= max as int && 8 + len as int <= remaining as int
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == (body@.len() == len as int && crc == crc32(body@))
))]
pub(super) fn decode_frame_body(len: u32, crc: u32, body: &[u8]) -> bool {
    body.len() == len as usize && checksum_matches(crc, checksum(&[], body))
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn fragment_wire(stream: Seq<u8>, flags: u8) -> Seq<u8> {
    stream + seq![flags]
}

pub(super) open spec fn fragment_prefix(stream: u128, flags: u8) -> Seq<u8> {
    fragment_wire(be128(stream), flags)
}

pub(super) open spec fn fragment_valid(stream: u128, flags: u8, payload: Seq<u8>) -> bool {
    (flags <= 3 && payload.len() > 0)
        || (stream == 0 && flags == 4 && payload == seq![0u8])
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == fragment_prefix(stream, flags)))]
pub(super) fn encode_fragment_prefix(stream: u128, flags: u8) -> [u8; FRAGMENT_PREFIX_BYTES] {
    let [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] = encode_u128(stream);
    let prefix = [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, flags];
    #[cfg(verus_keep_ghost)]
    proof! { assert(prefix@ =~= fragment_prefix(stream, flags)); }
    prefix
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((stream, flags, payload)) => fragment_valid(stream, flags, payload@)
            && bytes@ == fragment_prefix(stream, flags) + payload@,
        None => bytes@.len() <= 17
            || !fragment_valid(read_be128(bytes@.take(16)), bytes@[16], bytes@.skip(17)),
    }
))]
pub(super) fn decode_fragment(bytes: &[u8]) -> Option<(u128, u8, &[u8])> {
    let (stream, rest) = take::<16>(bytes)?;
    let (tag, payload) = take::<1>(rest)?;
    let [flags] = tag;
    let stream = decode_u128(stream);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(flags == bytes@[16]);
        assert(payload@ =~= bytes@.skip(17));
    }
    if payload.is_empty()
        || (flags > 3 && !(flags == 4 && stream == 0 && payload.len() == 1 && payload[0] == 0))
    {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        be128_inverse(stream, bytes@.take(16));
        assert(payload@ =~= bytes@.skip(17));
        if flags > 3 { assert(payload@ =~= seq![0u8]); }
        assert(bytes@ =~= fragment_prefix(stream, flags) + payload@);
    }
    Some((stream, flags, payload))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    final(output)@ == old(output)@ + bytes@
))]
pub(super) fn append_bytes(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(bytes);
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    if out {
        final(output)@ == old(output)@ + frame_bytes(fragment_prefix(stream, flags) + payload@)
            && payload@.len() + FRAGMENT_PREFIX_BYTES <= u32::MAX
    } else {
        final(output)@ == old(output)@ && payload@.len() + FRAGMENT_PREFIX_BYTES > u32::MAX
    }
))]
pub(super) fn encode_fragment(
    output: &mut Vec<u8>,
    stream: u128,
    flags: u8,
    payload: &[u8],
) -> bool {
    let prefix = encode_fragment_prefix(stream, flags);
    let Some(header) = encode_frame(&prefix, payload) else {
        return false;
    };
    append_bytes(output, &header);
    append_bytes(output, &prefix);
    append_bytes(output, payload);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~= old(output)@ + frame_bytes(fragment_prefix(stream, flags) + payload@));
    }
    true
}

/// Decode one frame prefix and leave subsequent frames untouched.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((body, rest)) => accepts_frame(bytes@.take(8 + body@.len() as int), body@, max as int)
            && bytes@ == frame_bytes(body@) + rest@
            && frame_decode_wire(
                bytes@.take(8 + body@.len() as int), body@,
                read_be32(bytes@.take(4)) as nat,
                read_be32(bytes@.subrange(4, 8)), crc32(body@), max as nat,
            ),
        None => bytes@.len() < 8 || {
            let len = read_be32(bytes@.take(4)) as int;
            len > max || 8 + len > bytes@.len()
                || read_be32(bytes@.subrange(4, 8)) != crc32(bytes@.subrange(8, 8 + len))
        },
    }
))]
pub(super) fn decode_frame(bytes: &[u8], max: usize) -> Option<(&[u8], &[u8])> {
    let (header, contents) = bytes.split_at_checked(FRAME_HEADER_BYTES)?;
    let (len, crc) = decode_frame_header(header, bytes.len() as u64, max)?;
    let (body, rest) = contents.split_at_checked(len as usize)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        be32_inverse(len, bytes@.take(4));
        be32_inverse(crc, bytes@.subrange(4, 8));
        assert(header@.take(4) =~= bytes@.take(4));
        assert(header@ =~= frame_header_spec(len, crc));
        assert(header@.take(4) =~= be32(len));
        assert(header@.skip(4) =~= be32(crc));
        assert(header@.skip(4) =~= bytes@.subrange(4, 8));
        assert(body@ =~= bytes@.subrange(8, 8 + len as int));
        assert(bytes@ =~= header@ + body@ + rest@);
    }
    if !decode_frame_body(len, crc, body) {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let consumed = bytes@.take(8 + body@.len() as int);
        assert(consumed =~= frame_bytes(body@));
        assert(bytes@ =~= frame_bytes(body@) + rest@);
        assert(consumed.skip(8) =~= body@);
        assert(read_be32(bytes@.take(4)) == len);
        assert(read_be32(bytes@.subrange(4, 8)) == crc);
    }
    Some((body, rest))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((field, rest)) => field@.len() <= u32::MAX
            && bytes@ == be32(field@.len() as u32) + field@ + rest@,
        None => bytes@.len() < 4
            || 4 + read_be32(bytes@.take(4)) as int > bytes@.len(),
    }
))]
pub(super) fn decode_field(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let (count, rest) = take::<4>(bytes)?;
    let len = decode_u32(count);
    let (field, rest) = rest.split_at_checked(len as usize)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        be32_inverse(len, count@);
        assert(bytes@ =~= be32(len) + field@ + rest@);
    }
    Some((field, rest))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    if out {
        bytes@.len() <= u32::MAX && final(output)@ == old(output)@ + be32(bytes@.len() as u32) + bytes@
    } else {
        bytes@.len() > u32::MAX && final(output)@ == old(output)@
    }
))]
pub(super) fn encode_field(output: &mut Vec<u8>, bytes: &[u8]) -> bool {
    let Some(len) = stored_length(bytes.len()) else {
        return false;
    };
    append_bytes(output, &encode_u32(len));
    append_bytes(output, bytes);
    true
}

/// The request and identity bytes remain opaque to the storage format.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some(bytes) => identity@.len() <= u32::MAX
            && bytes@ == be32(identity@.len() as u32) + identity@ + request@,
        None => identity@.len() > u32::MAX,
    }
))]
pub(super) fn encode_entry(identity: &[u8], request: &[u8]) -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    if !encode_field(&mut bytes, identity) {
        return None;
    }
    append_bytes(&mut bytes, request);
    Some(bytes)
}
