//! Checkpoint header, stream index, and extent codecs. The index carries
//! per-record locations and keeps the protobuf view byte-for-byte.

use super::{
    wal_bytes::{
        append_bytes, checksum, decode_field, decode_u32, decode_u64, decode_u128, encode_field,
        encode_u32, encode_u64, encode_u128, take,
    },
    wal_layout::{checksum_matches, place_extent, stored_length},
};

#[cfg(verus_keep_ghost)]
use super::wal_bytes::{
    be32, be32_inverse, be64, be64_inverse, be128, be128_inverse, crc32, read_be32,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) const INDEX_HEADER_BYTES: usize = 24;
pub(super) const EXTENT_BYTES: usize = 32;
pub(super) const INDEX_MAGIC: [u8; 8] = *b"LKPACK01";

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn index_fields(next: u64, count: u32) -> Seq<u8> {
    be64(next) + be32(count)
}

pub(super) open spec fn index_wire(
    magic: Seq<u8>, next: Seq<u8>, count: Seq<u8>,
    word: spec_fn(u32) -> Seq<u8>, crc: spec_fn(Seq<u8>) -> u32,
) -> Seq<u8> {
    magic + next + count + word(crc(next + count))
}

pub(super) open spec fn index_header(next: u64, count: u32) -> Seq<u8> {
    index_wire(INDEX_MAGIC@, be64(next), be32(count), |value| be32(value), |bytes| crc32(bytes))
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == index_fields(next, count)))]
fn encode_index_fields(next: u64, count: u32) -> [u8; 12] {
    let [a, b, c, d, e, f, g, h] = encode_u64(next);
    let [i, j, k, l] = encode_u32(count);
    let fields = [a, b, c, d, e, f, g, h, i, j, k, l];
    #[cfg(verus_keep_ghost)]
    proof! { assert(fields@ =~= index_fields(next, count)); }
    fields
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == index_header(next, count)))]
pub(super) fn encode_index_header(next: u64, count: u32) -> [u8; INDEX_HEADER_BYTES] {
    let fields = encode_index_fields(next, count);
    let [a, b, c, d, e, f, g, h, i, j, k, l] = fields;
    let [m, n, o, p] = encode_u32(checksum(&[], &fields));
    let [s, t, u, v, w, x, y, z] = INDEX_MAGIC;
    let header = [
        s, t, u, v, w, x, y, z, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
    ];
    #[cfg(verus_keep_ghost)]
    proof! { assert(header@ =~= index_header(next, count)); }
    header
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((next, count)) => bytes@ == index_header(next, count),
        None => bytes@.len() != 24 || bytes@.take(8) != INDEX_MAGIC@
            || read_be32(bytes@.skip(20)) != crc32(bytes@.subrange(8, 20)),
    }
))]
pub(super) fn decode_index_header(bytes: &[u8]) -> Option<(u64, u32)> {
    let (magic, rest) = take::<8>(bytes)?;
    let (fields, rest) = take::<12>(rest)?;
    let (crc, rest) = take::<4>(rest)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if rest@.len() == 0 {
            assert(crc@ =~= bytes@.skip(20));
            assert(fields@ =~= bytes@.subrange(8, 20));
        }
    }
    if !rest.is_empty()
        || magic != INDEX_MAGIC
        || !checksum_matches(decode_u32(crc), checksum(&[], &fields))
    {
        return None;
    }
    let (next, rest) = take::<8>(&fields)?;
    let (count, _) = take::<4>(rest)?;
    let next = decode_u64(next);
    let count = decode_u32(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        be64_inverse(next, fields@.take(8));
        be32_inverse(count, fields@.skip(8));
        be32_inverse(read_be32(crc@), crc@);
        assert(fields@ =~= index_fields(next, count));
        assert(bytes@ =~= index_header(next, count));
    }
    Some((next, count))
}

#[derive(Clone, Copy)]
pub(super) struct Location {
    pub seq: u64,
    pub offset: u64,
    pub len: u32,
    pub crc: u32,
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn extent_wire(
    epoch: Seq<u8>, sequence: Seq<u8>, offset: Seq<u8>, length: Seq<u8>, crc: Seq<u8>,
) -> Seq<u8> {
    epoch + sequence + offset + length + crc
}

pub(super) open spec fn extent_bytes(epoch: u64, location: Location) -> Seq<u8> {
    extent_wire(be64(epoch), be64(location.seq), be64(location.offset),
        be32(location.len), be32(location.crc))
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ == extent_bytes(epoch, location)))]
pub(super) fn encode_extent(epoch: u64, location: Location) -> [u8; EXTENT_BYTES] {
    let [a, b, c, d, e, f, g, h] = encode_u64(epoch);
    let [i, j, k, l, m, n, o, p] = encode_u64(location.seq);
    let [q, r, s, t, u, v, w, x] = encode_u64(location.offset);
    let [y, z, aa, ab] = encode_u32(location.len);
    let [ac, ad, ae, af] = encode_u32(location.crc);
    let row = [
        a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac,
        ad, ae, af,
    ];
    #[cfg(verus_keep_ghost)]
    proof! { assert(row@ =~= extent_bytes(epoch, location)); }
    row
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((epoch, location, rest)) => bytes@ == extent_bytes(epoch, location) + rest@,
        None => bytes@.len() < 32,
    }
))]
pub(super) fn decode_extent(bytes: &[u8]) -> Option<(u64, Location, &[u8])> {
    let (epoch, rest) = take::<8>(bytes)?;
    let (seq, rest) = take::<8>(rest)?;
    let (offset, rest) = take::<8>(rest)?;
    let (len, rest) = take::<4>(rest)?;
    let (crc, rest) = take::<4>(rest)?;
    let epoch = decode_u64(epoch);
    let location = Location {
        seq: decode_u64(seq),
        offset: decode_u64(offset),
        len: decode_u32(len),
        crc: decode_u32(crc),
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        be64_inverse(epoch, bytes@.take(8));
        be64_inverse(location.seq, bytes@.subrange(8, 16));
        be64_inverse(location.offset, bytes@.subrange(16, 24));
        be32_inverse(location.len, bytes@.subrange(24, 28));
        be32_inverse(location.crc, bytes@.subrange(28, 32));
        assert(rest@ =~= bytes@.skip(32));
        assert(bytes@ =~= extent_bytes(epoch, location) + rest@);
    }
    Some((epoch, location, rest))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((begin, end, len, crc)) =>
            begin == offset && len as int == payload@.len()
                && end as int == offset as int + payload@.len() && crc == crc32(payload@),
        None => payload@.len() > u32::MAX || offset as int + payload@.len() > u64::MAX,
    }
))]
pub(super) fn describe_extent(offset: u64, payload: &[u8]) -> Option<(u64, u64, u32, u32)> {
    let (len, end) = place_extent(offset, payload.len())?;
    Some((offset, end, len, checksum(&[], payload)))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (crc == crc32(payload@))))]
pub(super) fn check_extent(crc: u32, payload: &[u8]) -> bool {
    checksum_matches(crc, checksum(&[], payload))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == (flag == 0 || flag == 1)
))]
fn valid_flag(flag: u8) -> bool {
    flag <= 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == if flag { 1u8 } else { 0u8 }
))]
fn encode_flag(flag: bool) -> u8 {
    if flag { 1 } else { 0 }
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn extent_table(rows: Seq<u8>) -> Seq<u8> {
    be32((rows.len() / 32) as u32) + rows
}

pub(super) open spec fn valid_extent_table(rows: Seq<u8>) -> bool {
    rows.len() % 32 == 0 && rows.len() / 32 <= u32::MAX
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some((rows, rest)) => valid_extent_table(rows@) && bytes@ == extent_table(rows@) + rest@,
        None => bytes@.len() < 4
            || 4 + 32 * read_be32(bytes@.take(4)) as int > bytes@.len(),
    }
))]
fn decode_extent_table(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let (count, rest) = take::<4>(bytes)?;
    let count = decode_u32(count) as usize;
    if count > rest.len() / EXTENT_BYTES {
        return None;
    }
    let len = count * EXTENT_BYTES;
    let (rows, rest) = rest.split_at_checked(len)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        be32_inverse(count as u32, bytes@.take(4));
        assert(rows@.len() / 32 == count as int) by (nonlinear_arith)
            requires rows@.len() == count as int * 32;
        assert(rows@.len() % 32 == 0) by (nonlinear_arith)
            requires rows@.len() == count as int * 32;
        assert(bytes@ =~= extent_table(rows@) + rest@);
    }
    Some((rows, rest))
}

#[derive(Clone, Copy)]
pub(super) struct StagedIndex<'a> {
    pub from: u64,
    pub floor: u64,
    pub rows: &'a [u8],
}

#[derive(Clone, Copy)]
pub(super) struct StreamIndex<'a> {
    pub stream: u128,
    pub deleted: bool,
    pub view: &'a [u8],
    pub retained: &'a [u8],
    pub staged: Option<StagedIndex<'a>>,
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn staged_index_prefix(stage: Option<(u64, u64, u32)>) -> Seq<u8> {
    match stage {
        None => seq![0u8],
        Some((from, floor, count)) => seq![1u8] + be64(from) + be64(floor) + be32(count),
    }
}

pub(super) open spec fn staged_index(stage: Option<StagedIndex>) -> Seq<u8> {
    match stage {
        None => seq![0u8],
        Some(s) => seq![1u8] + be64(s.from) + be64(s.floor) + extent_table(s.rows@),
    }
}

pub(super) open spec fn stream_index_wire(
    stream: Seq<u8>, deleted: u8, view_length: Seq<u8>, view: Seq<u8>,
    retained: Seq<u8>, staged: Seq<u8>,
) -> Seq<u8> {
    stream + seq![deleted] + view_length + view + retained + staged
}

pub(super) open spec fn stream_index(index: StreamIndex) -> Seq<u8> {
    stream_index_wire(be128(index.stream), if index.deleted { 1u8 } else { 0u8 },
        be32(index.view@.len() as u32), index.view@, extent_table(index.retained@),
        staged_index(index.staged))
}

pub(super) open spec fn valid_stream_index(index: StreamIndex) -> bool {
    index.view@.len() <= u32::MAX && valid_extent_table(index.retained@)
        && match index.staged {
            None => true,
            Some(s) => s.from != 0 && valid_extent_table(s.rows@),
        }
}

}

/// Size the body before writing any extents. INDEX uses a u32 frame length.
pub(super) fn stream_index_len(view: usize, retained: u32, staged: Option<u32>) -> Option<usize> {
    // Stream ID, deleted flag, view length, retained count, and staging flag.
    const STREAM_FIELDS: usize = 16 + 1 + 4 + 4 + 1;
    // Staging start, floor, and extent count.
    const STAGED_FIELDS: usize = 8 + 8 + 4;

    let retained_bytes = (retained as usize).checked_mul(EXTENT_BYTES)?;
    let mut len = STREAM_FIELDS.checked_add(view)?.checked_add(retained_bytes)?;
    if let Some(count) = staged {
        let staged_bytes = (count as usize).checked_mul(EXTENT_BYTES)?;
        len = len.checked_add(STAGED_FIELDS)?.checked_add(staged_bytes)?;
    }
    stored_length(len)?;
    Some(len)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    if out {
        view@.len() <= u32::MAX && final(output)@ == old(output)@ + stream_index_wire(
            be128(stream), if deleted { 1u8 } else { 0u8 }, be32(view@.len() as u32),
            view@, be32(retained), Seq::empty())
    } else {
        view@.len() > u32::MAX
    }
))]
pub(super) fn encode_stream_index_prefix(
    output: &mut Vec<u8>,
    stream: u128,
    deleted: bool,
    view: &[u8],
    retained: u32,
) -> bool {
    append_bytes(output, &encode_u128(stream));
    append_bytes(output, &[encode_flag(deleted)]);
    if !encode_field(output, view) {
        return false;
    }
    append_bytes(output, &encode_u32(retained));
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~= old(output)@ + stream_index_wire(
            be128(stream), if deleted { 1u8 } else { 0u8 }, be32(view@.len() as u32),
            view@, be32(retained), Seq::empty()));
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    final(output)@ == old(output)@ + staged_index_prefix(stage)
))]
pub(super) fn encode_staged_index_prefix(output: &mut Vec<u8>, stage: Option<(u64, u64, u32)>) {
    append_bytes(output, &[encode_flag(stage.is_some())]);
    if let Some((from, floor, count)) = stage {
        append_bytes(output, &encode_u64(from));
        append_bytes(output, &encode_u64(floor));
        append_bytes(output, &encode_u32(count));
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= old(output)@ + staged_index_prefix(stage)); }
}

#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == if valid_extent_table(rows@) { Some((rows@.len() / 32) as u32) } else { None }
))]
fn extent_count(rows: &[u8]) -> Option<u32> {
    if rows.len() % EXTENT_BYTES != 0 {
        return None;
    }
    stored_length(rows.len() / EXTENT_BYTES)
}

/// Compose the production prefixes and encoded extents for the byte laws.
#[cfg(verus_keep_ghost)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    match out {
        Some(bytes) => valid_stream_index(index) && bytes@ == stream_index(index),
        None => !valid_stream_index(index),
    }
))]
pub(super) fn encode_stream_index(index: StreamIndex<'_>) -> Option<Vec<u8>> {
    let retained = extent_count(index.retained)?;
    let staged = match index.staged {
        Some(stage) => {
            if stage.from == 0 {
                return None;
            }
            Some((stage.from, stage.floor, extent_count(stage.rows)?))
        }
        None => None,
    };
    let mut output = Vec::new();
    if !encode_stream_index_prefix(&mut output, index.stream, index.deleted, index.view, retained) {
        return None;
    }
    append_bytes(&mut output, index.retained);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost prefix = output@; }
    encode_staged_index_prefix(&mut output, staged);
    if let Some(stage) = index.staged {
        append_bytes(&mut output, stage.rows);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(prefix =~= stream_index_prefix(index));
        assert(output@ =~= prefix + staged_index(index.staged));
        assert(output@ =~= stream_index(index));
    }
    Some(output)
}

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn same_stage(a: StagedIndex, b: StagedIndex) -> bool {
    a.from == b.from && a.floor == b.floor && a.rows@ == b.rows@
}

pub(super) open spec fn same_prefix(a: StreamIndex, b: StreamIndex) -> bool {
    a.stream == b.stream && a.deleted == b.deleted && a.view@ == b.view@ && a.retained@ == b.retained@
}

pub(super) open spec fn same_index(a: StreamIndex, b: StreamIndex) -> bool {
    same_prefix(a, b) && match (a.staged, b.staged) {
            (None, None) => true,
            (Some(x), Some(y)) => same_stage(x, y),
            _ => false,
        }
}

pub(super) open spec fn stream_index_prefix(index: StreamIndex) -> Seq<u8> {
    be128(index.stream) + seq![if index.deleted { 1u8 } else { 0u8 }]
        + be32(index.view@.len() as u32) + index.view@ + extent_table(index.retained@)
}

pub(super) proof fn prefixed_field(bytes: Seq<u8>, field: Seq<u8>, rest: Seq<u8>)
    requires field.len() <= u32::MAX, bytes == be32(field.len() as u32) + field + rest,
    ensures bytes.len() >= 4 + field.len(),
        read_be32(bytes.take(4)) as int == field.len(),
        bytes.subrange(4, 4 + field.len() as int) == field,
        bytes.skip(4 + field.len() as int) == rest,
{
    assert(bytes.take(4) =~= be32(field.len() as u32));
    be32_inverse(field.len() as u32, bytes.take(4));
    assert(bytes.subrange(4, 4 + field.len() as int) =~= field);
    assert(bytes.skip(4 + field.len() as int) =~= rest);
}

proof fn prefixed_table(bytes: Seq<u8>, rows: Seq<u8>, rest: Seq<u8>)
    requires valid_extent_table(rows), bytes == extent_table(rows) + rest,
    ensures bytes.len() >= 4 + rows.len(),
        32 * read_be32(bytes.take(4)) as int == rows.len(),
        bytes.subrange(4, 4 + rows.len() as int) == rows,
        bytes.skip(4 + rows.len() as int) == rest,
{
    let count = (rows.len() / 32) as u32;
    assert(bytes.take(4) =~= be32(count));
    be32_inverse(count, bytes.take(4));
    assert(32 * count as int == rows.len()) by (nonlinear_arith)
        requires rows.len() / 32 == count as int, rows.len() % 32 == 0;
    assert(bytes.subrange(4, 4 + rows.len() as int) =~= rows);
    assert(bytes.skip(4 + rows.len() as int) =~= rest);
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(expected): Ghost<Option<StagedIndex<'_>>>, Ghost(suffix): Ghost<Seq<u8>>
    requires expected matches Some(s) ==> s.from != 0 && valid_extent_table(s.rows@)
        && bytes@ == be64(s.from) + be64(s.floor) + extent_table(s.rows@) + suffix,
    ensures
        out matches Some((stage, rest)) ==> stage.from != 0 && valid_extent_table(stage.rows@)
            && bytes@ == be64(stage.from) + be64(stage.floor) + extent_table(stage.rows@) + rest@,
        expected matches Some(s) ==> out matches Some((stage, rest))
            && same_stage(stage, s) && rest@ == suffix,
))]
fn decode_staged_index<'a>(bytes: &'a [u8]) -> Option<(StagedIndex<'a>, &'a [u8])> {
    #[cfg(verus_keep_ghost)]
    proof! {
        if expected.is_some() { assert(bytes@.len() >= 16); }
    }
    let (from_bytes, after_from) = take::<8>(bytes)?;
    let (floor_bytes, after_floor) = take::<8>(after_from)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(s) = expected {
            assert(from_bytes@ =~= be64(s.from));
            assert(floor_bytes@ =~= be64(s.floor));
            assert(after_floor@ =~= extent_table(s.rows@) + suffix);
            prefixed_table(after_floor@, s.rows@, suffix);
            be64_inverse(s.from, from_bytes@);
            be64_inverse(s.floor, floor_bytes@);
        }
    }
    let (rows, rest) = decode_extent_table(after_floor)?;
    let from = decode_u64(from_bytes);
    if from == 0 {
        return None;
    }
    let floor = decode_u64(floor_bytes);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(s) = expected {
            prefixed_table(after_floor@, rows@, rest@);
            assert(rows@ == s.rows@);
        }
        be64_inverse(from, from_bytes@);
        be64_inverse(floor, floor_bytes@);
        assert(bytes@ =~= from_bytes@ + after_from@);
        assert(after_from@ =~= floor_bytes@ + after_floor@);
        assert(after_from@ =~= be64(floor) + extent_table(rows@) + rest@);
        assert(bytes@ =~= be64(from) + be64(floor) + extent_table(rows@) + rest@);
    }
    Some((StagedIndex { from, floor, rows }, rest))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(expected): Ghost<Option<StreamIndex<'_>>>
    requires expected matches Some(index) ==> valid_stream_index(index)
        && bytes@ == stream_index(index),
    ensures
        out matches Some((index, rest)) ==> valid_stream_index(index) && index.staged is None
            && bytes@ == stream_index_prefix(index) + rest@,
        expected matches Some(index) ==> out matches Some((actual, rest))
            && same_prefix(actual, index) && rest@ == staged_index(index.staged),
))]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(80))]
fn decode_index_prefix<'a>(bytes: &'a [u8]) -> Option<(StreamIndex<'a>, &'a [u8])> {
    #[cfg(verus_keep_ghost)]
    proof! {
        if expected.is_some() { assert(bytes@.len() >= 17); }
    }
    let (stream_bytes, after_stream) = take::<16>(bytes)?;
    let (deleted_bytes, after_deleted) = take::<1>(after_stream)?;
    let [deleted] = deleted_bytes;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(i) = expected {
            assert(stream_bytes@ =~= be128(i.stream));
            assert(deleted == if i.deleted { 1u8 } else { 0u8 });
            be128_inverse(i.stream, stream_bytes@);
            assert(after_deleted@ =~= be32(i.view@.len() as u32) + i.view@
                + (extent_table(i.retained@) + staged_index(i.staged)));
            prefixed_field(after_deleted@, i.view@, extent_table(i.retained@) + staged_index(i.staged));
        }
    }
    if !valid_flag(deleted) {
        return None;
    }
    let (view, after_view) = decode_field(after_deleted)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(i) = expected {
            prefixed_field(after_deleted@, view@, after_view@);
            assert(view@ == i.view@);
            prefixed_table(after_view@, i.retained@, staged_index(i.staged));
        }
    }
    let (retained, rest) = decode_extent_table(after_view)?;
    let stream = decode_u128(stream_bytes);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(i) = expected {
            prefixed_table(after_view@, retained@, rest@);
            assert(retained@ == i.retained@);
            assert(rest@ == staged_index(i.staged));
        }
        be128_inverse(stream, stream_bytes@);
        assert(deleted_bytes@ =~= seq![deleted]);
        assert(bytes@ =~= stream_bytes@ + after_stream@);
        assert(after_stream@ =~= deleted_bytes@ + after_deleted@);
        assert(after_deleted@ =~= be32(view@.len() as u32) + view@ + extent_table(retained@) + rest@);
        assert(bytes@ =~= be128(stream) + seq![deleted]
            + be32(view@.len() as u32) + view@ + extent_table(retained@) + rest@);
    }
    let index = StreamIndex {
        stream,
        deleted: deleted == 1,
        view,
        retained,
        staged: None,
    };
    Some((index, rest))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(expected): Ghost<Option<StreamIndex<'_>>>
    requires expected matches Some(index) ==> valid_stream_index(index)
        && bytes@ == stream_index(index),
    ensures
        out matches Some(index) ==> valid_stream_index(index) && bytes@ == stream_index(index),
        expected matches Some(index) ==> out matches Some(actual) && same_index(actual, index),
))]
pub(super) fn decode_stream_index<'a>(bytes: &'a [u8]) -> Option<StreamIndex<'a>> {
    #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(expected)))]
    let (mut index, after_prefix) = decode_index_prefix(bytes)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected_stage = match expected { Some(i) => i.staged, None => None }; }
    #[cfg(verus_keep_ghost)]
    proof! {
        if expected.is_some() {
            assert(after_prefix@.len() >= 1) by { match expected_stage { None => {}, Some(_) => {} } }
        }
    }
    let (stage_bytes, rest) = take::<1>(after_prefix)?;
    let [stage] = stage_bytes;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(stage_bytes@ =~= seq![stage]);
        assert(after_prefix@ =~= stage_bytes@ + rest@);
        if expected.is_some() {
            match expected_stage {
                None => { assert(stage == 0 && rest@.len() == 0); },
                Some(s) => {
                    assert(stage == 1);
                    assert(rest@ =~= be64(s.from) + be64(s.floor) + extent_table(s.rows@));
                },
            }
        }
    }
    if !valid_flag(stage) {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost tail = rest@; }
    let rest = if stage == 1 {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(expected_stage), Ghost(Seq::empty())))]
        let (staged, rest) = decode_staged_index(rest)?;
        index.staged = Some(staged);
        rest
    } else {
        rest
    };
    if !rest.is_empty() {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(after_prefix@ =~= staged_index(index.staged));
        assert(bytes@ =~= stream_index(index));
    }
    Some(index)
}
