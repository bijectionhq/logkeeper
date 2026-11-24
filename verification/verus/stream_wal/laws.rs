use super::wal_layout::{extent_fits, frame_body_fits, place_extent};
use vstd::prelude::*;

verus! {

fn frame_never_reads_past_segment(remaining: u64, len: u32, max: usize) {
    let fits = frame_body_fits(remaining, len, max);
    assert(fits ==> len as int <= max as int && 8 + len as int <= remaining as int);
}

fn extent_stays_in_its_pack(
    seq: u64, next: u64, offset: u64, len: u32, max: usize, size: u64,
) {
    let fits = extent_fits(seq, next, offset, len, max, size);
    assert(fits ==> seq <= next && len as int <= max as int
        && offset as int + len as int <= size as int);
}

fn new_extents_are_adjacent(offset: u64, first: usize, second: usize) {
    if let Some((written, next)) = place_extent(offset, first) {
        if let Some((following, end)) = place_extent(next, second) {
            assert(written as int == first as int);
            assert(following as int == second as int);
            assert(next as int == offset as int + first as int);
            assert(end as int == offset as int + first as int + second as int);
        }
    }
}

}

use super::{checkpoint_bytes::*, wal_bytes::*};

verus! {

proof fn frame_head(bytes: Seq<u8>, body: Seq<u8>, crc: u32)
    requires body.len() <= u32::MAX,
        bytes == frame_header_spec(body.len() as u32, crc) + body,
    ensures
        bytes.len() == 8 + body.len(),
        read_be32(bytes.take(4)) as int == body.len(),
        read_be32(bytes.subrange(4, 8)) == crc,
        bytes.skip(8) == body,
{
    be32_inverse(body.len() as u32, bytes.take(4));
    be32_inverse(crc, bytes.subrange(4, 8));
    assert(bytes.take(4) =~= be32(body.len() as u32));
    assert(bytes.subrange(4, 8) =~= be32(crc));
    assert(bytes.skip(8) =~= body);
}

fn frame_decodes_its_encoding<'a>(bytes: &'a [u8], body: &[u8], max: usize) -> (payload: &'a [u8])
    requires accepts_frame(bytes@, body@, max as int),
    ensures payload@ == body@,
{
    proof { frame_head(bytes@, body@, crc32(body@)); }
    let decoded = decode_frame(bytes, max);
    assert(decoded matches Some((payload, rest)) && payload@ == body@ && rest@.len() == 0) by {
        match decoded {
            Some((payload, rest)) => {
                frame_head(frame_bytes(payload@), payload@, crc32(payload@));
                assert(bytes@.take(4) =~= frame_bytes(payload@).take(4));
                assert(payload@.len() == body@.len());
                assert(bytes@.skip(8) =~= payload@ + rest@);
            },
            None => {
                assert(bytes@.subrange(8, bytes@.len() as int) =~= body@);
            },
        }
    }
    decoded.unwrap().0
}

fn accepted_frame_reencodes_exactly(bytes: &[u8], max: usize) {
    if let Some((body, rest)) = decode_frame(bytes, max) {
        let header = encode_frame(&[], body);
        assert(header matches Some(header) && bytes@ == header@ + body@ + rest@);
    }
}

fn every_frame_truncation_is_rejected(bytes: &[u8], body: &[u8], cut: usize, max: usize)
    requires accepts_frame(bytes@, body@, max as int), cut < bytes.len(),
{
    let (prefix, _) = bytes.split_at(cut);
    let decoded = decode_frame(prefix, max);
    assert(decoded is None) by {
        frame_head(bytes@, body@, crc32(body@));
        if let Some((payload, _)) = decoded {
            frame_head(frame_bytes(payload@), payload@, crc32(payload@));
            assert(prefix@.take(4) =~= bytes@.take(4));
            assert(prefix@.take(4) =~= frame_bytes(payload@).take(4));
        }
    }
}

fn corrupted_frame_crc_is_rejected(bytes: &[u8], body: &[u8], crc: u32, max: usize)
    requires body@.len() <= u32::MAX,
        bytes@ == frame_header_spec(body@.len() as u32, crc) + body@,
        crc != crc32(body@),
{
    let decoded = decode_frame(bytes, max);
    assert(decoded is None) by {
        frame_head(bytes@, body@, crc);
        if let Some((payload, rest)) = decoded {
            frame_head(frame_bytes(payload@), payload@, crc32(payload@));
            assert(bytes@.take(4) =~= frame_bytes(payload@).take(4));
            assert(bytes@.subrange(4, 8) =~= frame_bytes(payload@).subrange(4, 8));
            assert(bytes@.skip(8) =~= payload@ + rest@);
        }
    }
}

fn pack_write_read_correspondence(
    pack: &[u8], previously_written: &[u8], payload: &[u8], later_writes: &[u8],
)
    requires pack@ == previously_written@ + payload@ + later_writes@,
        payload@.len() <= u32::MAX,
{
    let offset = previously_written.len();
    let description = describe_extent(offset as u64, payload);
    assert(description is Some);
    let (begin, end, len, crc) = description.unwrap();
    let (_, suffix) = pack.split_at(begin as usize);
    let (read, _) = suffix.split_at(len as usize);
    assert(read@ =~= pack@.subrange(offset as int, end as int));
    assert(read@ =~= payload@);
    let accepted = check_extent(crc, read);
    assert(accepted);
}

fn corrupted_extent_crc_is_rejected(payload: &[u8], crc: u32)
    requires crc != crc32(payload@),
{
    let accepted = check_extent(crc, payload);
    assert(!accepted);
}

fn accepted_stream_index_reencodes_exactly(bytes: &[u8]) {
    #[verus_spec(with Ghost(None))]
    let decoded = decode_stream_index(bytes);
    if let Some(index) = decoded {
        let encoded = encode_stream_index(index);
        assert(encoded matches Some(row) && row@ == bytes@);
    }
}

fn stream_index_decodes_its_encoding(index: StreamIndex)
    requires valid_stream_index(index),
{
    let bytes = encode_stream_index(index).unwrap();
    #[verus_spec(with Ghost(Some(index)))]
    let decoded = decode_stream_index(&bytes);
    assert(decoded matches Some(actual) && same_index(actual, index));
}

proof fn index_header_fields(bytes: Seq<u8>, next: u64, count: u32)
    requires bytes == index_header(next, count),
    ensures bytes.len() == 24, bytes.take(8) == INDEX_MAGIC@,
        bytes.subrange(8, 20) == index_fields(next, count),
        read_be64(bytes.subrange(8, 16)) == next,
        read_be32(bytes.subrange(16, 20)) == count,
        read_be32(bytes.skip(20)) == crc32(index_fields(next, count)),
{
    be64_inverse(next, bytes.subrange(8, 16));
    be32_inverse(count, bytes.subrange(16, 20));
    let crc = crc32(index_fields(next, count));
    be32_inverse(crc, bytes.skip(20));
    assert(bytes.take(8) =~= INDEX_MAGIC@);
    assert(bytes.subrange(8, 20) =~= index_fields(next, count));
    assert(bytes.subrange(8, 16) =~= be64(next));
    assert(bytes.subrange(16, 20) =~= be32(count));
    assert(bytes.skip(20) =~= be32(crc));
}

fn index_header_round_trip(next: u64, count: u32) {
    let bytes = encode_index_header(next, count);
    proof { index_header_fields(bytes@, next, count); }
    let decoded = decode_index_header(&bytes);
    assert(decoded is Some);
    let (n, c) = decoded.unwrap();
    proof { index_header_fields(bytes@, n, c); }
    assert(n == next);
    assert(c == count);
}

fn accepted_index_header_reencodes_exactly(bytes: &[u8]) {
    if let Some((next, count)) = decode_index_header(bytes) {
        let encoded = encode_index_header(next, count);
        assert(encoded@ == bytes@);
    }
}

fn every_index_header_truncation_is_rejected(next: u64, count: u32, cut: usize)
    requires cut < 24,
{
    let bytes = encode_index_header(next, count);
    proof { index_header_fields(bytes@, next, count); }
    let input: &[u8] = &bytes;
    let (prefix, _) = input.split_at(cut);
    let decoded = decode_index_header(prefix);
    assert(decoded is None) by {
        assert(prefix@.len() == cut);
        if let Some((n, c)) = decoded {
            index_header_fields(prefix@, n, c);
        }
    }
}

fn corrupted_index_header_crc_is_rejected(bytes: &[u8], next: u64, count: u32, crc: u32)
    requires bytes@ == INDEX_MAGIC@ + index_fields(next, count) + be32(crc),
        crc != crc32(index_fields(next, count)),
{
    let decoded = decode_index_header(bytes);
    assert(decoded is None) by {
        if let Some((n, c)) = decoded {
            index_header_fields(bytes@, n, c);
            be32_inverse(crc, bytes@.skip(20));
            assert(bytes@.skip(20) =~= be32(crc));
            assert(bytes@.subrange(8, 20) =~= index_fields(next, count));
        }
    }
}

proof fn extent_fields(bytes: Seq<u8>, epoch: u64, location: Location)
    requires bytes == extent_bytes(epoch, location),
    ensures bytes.len() == 32,
        read_be64(bytes.take(8)) == epoch,
        read_be64(bytes.subrange(8, 16)) == location.seq,
        read_be64(bytes.subrange(16, 24)) == location.offset,
        read_be32(bytes.subrange(24, 28)) == location.len,
        read_be32(bytes.skip(28)) == location.crc,
{
    be64_inverse(epoch, bytes.take(8));
    be64_inverse(location.seq, bytes.subrange(8, 16));
    be64_inverse(location.offset, bytes.subrange(16, 24));
    be32_inverse(location.len, bytes.subrange(24, 28));
    be32_inverse(location.crc, bytes.skip(28));
    assert(bytes.take(8) =~= be64(epoch));
    assert(bytes.subrange(8, 16) =~= be64(location.seq));
    assert(bytes.subrange(16, 24) =~= be64(location.offset));
    assert(bytes.subrange(24, 28) =~= be32(location.len));
    assert(bytes.skip(28) =~= be32(location.crc));
    assert(bytes.len() == 32);
}

fn extent_round_trip(epoch: u64, location: Location) {
    let bytes = encode_extent(epoch, location);
    let result = decode_extent(&bytes);
    assert(result matches Some((read_epoch, read_location, rest))
        && read_epoch == epoch && read_location == location && rest@.len() == 0) by {
        extent_fields(bytes@, epoch, location);
        if let Some((e, l, rest)) = result {
            extent_fields(extent_bytes(e, l), e, l);
            assert(bytes@.take(32) =~= extent_bytes(e, l));
            assert(bytes@.take(32) =~= bytes@);
        }
    }
}

fn accepted_extent_reencodes_exactly(bytes: &[u8]) {
    if let Some((epoch, location, rest)) = decode_extent(bytes) {
        let encoded = encode_extent(epoch, location);
        assert(encoded@ + rest@ == bytes@);
    }
}

fn wal_entry_round_trip(identity: &[u8], request: &[u8])
    requires identity@.len() <= u32::MAX,
{
    let encoded = encode_entry(identity, request).unwrap();
    let result = decode_field(&encoded);
    assert(result matches Some((id, body)) && id@ == identity@ && body@ == request@) by {
        prefixed_field(encoded@, identity@, request@);
        if let Some((id, body)) = result {
            prefixed_field(encoded@, id@, body@);
            assert(id@.len() == identity@.len());
        }
    }
}

fn accepted_wal_entry_reencodes_exactly(bytes: &[u8]) {
    if let Some((id, request)) = decode_field(bytes) {
        let encoded = encode_entry(id, request).unwrap();
        assert(encoded@ == bytes@);
    }
}

fn fragment_round_trip(stream: u128, flags: u8, payload: &[u8], slice: &[u8])
    requires fragment_valid(stream, flags, payload@),
        slice@ == fragment_prefix(stream, flags) + payload@,
{
    let decoded = decode_fragment(slice);
    assert(decoded matches Some((s, f, bytes)) && s == stream && f == flags && bytes@ == payload@) by {
        be128_inverse(stream, slice@.take(16));
        assert(payload@.len() > 0);
        assert(slice@.len() == 17 + payload@.len());
        assert(slice@.take(16) =~= be128(stream));
        assert(slice@[16] == flags);
        assert(slice@.skip(17) =~= payload@);
        if let Some((s, f, bytes)) = decoded {
            be128_inverse(s, slice@.take(16));
            assert(slice@.take(16) =~= be128(s));
            assert(slice@[16] == f);
            assert(slice@.skip(17) =~= bytes@);
        }
    }
}

fn accepted_fragment_reencodes_exactly(body: &[u8]) {
    if let Some((stream, flags, payload)) = decode_fragment(body) {
        let prefix = encode_fragment_prefix(stream, flags);
        assert(body@ == prefix@ + payload@);
    }
}

fn framed_checkpoint_row_round_trip(index: StreamIndex, max: usize)
    requires valid_stream_index(index),
        stream_index(index).len() <= max,
        stream_index(index).len() <= u32::MAX,
{
    let row = encode_stream_index(index).unwrap();
    let header = encode_frame(&[], &row).unwrap();
    let mut written = Vec::new();
    append_bytes(&mut written, &header);
    append_bytes(&mut written, &row);
    assert(accepts_frame(written@, row@, max as int));
    let payload = frame_decodes_its_encoding(&written, &row, max);
    #[verus_spec(with Ghost(Some(index)))]
    let decoded = decode_stream_index(payload);
    assert(decoded matches Some(actual) && same_index(actual, index));
}

}
