//! The bytes of offloaded objects.
//!
//! A segment object holds a contiguous run of one stream's committed
//! records under one offload lineage:
//!
//! ```text
//! "LKOFF001" | u32 header length | header | frames | SHA-256 of all before
//! frame = u32 length (bit 31 marks a timed record) | u32 CRC-32 | record
//! ```
//!
//! The header names the stream, lineage, first and last LSN, the record
//! count and the writer epochs the uploader knew for the records. A reader
//! checks the trailer, every frame's checksum, and that the header matches
//! the key it fetched, so a damaged or misplaced object is refused.
//!
//! A lineage object (`"LKLIN001"`) records where each lineage of the stream
//! starts, so a restore with no surviving voter can find which objects are
//! authoritative.

use std::io;

use bytes::{Bytes, BytesMut};
use journal_contract::{Epoch, Lsn, StreamId};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::stream::consensus::{MAX_RECORD, decode, encode, invalid, state::TIMED_RECORD};

const SEGMENT_MAGIC: &[u8; 8] = b"LKOFF001";
const LINEAGE_MAGIC: &[u8; 8] = b"LKLIN001";
const TRAILER: usize = 32;
const MAX_HEADER: usize = 1024 * 1024;

/// One committed record as uploaded: its position, its retained bytes
/// (with the evidence prefix of a timed record) and whether it is timed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub lsn: Lsn,
    pub timed: bool,
    pub bytes: Bytes,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SegmentHeader {
    pub stream: StreamId,
    pub lineage: u64,
    pub first: Lsn,
    pub last: Lsn,
    pub records: u32,
    /// Runs of the writer epochs the uploader knew: the first LSN of each
    /// run and its epoch. Records before the first run have no known epoch.
    pub epochs: Vec<(Lsn, Epoch)>,
}

/// A decoded, verified segment object.
#[derive(Clone, Debug)]
pub struct Segment {
    pub header: SegmentHeader,
    pub records: Vec<Record>,
    /// Encoded size, for cache accounting.
    pub size: usize,
}

impl Segment {
    /// The highest writer epoch the header names.
    pub fn max_epoch(&self) -> Epoch {
        self.header
            .epochs
            .iter()
            .map(|(_, epoch)| *epoch)
            .max()
            .unwrap_or(Epoch(0))
    }
}

/// Encodes a run of contiguous records.
pub fn encode_segment(
    stream: StreamId,
    lineage: u64,
    records: &[Record],
    epochs: Vec<(Lsn, Epoch)>,
) -> io::Result<Bytes> {
    let (Some(first), Some(last)) = (records.first(), records.last()) else {
        return Err(invalid("an offloaded segment holds at least one record"));
    };
    if records
        .windows(2)
        .any(|pair| pair[1].lsn.0 != pair[0].lsn.0 + 1)
    {
        return Err(invalid("offloaded records are not contiguous"));
    }
    let header = encode(&SegmentHeader {
        stream,
        lineage,
        first: first.lsn,
        last: last.lsn,
        records: u32::try_from(records.len()).map_err(io::Error::other)?,
        epochs,
    })?;
    let body: usize = records.iter().map(|record| 8 + record.bytes.len()).sum();
    let mut out = BytesMut::with_capacity(12 + header.len() + body + TRAILER);
    out.extend_from_slice(SEGMENT_MAGIC);
    out.extend_from_slice(&(header.len() as u32).to_be_bytes());
    out.extend_from_slice(&header);
    for record in records {
        if record.bytes.len() > MAX_RECORD {
            return Err(invalid("offloaded record exceeds the record bound"));
        }
        let len = record.bytes.len() as u32 | if record.timed { TIMED_RECORD } else { 0 };
        out.extend_from_slice(&len.to_be_bytes());
        out.extend_from_slice(&crc32fast::hash(&record.bytes).to_be_bytes());
        out.extend_from_slice(&record.bytes);
    }
    let digest = Sha256::digest(&out);
    out.extend_from_slice(&digest);
    Ok(out.freeze())
}

fn checked_body<'a>(bytes: &'a [u8], magic: &[u8; 8]) -> io::Result<&'a [u8]> {
    if bytes.len() < magic.len() + TRAILER || &bytes[..magic.len()] != magic {
        return Err(invalid("offloaded object has the wrong format"));
    }
    let (body, trailer) = bytes.split_at(bytes.len() - TRAILER);
    if Sha256::digest(body).as_slice() != trailer {
        return Err(invalid("offloaded object checksum mismatch"));
    }
    Ok(&body[magic.len()..])
}

/// Decodes and verifies a segment object.
pub fn decode_segment(bytes: &Bytes) -> io::Result<Segment> {
    let body = checked_body(bytes, SEGMENT_MAGIC)?;
    let header_len = body
        .get(..4)
        .map(|len| u32::from_be_bytes(len.try_into().unwrap()) as usize)
        .filter(|len| *len <= MAX_HEADER)
        .ok_or_else(|| invalid("offloaded segment header is damaged"))?;
    let header: SegmentHeader = decode(
        body.get(4..4 + header_len)
            .ok_or_else(|| invalid("offloaded segment header is short"))?,
    )?;
    let count = header.records as u64;
    if header.first.0 == 0
        || header
            .last
            .0
            .checked_sub(header.first.0)
            .map(|span| span + 1)
            != Some(count)
    {
        return Err(invalid("offloaded segment header is inconsistent"));
    }
    let mut at = 4 + header_len;
    let mut records = Vec::with_capacity(count as usize);
    for index in 0..count {
        let frame = body
            .get(at..at + 8)
            .ok_or_else(|| invalid("offloaded segment frame is short"))?;
        let len = u32::from_be_bytes(frame[..4].try_into().unwrap());
        let crc = u32::from_be_bytes(frame[4..].try_into().unwrap());
        let timed = len & TIMED_RECORD != 0;
        let len = (len & !TIMED_RECORD) as usize;
        if len > MAX_RECORD {
            return Err(invalid("offloaded record exceeds the record bound"));
        }
        let payload = body
            .get(at + 8..at + 8 + len)
            .ok_or_else(|| invalid("offloaded record is short"))?;
        if crc32fast::hash(payload) != crc {
            return Err(invalid("offloaded record checksum mismatch"));
        }
        let offset = SEGMENT_MAGIC.len() + at + 8;
        records.push(Record {
            lsn: Lsn(header.first.0 + index),
            timed,
            bytes: bytes.slice(offset..offset + len),
        });
        at += 8 + len;
    }
    if at != body.len() {
        return Err(invalid("offloaded segment has trailing bytes"));
    }
    Ok(Segment {
        header,
        records,
        size: bytes.len(),
    })
}

/// Where each lineage of a stream starts, as its lineage object records it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageRecord {
    pub stream: StreamId,
    pub lineage: u64,
    /// Every lineage up to and including this one, with the first LSN its
    /// segments are authoritative for, ascending.
    pub lineages: Vec<(u64, Lsn)>,
    /// The lowest LSN the stream still held when this lineage started.
    pub floor: Lsn,
    /// The highest writer epoch known when this lineage started.
    pub epoch: Epoch,
}

pub fn encode_lineage(record: &LineageRecord) -> io::Result<Bytes> {
    let mut out = Vec::from(&LINEAGE_MAGIC[..]);
    out.extend_from_slice(&encode(record)?);
    let digest = Sha256::digest(&out);
    out.extend_from_slice(&digest);
    Ok(Bytes::from(out))
}

pub fn decode_lineage(bytes: &[u8]) -> io::Result<LineageRecord> {
    let record: LineageRecord = decode(checked_body(bytes, LINEAGE_MAGIC)?)?;
    if record.lineages.last().map(|(lineage, _)| *lineage) != Some(record.lineage)
        || record
            .lineages
            .windows(2)
            .any(|pair| pair[0].0 >= pair[1].0 || pair[0].1 > pair[1].1)
    {
        return Err(invalid("offloaded lineage record is inconsistent"));
    }
    Ok(record)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn records(first: u64, count: u64) -> Vec<Record> {
        (first..first + count)
            .map(|lsn| Record {
                lsn: Lsn(lsn),
                timed: lsn % 3 == 0,
                bytes: Bytes::from(format!("record {lsn}")),
            })
            .collect()
    }

    #[test]
    fn segments_round_trip_and_refuse_damage() {
        let stream = StreamId(7);
        let written = records(5, 10);
        let bytes = encode_segment(stream, 2, &written, vec![(Lsn(5), Epoch(3))]).unwrap();
        let segment = decode_segment(&bytes).unwrap();
        assert_eq!(segment.records, written);
        assert_eq!(segment.header.first, Lsn(5));
        assert_eq!(segment.header.last, Lsn(14));
        assert_eq!(segment.header.lineage, 2);
        assert_eq!(segment.max_epoch(), Epoch(3));
        for position in [0, 9, 20, bytes.len() / 2, bytes.len() - 1] {
            let mut damaged = bytes.to_vec();
            damaged[position] ^= 1;
            assert!(decode_segment(&Bytes::from(damaged)).is_err(), "{position}");
        }
        assert!(decode_segment(&bytes.slice(..bytes.len() - 1)).is_err());
        let gap = [written[0].clone(), written[2].clone()];
        assert!(encode_segment(stream, 2, &gap, Vec::new()).is_err());
        assert!(encode_segment(stream, 2, &[], Vec::new()).is_err());
    }

    #[test]
    fn lineage_records_round_trip() {
        let record = LineageRecord {
            stream: StreamId(9),
            lineage: 1,
            lineages: vec![(0, Lsn(1)), (1, Lsn(40))],
            floor: Lsn(3),
            epoch: Epoch(4),
        };
        let bytes = encode_lineage(&record).unwrap();
        assert_eq!(decode_lineage(&bytes).unwrap(), record);
        let mut damaged = bytes.to_vec();
        damaged[10] ^= 1;
        assert!(decode_lineage(&damaged).is_err());
    }
}
