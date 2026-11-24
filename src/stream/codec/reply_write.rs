//! TCP reply framing with bounded control scratch and borrowed record payloads.

use std::io::{self, IoSlice};

use bytes::Bytes;
use prost::encoding::{self, WireType};
use tokio::io::{AsyncWrite, AsyncWriteExt};

use super::{MAX_FRAME_BYTES, ReplyFrame, encode, invalid, validate_reply_batch};
use crate::stream::wire::{Lsn, Reply};

const RECORDS_PER_WRITE: usize = 32;

// Tags from ReplyFrame, ReplyBody, ReplyRecords, and Record in the stream codec.
const BATCH_TAG: u32 = 11;
const RECORDS_TAG: u32 = 7;
const FLOOR_TAG: u32 = 1;
const RECORD_TAG: u32 = 2;
const HEAD_TAG: u32 = 3;
const LSN_TAG: u32 = 1;
const PAYLOAD_TAG: u32 = 2;

pub(in crate::stream) struct PreparedReply<'a> {
    body_len: usize,
    body: Body<'a>,
}

enum Body<'a> {
    Single(Part<'a>),
    Batch(Vec<Part<'a>>),
}

enum Part<'a> {
    Control(Bytes),
    Records(Records<'a>),
}

struct Records<'a> {
    body_len: usize,
    floor: Lsn,
    records: &'a [(Lsn, Bytes)],
    head: Lsn,
}

impl<'a> PreparedReply<'a> {
    /// Validate the complete body, including batch envelopes, before any socket write.
    pub(in crate::stream) fn new(reply: &'a Reply) -> io::Result<Self> {
        if let Reply::Batch(replies) = reply {
            validate_reply_batch(replies)?;
            if replies
                .iter()
                .any(|reply| matches!(reply, Reply::Records { .. }))
            {
                return Self::batch(replies);
            }
        }
        let part = Part::new(reply, MAX_FRAME_BYTES)?;
        Ok(Self {
            body_len: part.encoded_len(),
            body: Body::Single(part),
        })
    }

    fn batch(replies: &'a [Reply]) -> io::Result<Self> {
        let mut body_len = 0;
        let mut parts = Vec::new();
        for reply in replies {
            let remaining = MAX_FRAME_BYTES - body_len;
            let part = Part::new(reply, remaining)?;
            body_len += capped_len(delimited_len(BATCH_TAG, part.encoded_len()), remaining)?;
            parts.push(part);
        }
        Ok(Self {
            body_len,
            body: Body::Batch(parts),
        })
    }

    pub(in crate::stream) async fn write(
        &self,
        channel: &mut (impl AsyncWrite + Unpin),
    ) -> io::Result<()> {
        channel.write_u32(self.body_len as u32).await?;
        let mut control = Vec::new();
        match &self.body {
            Body::Single(part) => part.write(channel, &mut control).await?,
            Body::Batch(parts) => {
                for part in parts {
                    control.clear();
                    encode_delimited_header(BATCH_TAG, part.encoded_len(), &mut control);
                    part.write(channel, &mut control).await?;
                }
            }
        }
        channel.flush().await
    }
}

impl<'a> Part<'a> {
    fn new(reply: &'a Reply, limit: usize) -> io::Result<Self> {
        match reply {
            Reply::Records {
                floor,
                records,
                head,
            } => {
                let mut body_len = fixed64_len(FLOOR_TAG, floor.0) + fixed64_len(HEAD_TAG, head.0);
                for (lsn, payload) in records {
                    let record = delimited_len(RECORD_TAG, record_len(*lsn, payload.len()));
                    body_len = capped_len(body_len.saturating_add(record), limit)?;
                }
                capped_len(delimited_len(RECORDS_TAG, body_len), limit)?;
                Ok(Self::Records(Records {
                    body_len,
                    floor: *floor,
                    records,
                    head: *head,
                }))
            }
            _ => Ok(Self::Control(encode(&ReplyFrame::from(reply), limit)?)),
        }
    }

    fn encoded_len(&self) -> usize {
        match self {
            Self::Control(body) => body.len(),
            Self::Records(records) => delimited_len(RECORDS_TAG, records.body_len),
        }
    }

    async fn write(
        &self,
        channel: &mut (impl AsyncWrite + Unpin),
        control: &mut Vec<u8>,
    ) -> io::Result<()> {
        match self {
            Self::Control(body) if control.is_empty() => channel.write_all(body).await,
            Self::Control(body) => {
                let mut spans = [IoSlice::new(control), IoSlice::new(body)];
                write_spans(channel, &mut spans).await
            }
            Self::Records(records) => records.write(channel, control).await,
        }
    }
}

impl Records<'_> {
    async fn write(
        &self,
        channel: &mut (impl AsyncWrite + Unpin),
        control: &mut Vec<u8>,
    ) -> io::Result<()> {
        // The first control span includes any batch header, the Records header, and floor.
        encode_delimited_header(RECORDS_TAG, self.body_len, control);
        encode_fixed64(FLOOR_TAG, self.floor.0, control);
        for chunk in self.records.chunks(RECORDS_PER_WRITE) {
            let mut ends = [0; RECORDS_PER_WRITE + 1];
            for ((lsn, payload), end) in chunk.iter().zip(&mut ends[1..]) {
                encode_delimited_header(RECORD_TAG, record_len(*lsn, payload.len()), control);
                encode_fixed64(LSN_TAG, lsn.0, control);
                if !payload.is_empty() {
                    encode_delimited_header(PAYLOAD_TAG, payload.len(), control);
                }
                *end = control.len();
            }

            let mut spans: [IoSlice<'_>; RECORDS_PER_WRITE * 2] =
                std::array::from_fn(|_| IoSlice::new(&[]));
            let mut count = 0;
            for (range, (_, payload)) in ends.windows(2).zip(chunk) {
                spans[count] = IoSlice::new(&control[range[0]..range[1]]);
                count += 1;
                if !payload.is_empty() {
                    spans[count] = IoSlice::new(payload);
                    count += 1;
                }
            }
            write_spans(channel, &mut spans[..count]).await?;
            control.clear();
        }
        encode_fixed64(HEAD_TAG, self.head.0, control);
        channel.write_all(control).await
    }
}

async fn write_spans(
    channel: &mut (impl AsyncWrite + Unpin),
    mut spans: &mut [IoSlice<'_>],
) -> io::Result<()> {
    while !spans.is_empty() {
        match channel.write_vectored(spans).await {
            Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
            Ok(written) => IoSlice::advance_slices(&mut spans, written),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

fn capped_len(len: usize, limit: usize) -> io::Result<usize> {
    if len > limit {
        return Err(invalid("keeper message too large"));
    }
    Ok(len)
}

fn record_len(lsn: Lsn, payload_len: usize) -> usize {
    let len = fixed64_len(LSN_TAG, lsn.0);
    // As in Record, the bytes field is omitted for an empty payload.
    if payload_len == 0 {
        len
    } else {
        len.saturating_add(delimited_len(PAYLOAD_TAG, payload_len))
    }
}

fn delimited_len(tag: u32, len: usize) -> usize {
    (encoding::key_len(tag) + encoding::encoded_len_varint(len as u64)).saturating_add(len)
}

fn encode_delimited_header(tag: u32, len: usize, control: &mut Vec<u8>) {
    encoding::encode_key(tag, WireType::LengthDelimited, control);
    encoding::encode_varint(len as u64, control);
}

fn fixed64_len(tag: u32, value: u64) -> usize {
    if value == 0 {
        return 0;
    }
    encoding::fixed64::encoded_len(tag, &value)
}

fn encode_fixed64(tag: u32, value: u64, control: &mut Vec<u8>) {
    if value != 0 {
        encoding::fixed64::encode(tag, &value, control);
    }
}
