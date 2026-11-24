//! Outgoing request frames with borrowed record payloads.

use std::io::{self, IoSlice};

use bytes::{BufMut, Bytes};
use prost::{Message, encoding};
use tokio::io::{AsyncWrite, AsyncWriteExt};

use super::{MAX_FRAME_BYTES, Request, RequestBody, RequestFrame, checked_request_frame, request};

const CONTROL_BYTES: usize = 4096;
const RECORDS_PER_WRITE: usize = 16;
// Append and Sync record keys each occupy one byte.
const RECORD_HEADER_BYTES: usize = 1 + encoding::encoded_len_varint(MAX_FRAME_BYTES as u64);

pub(in crate::stream) struct RequestWrite {
    frame: RequestFrame,
    len: usize,
}

impl RequestWrite {
    pub(in crate::stream) fn preflight(request: Request) -> io::Result<Self> {
        // Prost sizes the complete message using the length of each retained Bytes.
        let (frame, len) = checked_request_frame(&request)?;
        Ok(Self { frame, len })
    }

    pub(in crate::stream) async fn write(
        self,
        channel: &mut (impl AsyncWrite + Unpin),
    ) -> io::Result<()> {
        let mut control = Vec::with_capacity(128);
        control.extend_from_slice(&(self.len as u32).to_be_bytes());
        if self.frame.batch.is_empty() {
            write_request(channel, &self.frame, false, &mut control).await?;
        } else {
            for frame in &self.frame.batch {
                write_request(channel, frame, true, &mut control).await?;
            }
        }
        channel.write_all(&control).await?;
        channel.flush().await
    }
}

async fn write_request(
    channel: &mut (impl AsyncWrite + Unpin),
    frame: &RequestFrame,
    in_batch: bool,
    control: &mut Vec<u8>,
) -> io::Result<()> {
    flush_full_control(channel, control).await?;
    if in_batch {
        encode_delimited_header(12, frame.encoded_len(), control);
    }
    // Match Prost's tag order and omit default singular scalars. Repeated record
    // fields still get a header for a zero-length entry.
    match &frame.body {
        Some(RequestBody::Append(
            body @ request::Append {
                epoch,
                at,
                records,
                head,
            },
        )) => {
            encoding::bytes::encode(1, &frame.stream, control);
            encode_delimited_header(5, body.encoded_len(), control);
            encode_fixed64(1, *epoch, control);
            encode_fixed64(2, *at, control);
            write_records(channel, 3, records, control).await?;
            encode_fixed64(4, *head, control);
        }
        Some(RequestBody::Sync(
            body @ request::Sync {
                epoch,
                floor,
                from,
                records,
                runs,
                head,
                complete,
            },
        )) => {
            encoding::bytes::encode(1, &frame.stream, control);
            encode_delimited_header(4, body.encoded_len(), control);
            encode_fixed64(1, *epoch, control);
            encode_fixed64(2, *floor, control);
            encode_fixed64(3, *from, control);
            write_records(channel, 4, records, control).await?;
            for run in runs {
                flush_full_control(channel, control).await?;
                encoding::message::encode(5, run, control);
            }
            encode_fixed64(6, *head, control);
            if *complete {
                encoding::bool::encode(7, complete, control);
            }
        }
        _ => frame.encode(control).map_err(io::Error::other)?,
    }
    Ok(())
}

fn encode_delimited_header(tag: u32, len: usize, out: &mut impl BufMut) {
    encoding::encode_key(tag, encoding::WireType::LengthDelimited, out);
    encoding::encode_varint(len as u64, out);
}

fn encode_fixed64(tag: u32, value: u64, out: &mut impl BufMut) {
    if value != 0 {
        encoding::fixed64::encode(tag, &value, out);
    }
}

async fn flush_full_control(
    channel: &mut (impl AsyncWrite + Unpin),
    control: &mut Vec<u8>,
) -> io::Result<()> {
    if control.len() >= CONTROL_BYTES {
        channel.write_all(control).await?;
        control.clear();
    }
    Ok(())
}

async fn write_records(
    channel: &mut (impl AsyncWrite + Unpin),
    tag: u32,
    records: &[Bytes],
    control: &mut Vec<u8>,
) -> io::Result<()> {
    for group in records.chunks(RECORDS_PER_WRITE) {
        let mut headers = [[0; RECORD_HEADER_BYTES]; RECORDS_PER_WRITE];
        let mut parts: [IoSlice<'_>; 1 + 2 * RECORDS_PER_WRITE] =
            std::array::from_fn(|_| IoSlice::new(&[]));
        let mut count = 0;
        if !control.is_empty() {
            parts[count] = IoSlice::new(control.as_slice());
            count += 1;
        }
        for (header, record) in headers.iter_mut().zip(group) {
            let mut out = &mut header[..];
            encode_delimited_header(tag, record.len(), &mut out);
            let len = RECORD_HEADER_BYTES - out.len();
            parts[count] = IoSlice::new(&header[..len]);
            count += 1;
            if !record.is_empty() {
                parts[count] = IoSlice::new(record);
                count += 1;
            }
        }
        let mut remaining = &mut parts[..count];
        while !remaining.is_empty() {
            let written = channel.write_vectored(remaining).await?;
            if written == 0 {
                return Err(io::ErrorKind::WriteZero.into());
            }
            IoSlice::advance_slices(&mut remaining, written);
        }
        control.clear();
    }
    Ok(())
}
