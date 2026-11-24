//! Length-prefixed keeper messages. The length is a big-endian u32, excluding itself.
use std::io;

use bytes::{Buf, BufMut, Bytes, BytesMut};
#[cfg(any(test, feature = "stream"))]
use tokio::io::{AsyncRead, AsyncReadExt};
#[cfg(feature = "stream")]
use tokio::io::{AsyncWrite, AsyncWriteExt};

use super::wire::*;

pub const MAX_FRAME_BYTES: usize = 64 * 1024 * 1024;
pub(super) const PAGE_BYTES: usize = MAX_FRAME_BYTES - 64;

pub(super) fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(any(test, feature = "stream"))]
pub(super) async fn read_frame(channel: &mut (impl AsyncRead + Unpin)) -> io::Result<Bytes> {
    let length = channel.read_u32().await? as usize;
    if length == 0 || length > MAX_FRAME_BYTES {
        return Err(invalid("invalid keeper frame length"));
    }
    let mut body = vec![0; length];
    channel.read_exact(&mut body).await?;
    Ok(Bytes::from(body))
}

#[cfg(feature = "stream")]
pub(super) async fn write_frame(
    channel: &mut (impl AsyncWrite + Unpin),
    body: &[u8],
) -> io::Result<()> {
    if body.is_empty() || body.len() > MAX_FRAME_BYTES {
        return Err(invalid("invalid keeper frame length"));
    }
    channel.write_u32(body.len() as u32).await?;
    channel.write_all(body).await?;
    channel.flush().await
}

pub(super) fn put_count(out: &mut BytesMut, len: usize) -> io::Result<()> {
    out.put_u32(
        len.try_into()
            .map_err(|_| invalid("keeper collection too large"))?,
    );
    Ok(())
}

pub(super) fn put_bytes(out: &mut BytesMut, bytes: &[u8]) -> io::Result<()> {
    put_count(out, bytes.len())?;
    out.put_slice(bytes);
    Ok(())
}

fn put_records(out: &mut BytesMut, records: &[Bytes]) -> io::Result<()> {
    put_count(out, records.len())?;
    for record in records {
        put_bytes(out, record)?;
    }
    Ok(())
}

fn put_runs(out: &mut BytesMut, runs: &[EpochRun]) -> io::Result<()> {
    put_count(out, runs.len())?;
    for run in runs {
        out.put_u64(run.epoch.0);
        out.put_u64(run.first.0);
        out.put_u64(run.last.0);
    }
    Ok(())
}

fn put_ensemble(out: &mut BytesMut, ensemble: &[KeeperId; 3]) {
    for keeper in ensemble {
        out.put_u128(keeper.0);
    }
}

pub(super) fn put_view(out: &mut BytesMut, view: &StreamView) -> io::Result<()> {
    out.put_u8(u8::from(view.promised.is_some()));
    if let Some((epoch, holder)) = view.promised {
        out.put_u64(epoch.0);
        out.put_u128(holder.0);
    }
    out.put_u8(u8::from(view.synced.is_some()));
    if let Some(epoch) = view.synced {
        out.put_u64(epoch.0);
    }
    out.put_u64(view.end.0);
    out.put_u64(view.commit.0);
    out.put_u64(view.floor.0);
    put_ensemble(out, &view.ensemble);
    out.put_u8(u8::from(view.learner));
    put_runs(out, &view.runs)
}

pub(super) struct Decoder(pub Bytes);

impl Decoder {
    fn take(&mut self, length: usize) -> io::Result<Bytes> {
        if self.0.len() < length {
            return Err(invalid("short keeper message"));
        }
        Ok(self.0.split_to(length))
    }

    pub(super) fn u8(&mut self) -> io::Result<u8> {
        Ok(self.take(1)?.get_u8())
    }

    pub(super) fn u32(&mut self) -> io::Result<u32> {
        Ok(self.take(4)?.get_u32())
    }

    pub(super) fn u64(&mut self) -> io::Result<u64> {
        Ok(self.take(8)?.get_u64())
    }

    pub(super) fn u128(&mut self) -> io::Result<u128> {
        Ok(self.take(16)?.get_u128())
    }

    pub(super) fn boolean(&mut self) -> io::Result<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(invalid("invalid keeper boolean")),
        }
    }

    pub(super) fn bytes(&mut self) -> io::Result<Bytes> {
        let count = self.u32()? as usize;
        self.take(count)
    }

    pub(super) fn count(&mut self, element_minimum: usize) -> io::Result<usize> {
        let count = self.u32()? as usize;
        if count > self.0.len() / element_minimum {
            return Err(invalid("short keeper collection"));
        }
        Ok(count)
    }

    fn records(&mut self) -> io::Result<Vec<Bytes>> {
        (0..self.count(4)?).map(|_| self.bytes()).collect()
    }

    fn runs(&mut self) -> io::Result<Vec<EpochRun>> {
        (0..self.count(24)?)
            .map(|_| {
                Ok(EpochRun {
                    epoch: Epoch(self.u64()?),
                    first: Lsn(self.u64()?),
                    last: Lsn(self.u64()?),
                })
            })
            .collect()
    }

    fn ensemble(&mut self) -> io::Result<[KeeperId; 3]> {
        Ok([
            KeeperId(self.u128()?),
            KeeperId(self.u128()?),
            KeeperId(self.u128()?),
        ])
    }

    pub(super) fn view(&mut self) -> io::Result<StreamView> {
        Ok(StreamView {
            promised: self
                .boolean()?
                .then(|| Ok::<_, io::Error>((Epoch(self.u64()?), Holder(self.u128()?))))
                .transpose()?,
            synced: self.boolean()?.then(|| self.u64().map(Epoch)).transpose()?,
            end: Lsn(self.u64()?),
            commit: Lsn(self.u64()?),
            floor: Lsn(self.u64()?),
            ensemble: self.ensemble()?,
            learner: self.boolean()?,
            runs: self.runs()?,
        })
    }

    pub(super) fn finish(self) -> io::Result<()> {
        if self.0.is_empty() {
            Ok(())
        } else {
            Err(invalid("trailing keeper message bytes"))
        }
    }
}

pub(super) fn stream(request: &Request) -> StreamId {
    match *request {
        Request::Create { stream, .. }
        | Request::Seal { stream, .. }
        | Request::Sync { stream, .. }
        | Request::Append { stream, .. }
        | Request::Trim { stream, .. }
        | Request::Check { stream, .. }
        | Request::Recover { stream, .. }
        | Request::Read { stream, .. }
        | Request::Replace { stream, .. }
        | Request::Delete { stream, .. } => stream,
    }
}

pub fn encode_request(request: &Request) -> io::Result<Bytes> {
    let mut out = BytesMut::new();
    write_request(&mut out, request)?;
    if out.len() > MAX_FRAME_BYTES {
        return Err(invalid("keeper request too large"));
    }
    Ok(out.freeze())
}

fn write_request(out: &mut BytesMut, request: &Request) -> io::Result<()> {
    let tag = match request {
        Request::Create { .. } => 0,
        Request::Seal { .. } => 1,
        Request::Sync { .. } => 2,
        Request::Append { .. } => 3,
        Request::Trim { .. } => 4,
        Request::Check { .. } => 5,
        Request::Read { .. } => 6,
        Request::Delete { .. } => 7,
        Request::Recover { .. } => 8,
        Request::Replace { .. } => 9,
    };
    out.put_u8(tag);
    out.put_u128(stream(request).0);
    match request {
        Request::Create { ensemble, .. } => put_ensemble(out, ensemble),
        Request::Seal {
            epoch,
            holder,
            ensemble,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            put_ensemble(out, ensemble);
        }
        Request::Sync {
            epoch,
            holder,
            floor,
            from,
            records,
            runs,
            commit,
            complete,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            out.put_u64(floor.0);
            out.put_u64(from.0);
            out.put_u64(commit.0);
            out.put_u8(u8::from(*complete));
            put_runs(out, runs)?;
            put_records(out, records)?;
        }
        Request::Append {
            epoch,
            holder,
            at,
            records,
            commit,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            out.put_u64(at.0);
            out.put_u64(commit.0);
            put_records(out, records)?;
        }
        Request::Trim {
            epoch,
            holder,
            through,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            out.put_u64(through.0);
        }
        Request::Check { epoch, .. } => out.put_u64(epoch.0),
        Request::Read {
            from, max, wait_ms, ..
        } => {
            out.put_u64(from.0);
            out.put_u32(*max);
            out.put_u32(*wait_ms);
        }
        Request::Recover {
            epoch,
            holder,
            from,
            max,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            out.put_u64(from.0);
            out.put_u32(*max);
        }
        Request::Replace {
            epoch,
            holder,
            from,
            to,
            ..
        } => {
            out.put_u64(epoch.0);
            out.put_u128(holder.0);
            put_ensemble(out, from);
            put_ensemble(out, to);
        }
        Request::Delete { ensemble, .. } => put_ensemble(out, ensemble),
    }
    Ok(())
}

pub fn decode_request(body: Bytes) -> io::Result<Request> {
    if body.len() > MAX_FRAME_BYTES {
        return Err(invalid("keeper request too large"));
    }
    let mut input = Decoder(body);
    let tag = input.u8()?;
    let stream = StreamId(input.u128()?);
    let request = match tag {
        0 => Request::Create {
            stream,
            ensemble: input.ensemble()?,
        },
        1 => Request::Seal {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            ensemble: input.ensemble()?,
        },
        2 => Request::Sync {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            floor: Lsn(input.u64()?),
            from: Lsn(input.u64()?),
            commit: Lsn(input.u64()?),
            complete: input.boolean()?,
            runs: input.runs()?,
            records: input.records()?,
        },
        3 => Request::Append {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            at: Lsn(input.u64()?),
            commit: Lsn(input.u64()?),
            records: input.records()?,
        },
        4 => Request::Trim {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            through: Lsn(input.u64()?),
        },
        5 => Request::Check {
            stream,
            epoch: Epoch(input.u64()?),
        },
        6 => Request::Read {
            stream,
            from: Lsn(input.u64()?),
            max: input.u32()?,
            wait_ms: input.u32()?,
        },
        7 => Request::Delete {
            stream,
            ensemble: input.ensemble()?,
        },
        8 => Request::Recover {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            from: Lsn(input.u64()?),
            max: input.u32()?,
        },
        9 => Request::Replace {
            stream,
            epoch: Epoch(input.u64()?),
            holder: Holder(input.u128()?),
            from: input.ensemble()?,
            to: input.ensemble()?,
        },
        _ => return Err(invalid("unknown keeper request")),
    };
    input.finish()?;
    Ok(request)
}

pub fn encode_reply(reply: &Reply) -> io::Result<Bytes> {
    let mut out = BytesMut::new();
    match reply {
        Reply::Created => out.put_u8(0),
        Reply::Sealed(view) => {
            out.put_u8(1);
            put_view(&mut out, view)?;
        }
        Reply::Synced { end } => {
            out.put_u8(2);
            out.put_u64(end.0);
        }
        Reply::Appended { end } => {
            out.put_u8(3);
            out.put_u64(end.0);
        }
        Reply::Trimmed { floor } => {
            out.put_u8(4);
            out.put_u64(floor.0);
        }
        Reply::Checked(view) => {
            out.put_u8(5);
            put_view(&mut out, view)?;
        }
        Reply::Records {
            floor,
            records,
            commit,
        } => {
            out.put_u8(6);
            out.put_u64(floor.0);
            out.put_u64(commit.0);
            put_count(&mut out, records.len())?;
            for (lsn, payload) in records {
                out.put_u64(lsn.0);
                put_bytes(&mut out, payload)?;
            }
        }
        Reply::Deleted => out.put_u8(7),
        Reply::Replaced => out.put_u8(9),
        Reply::Refused(refusal) => {
            out.put_u8(8);
            match refusal {
                Refusal::Fenced { promised } => {
                    out.put_u8(0);
                    out.put_u64(promised.0);
                }
                Refusal::NotSynced => out.put_u8(1),
                Refusal::Gap { end } => {
                    out.put_u8(2);
                    out.put_u64(end.0);
                }
                Refusal::Conflict { end } => {
                    out.put_u8(3);
                    out.put_u64(end.0);
                }
                Refusal::BelowFloor { floor } => {
                    out.put_u8(4);
                    out.put_u64(floor.0);
                }
                Refusal::AboveCommit { commit } => {
                    out.put_u8(5);
                    out.put_u64(commit.0);
                }
                Refusal::Full { floor } => {
                    out.put_u8(6);
                    out.put_u64(floor.0);
                }
                Refusal::TooLarge { max } => {
                    out.put_u8(7);
                    out.put_u32(*max);
                }
                Refusal::NotFound => out.put_u8(8),
                Refusal::Deleted => out.put_u8(9),
                Refusal::Unauthorized => out.put_u8(10),
                Refusal::WrongEnsemble { ensemble } => {
                    out.put_u8(11);
                    put_ensemble(&mut out, ensemble);
                }
            }
        }
    }
    if out.len() > MAX_FRAME_BYTES {
        return Err(invalid("keeper reply too large"));
    }
    Ok(out.freeze())
}

pub fn decode_reply(body: Bytes) -> io::Result<Reply> {
    if body.len() > MAX_FRAME_BYTES {
        return Err(invalid("keeper reply too large"));
    }
    let mut input = Decoder(body);
    let reply = match input.u8()? {
        0 => Reply::Created,
        1 => Reply::Sealed(input.view()?),
        2 => Reply::Synced {
            end: Lsn(input.u64()?),
        },
        3 => Reply::Appended {
            end: Lsn(input.u64()?),
        },
        4 => Reply::Trimmed {
            floor: Lsn(input.u64()?),
        },
        5 => Reply::Checked(input.view()?),
        6 => Reply::Records {
            floor: Lsn(input.u64()?),
            commit: Lsn(input.u64()?),
            records: (0..input.count(12)?)
                .map(|_| Ok((Lsn(input.u64()?), input.bytes()?)))
                .collect::<io::Result<_>>()?,
        },
        7 => Reply::Deleted,
        9 => Reply::Replaced,
        8 => Reply::Refused(match input.u8()? {
            0 => Refusal::Fenced {
                promised: Epoch(input.u64()?),
            },
            1 => Refusal::NotSynced,
            2 => Refusal::Gap {
                end: Lsn(input.u64()?),
            },
            3 => Refusal::Conflict {
                end: Lsn(input.u64()?),
            },
            4 => Refusal::BelowFloor {
                floor: Lsn(input.u64()?),
            },
            5 => Refusal::AboveCommit {
                commit: Lsn(input.u64()?),
            },
            6 => Refusal::Full {
                floor: Lsn(input.u64()?),
            },
            7 => Refusal::TooLarge { max: input.u32()? },
            8 => Refusal::NotFound,
            9 => Refusal::Deleted,
            10 => Refusal::Unauthorized,
            11 => Refusal::WrongEnsemble {
                ensemble: input.ensemble()?,
            },
            _ => return Err(invalid("unknown keeper refusal")),
        }),
        _ => return Err(invalid("unknown keeper reply")),
    };
    input.finish()?;
    Ok(reply)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_every_keeper_message() {
        let stream = StreamId(6);
        let epoch = Epoch(2);
        let holder = Holder(1);
        let ensemble = [KeeperId(1), KeeperId(2), KeeperId(3)];
        let records = vec![Bytes::new(), Bytes::from_static(b"record")];
        let runs = vec![EpochRun {
            epoch,
            first: Lsn(1),
            last: Lsn(2),
        }];
        for request in [
            Request::Create { stream, ensemble },
            Request::Seal {
                stream,
                epoch,
                holder,
                ensemble,
            },
            Request::Sync {
                stream,
                epoch,
                holder,
                from: Lsn(1),
                floor: Lsn(1),
                records: records.clone(),
                runs: runs.clone(),
                commit: Lsn(2),
                complete: true,
            },
            Request::Append {
                stream,
                epoch,
                holder,
                at: Lsn(1),
                records,
                commit: Lsn(1),
            },
            Request::Trim {
                stream,
                epoch,
                holder,
                through: Lsn(1),
            },
            Request::Check { stream, epoch },
            Request::Recover {
                stream,
                epoch,
                holder,
                from: Lsn(1),
                max: 5,
            },
            Request::Read {
                stream,
                from: Lsn(1),
                max: 5,
                wait_ms: 10,
            },
            Request::Delete { stream, ensemble },
            Request::Replace {
                stream,
                epoch,
                holder,
                from: ensemble,
                to: [KeeperId(1), KeeperId(2), KeeperId(4)],
            },
        ] {
            let body = encode_request(&request).unwrap();
            assert_eq!(decode_request(body.clone()).unwrap(), request);
            assert!(decode_request(body.slice(..body.len() - 1)).is_err());
        }

        let view = StreamView {
            promised: Some((epoch, holder)),
            synced: Some(epoch),
            end: Lsn(2),
            floor: Lsn(1),
            commit: Lsn(1),
            runs,
            ensemble,
            learner: true,
        };
        let refusals = [
            Refusal::Fenced { promised: epoch },
            Refusal::NotSynced,
            Refusal::Gap { end: Lsn(2) },
            Refusal::Conflict { end: Lsn(2) },
            Refusal::BelowFloor { floor: Lsn(1) },
            Refusal::AboveCommit { commit: Lsn(1) },
            Refusal::Full { floor: Lsn(1) },
            Refusal::TooLarge { max: 10 },
            Refusal::NotFound,
            Refusal::Deleted,
            Refusal::Unauthorized,
            Refusal::WrongEnsemble { ensemble },
        ];
        let replies = [
            Reply::Created,
            Reply::Sealed(view.clone()),
            Reply::Synced { end: Lsn(2) },
            Reply::Appended { end: Lsn(2) },
            Reply::Trimmed { floor: Lsn(1) },
            Reply::Checked(view),
            Reply::Records {
                floor: Lsn(1),
                records: vec![(Lsn(1), Bytes::from_static(b"record"))],
                commit: Lsn(1),
            },
            Reply::Deleted,
            Reply::Replaced,
        ];
        for reply in replies
            .into_iter()
            .chain(refusals.into_iter().map(Reply::Refused))
        {
            let body = encode_reply(&reply).unwrap();
            assert_eq!(decode_reply(body.clone()).unwrap(), reply);
            assert!(decode_reply(body.slice(..body.len() - 1)).is_err());
        }
        assert!(
            decode_reply(Bytes::from_static(&[0, 0])).is_err(),
            "accepted trailing reply bytes"
        );
    }

    #[tokio::test]
    async fn framing_rejects_an_oversized_length_before_reading_the_body() {
        use tokio::io::AsyncWriteExt;
        let (mut writer, mut reader) = tokio::io::duplex(64);
        writer.write_u32(MAX_FRAME_BYTES as u32 + 1).await.unwrap();
        assert_eq!(
            read_frame(&mut reader).await.unwrap_err().to_string(),
            "invalid keeper frame length"
        );
    }
}
