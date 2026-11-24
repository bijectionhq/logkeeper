//! Protobuf keeper messages inside big-endian length-prefixed frames.
use std::io;

use bytes::{Bytes, BytesMut};
use prost::Message;
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
        // An envelope names no stream. The keeper splits it before any per-stream rule.
        Request::Batch(_) => StreamId(0),
    }
}

pub fn encode_request(request: &Request) -> io::Result<Bytes> {
    encode_request_after(request, |bytes| Ok(Vec::with_capacity(bytes)))
}

pub(super) fn encode_request_after(
    request: &Request,
    prefix: impl FnOnce(usize) -> io::Result<Vec<u8>>,
) -> io::Result<Bytes> {
    if !well_formed_batch(request) {
        return Err(invalid("empty or nested keeper batch"));
    }
    let message = RequestFrame::from(request);
    let len = message.encoded_len();
    if len > MAX_FRAME_BYTES {
        return Err(invalid("keeper message too large"));
    }
    let mut body = prefix(len)?;
    message.encode(&mut body).map_err(io::Error::other)?;
    Ok(Bytes::from(body))
}

/// A batch carries at least one request and never another batch.
fn well_formed_batch(request: &Request) -> bool {
    match request {
        Request::Batch(requests) => {
            !requests.is_empty()
                && !requests
                    .iter()
                    .any(|request| matches!(request, Request::Batch(_)))
        }
        _ => true,
    }
}

/// Encoded size of one request inside a batch frame, including its field header.
pub fn batched_request_len(request: &Request) -> usize {
    let len = RequestFrame::from(request).encoded_len();
    1 + prost::encoding::encoded_len_varint(len as u64) + len
}

pub fn decode_request(body: Bytes) -> io::Result<Request> {
    decode::<RequestFrame>(body)?.try_into()
}

pub fn encode_reply(reply: &Reply) -> io::Result<Bytes> {
    if let Reply::Batch(replies) = reply
        && (replies.is_empty() || replies.iter().any(|reply| matches!(reply, Reply::Batch(_))))
    {
        return Err(invalid("empty or nested keeper batch"));
    }
    encode(&ReplyFrame::from(reply), MAX_FRAME_BYTES)
}

pub fn decode_reply(body: Bytes) -> io::Result<Reply> {
    decode::<ReplyFrame>(body)?.try_into()
}

pub(super) fn encode_checkpoint_view(view: &StreamView) -> io::Result<Bytes> {
    encode(&encode_view(view), u32::MAX as usize)
}

pub(super) fn decode_checkpoint_view(body: Bytes) -> io::Result<StreamView> {
    decode_view(View::decode(body).map_err(io::Error::other)?)
}

fn encode(message: &impl Message, limit: usize) -> io::Result<Bytes> {
    let len = message.encoded_len();
    if len > limit {
        return Err(invalid("keeper message too large"));
    }
    let mut body = BytesMut::with_capacity(len);
    message.encode(&mut body).map_err(io::Error::other)?;
    Ok(body.freeze())
}

fn decode<M: Message + Default>(body: Bytes) -> io::Result<M> {
    if body.is_empty() || body.len() > MAX_FRAME_BYTES {
        return Err(invalid("invalid keeper message length"));
    }
    M::decode(body).map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

fn encode_id(id: u128) -> Bytes {
    Bytes::copy_from_slice(&id.to_be_bytes())
}

fn decode_id(id: &[u8]) -> io::Result<u128> {
    Ok(u128::from_be_bytes(
        id.try_into().map_err(|_| invalid("invalid ID length"))?,
    ))
}

fn encode_ensemble(ensemble: &[KeeperId; 3]) -> Vec<Bytes> {
    ensemble.iter().map(|id| encode_id(id.0)).collect()
}

fn decode_ensemble(ensemble: Vec<Bytes>) -> io::Result<[KeeperId; 3]> {
    let [a, b, c]: [Bytes; 3] = ensemble
        .try_into()
        .map_err(|_| invalid("invalid ensemble size"))?;
    Ok([
        KeeperId(decode_id(&a)?),
        KeeperId(decode_id(&b)?),
        KeeperId(decode_id(&c)?),
    ])
}

fn encode_runs(runs: &[EpochRun]) -> Vec<Run> {
    runs.iter()
        .map(|run| Run {
            epoch: run.epoch.0,
            first: run.first.0,
            last: run.last.0,
        })
        .collect()
}

fn decode_runs(runs: Vec<Run>) -> Vec<EpochRun> {
    runs.into_iter()
        .map(|run| EpochRun {
            epoch: Epoch(run.epoch),
            first: Lsn(run.first),
            last: Lsn(run.last),
        })
        .collect()
}

fn encode_view(view: &StreamView) -> View {
    View {
        promised: view
            .promised
            .as_ref()
            .map(|(epoch, identity, proposal)| Promise {
                epoch: epoch.0,
                identity: identity.as_str().to_owned(),
                proposal: encode_id(*proposal),
            }),
        synced: view.synced.map(|epoch| epoch.0),
        tail: view.tail.0,
        head: view.head.0,
        floor: view.floor.0,
        runs: encode_runs(&view.runs),
        ensemble: encode_ensemble(&view.ensemble),
        learner: view.learner,
    }
}

fn decode_view(view: View) -> io::Result<StreamView> {
    Ok(StreamView {
        promised: view
            .promised
            .map(|promise| {
                decode_id(&promise.proposal).map(|proposal| {
                    (
                        Epoch(promise.epoch),
                        Identity::from(promise.identity),
                        proposal,
                    )
                })
            })
            .transpose()?,
        synced: view.synced.map(Epoch),
        tail: Lsn(view.tail),
        head: Lsn(view.head),
        floor: Lsn(view.floor),
        runs: decode_runs(view.runs),
        ensemble: decode_ensemble(view.ensemble)?,
        learner: view.learner,
    })
}

#[derive(Clone, Message)]
struct Empty {}

#[derive(Clone, Message)]
struct Run {
    #[prost(fixed64, tag = "1")]
    epoch: u64,
    #[prost(fixed64, tag = "2")]
    first: u64,
    #[prost(fixed64, tag = "3")]
    last: u64,
}

#[derive(Clone, Message)]
struct Record {
    #[prost(fixed64, tag = "1")]
    lsn: u64,
    #[prost(bytes = "bytes", tag = "2")]
    payload: Bytes,
}

#[derive(Clone, Message)]
struct Promise {
    #[prost(fixed64, tag = "1")]
    epoch: u64,
    #[prost(string, tag = "2")]
    identity: String,
    #[prost(bytes = "bytes", tag = "3")]
    proposal: Bytes,
}

#[derive(Clone, Message)]
struct View {
    #[prost(message, optional, tag = "1")]
    promised: Option<Promise>,
    #[prost(fixed64, optional, tag = "2")]
    synced: Option<u64>,
    #[prost(fixed64, tag = "3")]
    tail: u64,
    #[prost(fixed64, tag = "4")]
    head: u64,
    #[prost(fixed64, tag = "5")]
    floor: u64,
    #[prost(message, repeated, tag = "6")]
    runs: Vec<Run>,
    #[prost(bytes = "bytes", repeated, tag = "7")]
    ensemble: Vec<Bytes>,
    #[prost(bool, tag = "8")]
    learner: bool,
}

#[derive(Clone, Message)]
struct RequestFrame {
    #[prost(bytes = "bytes", tag = "1")]
    stream: Bytes,
    #[prost(oneof = "RequestBody", tags = "2, 3, 4, 5, 6, 7, 8, 9, 10, 11")]
    body: Option<RequestBody>,
    /// A `Request::Batch` envelope. Exclusive with `stream` and `body`.
    #[prost(message, repeated, tag = "12")]
    batch: Vec<RequestFrame>,
}

// Each request schema declares its protobuf fields and their domain conversion together.
macro_rules! request_messages {
    ($($variant:ident = $tag:literal {
        $($(#[$field_encoding:meta])* $field:ident: $wire_type:ty => $conversion:ident),+ $(,)?
    }),+ $(,)?) => {
        mod request {
            use super::*;

            $(
                #[derive(Clone, Message)]
                pub(super) struct $variant {
                    $($(#[$field_encoding])* pub(super) $field: $wire_type,)+
                }
            )+
        }

        #[derive(Clone, prost::Oneof)]
        enum RequestBody {
            $(#[prost(message, tag = $tag)] $variant(request::$variant),)+
        }

        impl From<&Request> for RequestFrame {
            fn from(value: &Request) -> Self {
                let body = match value {
                    Request::Batch(requests) => {
                        return Self {
                            stream: Bytes::new(),
                            body: None,
                            batch: requests.iter().map(Self::from).collect(),
                        };
                    }
                    $(Request::$variant { stream: _, $($field),+ } =>
                        RequestBody::$variant(request::$variant {
                            $($field: request_field!(encode $conversion, $field),)+
                        }),)+
                };
                Self { stream: encode_id(stream(value).0), body: Some(body), batch: Vec::new() }
            }
        }

        impl TryFrom<RequestFrame> for Request {
            type Error = io::Error;

            fn try_from(frame: RequestFrame) -> io::Result<Self> {
                if !frame.batch.is_empty() {
                    if frame.body.is_some()
                        || !frame.stream.is_empty()
                        || frame.batch.iter().any(|request| !request.batch.is_empty())
                    {
                        return Err(invalid("malformed keeper batch"));
                    }
                    return frame.batch.into_iter().map(Self::try_from).collect::<io::Result<_>>().map(Self::Batch);
                }
                let stream = StreamId(decode_id(&frame.stream)?);
                Ok(match frame.body.ok_or_else(|| invalid("missing keeper request variant"))? {
                    $(RequestBody::$variant(body) => Self::$variant {
                        stream,
                        $($field: request_field!(decode $conversion, body.$field),)+
                    },)+
                })
            }
        }
    };
}

macro_rules! request_field {
    (encode copy, $value:expr) => {
        *$value
    };
    (encode clone, $value:expr) => {
        $value.clone()
    };
    (encode position, $value:expr) => {
        $value.0
    };
    (encode epoch, $value:expr) => {
        $value.0
    };
    (encode ensemble, $value:expr) => {
        encode_ensemble($value)
    };
    (encode id, $value:expr) => {
        encode_id(*$value)
    };
    (decode id, $value:expr) => {
        decode_id(&$value)?
    };
    (encode runs, $value:expr) => {
        encode_runs($value)
    };
    (decode copy, $value:expr) => {
        $value
    };
    (decode clone, $value:expr) => {
        $value
    };
    (decode position, $value:expr) => {
        Lsn($value)
    };
    (decode epoch, $value:expr) => {
        Epoch($value)
    };
    (decode ensemble, $value:expr) => {
        decode_ensemble($value)?
    };
    (decode runs, $value:expr) => {
        decode_runs($value)
    };
}

request_messages! {
    Create = "2" {
        #[prost(bytes = "bytes", repeated, tag = "1")]
        ensemble: Vec<Bytes> => ensemble,
    },
    Seal = "3" {
        #[prost(bytes = "bytes", repeated, tag = "1")]
        ensemble: Vec<Bytes> => ensemble,
        #[prost(fixed64, tag = "2")]
        epoch: u64 => epoch,
        #[prost(bytes = "bytes", tag = "3")]
        proposal: Bytes => id,
    },
    Sync = "4" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
        #[prost(fixed64, tag = "2")]
        floor: u64 => position,
        #[prost(fixed64, tag = "3")]
        from: u64 => position,
        #[prost(bytes = "bytes", repeated, tag = "4")]
        records: Vec<Bytes> => clone,
        #[prost(message, repeated, tag = "5")]
        runs: Vec<Run> => runs,
        #[prost(fixed64, tag = "6")]
        head: u64 => position,
        #[prost(bool, tag = "7")]
        complete: bool => copy,
    },
    Append = "5" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
        #[prost(fixed64, tag = "2")]
        at: u64 => position,
        #[prost(bytes = "bytes", repeated, tag = "3")]
        records: Vec<Bytes> => clone,
        #[prost(fixed64, tag = "4")]
        head: u64 => position,
    },
    Trim = "6" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
        #[prost(fixed64, tag = "2")]
        through: u64 => position,
    },
    Check = "7" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
    },
    Recover = "8" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
        #[prost(fixed64, tag = "2")]
        from: u64 => position,
        #[prost(uint32, tag = "3")]
        max: u32 => copy,
    },
    Read = "9" {
        #[prost(fixed64, tag = "1")]
        from: u64 => position,
        #[prost(uint32, tag = "2")]
        max: u32 => copy,
        #[prost(uint32, tag = "3")]
        wait_ms: u32 => copy,
    },
    Delete = "10" {
        #[prost(bytes = "bytes", repeated, tag = "1")]
        ensemble: Vec<Bytes> => ensemble,
    },
    Replace = "11" {
        #[prost(fixed64, tag = "1")]
        epoch: u64 => epoch,
        #[prost(bytes = "bytes", repeated, tag = "2")]
        from: Vec<Bytes> => ensemble,
        #[prost(bytes = "bytes", repeated, tag = "3")]
        to: Vec<Bytes> => ensemble,
    },
}

#[derive(Clone, Message)]
struct ReplyFrame {
    #[prost(oneof = "ReplyBody", tags = "1, 2, 3, 4, 5, 6, 7, 8, 9, 10")]
    body: Option<ReplyBody>,
    /// A `Reply::Batch` envelope. Exclusive with `body`.
    #[prost(message, repeated, tag = "11")]
    batch: Vec<ReplyFrame>,
}

#[derive(Clone, prost::Oneof)]
enum ReplyBody {
    #[prost(message, tag = "1")]
    Created(Empty),
    #[prost(message, tag = "2")]
    Sealed(View),
    #[prost(message, tag = "3")]
    Synced(Position),
    #[prost(message, tag = "4")]
    Appended(Position),
    #[prost(message, tag = "5")]
    Trimmed(Position),
    #[prost(message, tag = "6")]
    Checked(View),
    #[prost(message, tag = "7")]
    Records(ReplyRecords),
    #[prost(message, tag = "8")]
    Deleted(Empty),
    #[prost(message, tag = "9")]
    Replaced(Empty),
    #[prost(message, tag = "10")]
    Refused(RefusalFrame),
}

#[derive(Clone, Message)]
struct Position {
    #[prost(fixed64, tag = "1")]
    lsn: u64,
}

#[derive(Clone, Message)]
struct ReplyRecords {
    #[prost(fixed64, tag = "1")]
    floor: u64,
    #[prost(message, repeated, tag = "2")]
    records: Vec<Record>,
    #[prost(fixed64, tag = "3")]
    head: u64,
}

#[derive(Clone, Message)]
struct RefusalFrame {
    #[prost(oneof = "RefusalBody", tags = "1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12")]
    body: Option<RefusalBody>,
}

#[derive(Clone, prost::Oneof)]
enum RefusalBody {
    #[prost(message, tag = "1")]
    Fenced(Position),
    #[prost(message, tag = "2")]
    NotSynced(Empty),
    #[prost(message, tag = "3")]
    Gap(Position),
    #[prost(message, tag = "4")]
    Conflict(Position),
    #[prost(message, tag = "5")]
    BelowFloor(Position),
    #[prost(message, tag = "6")]
    AboveHead(Position),
    #[prost(message, tag = "7")]
    Full(Position),
    #[prost(message, tag = "8")]
    TooLarge(RefusalTooLarge),
    #[prost(message, tag = "9")]
    NotFound(Empty),
    #[prost(message, tag = "10")]
    Deleted(Empty),
    #[prost(message, tag = "11")]
    Unauthorized(Empty),
    #[prost(message, tag = "12")]
    WrongEnsemble(RefusalWrongEnsemble),
}

#[derive(Clone, Message)]
struct RefusalTooLarge {
    #[prost(uint32, tag = "1")]
    max: u32,
}

#[derive(Clone, Message)]
struct RefusalWrongEnsemble {
    #[prost(bytes = "bytes", repeated, tag = "1")]
    ensemble: Vec<Bytes>,
}

impl From<&Reply> for ReplyFrame {
    fn from(value: &Reply) -> Self {
        let body = match value {
            Reply::Created => ReplyBody::Created(Empty {}),
            Reply::Sealed(view) => ReplyBody::Sealed(encode_view(view)),
            Reply::Synced { tail } => ReplyBody::Synced(Position { lsn: tail.0 }),
            Reply::Appended { tail } => ReplyBody::Appended(Position { lsn: tail.0 }),
            Reply::Trimmed { floor } => ReplyBody::Trimmed(Position { lsn: floor.0 }),
            Reply::Checked(view) => ReplyBody::Checked(encode_view(view)),
            Reply::Records {
                floor,
                records,
                head,
            } => ReplyBody::Records(ReplyRecords {
                floor: floor.0,
                records: records
                    .iter()
                    .map(|(lsn, payload)| Record {
                        lsn: lsn.0,
                        payload: payload.clone(),
                    })
                    .collect(),
                head: head.0,
            }),
            Reply::Deleted => ReplyBody::Deleted(Empty {}),
            Reply::Replaced => ReplyBody::Replaced(Empty {}),
            Reply::Refused(refusal) => ReplyBody::Refused(RefusalFrame::from(refusal)),
            Reply::Batch(replies) => {
                return Self {
                    body: None,
                    batch: replies.iter().map(Self::from).collect(),
                };
            }
        };
        Self {
            body: Some(body),
            batch: Vec::new(),
        }
    }
}

impl TryFrom<ReplyFrame> for Reply {
    type Error = io::Error;

    fn try_from(frame: ReplyFrame) -> io::Result<Self> {
        if !frame.batch.is_empty() {
            if frame.body.is_some() || frame.batch.iter().any(|reply| !reply.batch.is_empty()) {
                return Err(invalid("malformed keeper batch"));
            }
            return frame
                .batch
                .into_iter()
                .map(Self::try_from)
                .collect::<io::Result<_>>()
                .map(Self::Batch);
        }
        Ok(
            match frame
                .body
                .ok_or_else(|| invalid("missing keeper message variant"))?
            {
                ReplyBody::Created(_) => Self::Created,
                ReplyBody::Sealed(body) => Self::Sealed(decode_view(body)?),
                ReplyBody::Synced(body) => Self::Synced {
                    tail: Lsn(body.lsn),
                },
                ReplyBody::Appended(body) => Self::Appended {
                    tail: Lsn(body.lsn),
                },
                ReplyBody::Trimmed(body) => Self::Trimmed {
                    floor: Lsn(body.lsn),
                },
                ReplyBody::Checked(body) => Self::Checked(decode_view(body)?),
                ReplyBody::Records(body) => Self::Records {
                    floor: Lsn(body.floor),
                    records: body
                        .records
                        .into_iter()
                        .map(|record| (Lsn(record.lsn), record.payload))
                        .collect(),
                    head: Lsn(body.head),
                },
                ReplyBody::Deleted(_) => Self::Deleted,
                ReplyBody::Replaced(_) => Self::Replaced,
                ReplyBody::Refused(body) => Self::Refused(Refusal::try_from(body)?),
            },
        )
    }
}

impl From<&Refusal> for RefusalFrame {
    fn from(value: &Refusal) -> Self {
        let body = match value {
            Refusal::Fenced { promised } => RefusalBody::Fenced(Position { lsn: promised.0 }),
            Refusal::NotSynced => RefusalBody::NotSynced(Empty {}),
            Refusal::Gap { head } => RefusalBody::Gap(Position { lsn: head.0 }),
            Refusal::Conflict { head } => RefusalBody::Conflict(Position { lsn: head.0 }),
            Refusal::BelowFloor { floor } => RefusalBody::BelowFloor(Position { lsn: floor.0 }),
            Refusal::AboveHead { head } => RefusalBody::AboveHead(Position { lsn: head.0 }),
            Refusal::Full { floor } => RefusalBody::Full(Position { lsn: floor.0 }),
            Refusal::TooLarge { max } => RefusalBody::TooLarge(RefusalTooLarge { max: *max }),
            Refusal::NotFound => RefusalBody::NotFound(Empty {}),
            Refusal::Deleted => RefusalBody::Deleted(Empty {}),
            Refusal::Unauthorized => RefusalBody::Unauthorized(Empty {}),
            Refusal::WrongEnsemble { ensemble } => {
                RefusalBody::WrongEnsemble(RefusalWrongEnsemble {
                    ensemble: encode_ensemble(ensemble),
                })
            }
        };
        Self { body: Some(body) }
    }
}

impl TryFrom<RefusalFrame> for Refusal {
    type Error = io::Error;

    fn try_from(frame: RefusalFrame) -> io::Result<Self> {
        Ok(
            match frame
                .body
                .ok_or_else(|| invalid("missing keeper message variant"))?
            {
                RefusalBody::Fenced(body) => Self::Fenced {
                    promised: Epoch(body.lsn),
                },
                RefusalBody::NotSynced(_) => Self::NotSynced,
                RefusalBody::Gap(body) => Self::Gap {
                    head: Lsn(body.lsn),
                },
                RefusalBody::Conflict(body) => Self::Conflict {
                    head: Lsn(body.lsn),
                },
                RefusalBody::BelowFloor(body) => Self::BelowFloor {
                    floor: Lsn(body.lsn),
                },
                RefusalBody::AboveHead(body) => Self::AboveHead {
                    head: Lsn(body.lsn),
                },
                RefusalBody::Full(body) => Self::Full {
                    floor: Lsn(body.lsn),
                },
                RefusalBody::TooLarge(body) => Self::TooLarge { max: body.max },
                RefusalBody::NotFound(_) => Self::NotFound,
                RefusalBody::Deleted(_) => Self::Deleted,
                RefusalBody::Unauthorized(_) => Self::Unauthorized,
                RefusalBody::WrongEnsemble(body) => Self::WrongEnsemble {
                    ensemble: decode_ensemble(body.ensemble)?,
                },
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_every_keeper_message() {
        let stream = StreamId(6);
        let epoch = Epoch(2);
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
                proposal: 17,
                ensemble,
            },
            Request::Sync {
                stream,
                epoch,
                from: Lsn(1),
                floor: Lsn(1),
                records: records.clone(),
                runs: runs.clone(),
                head: Lsn(2),
                complete: true,
            },
            Request::Append {
                stream,
                epoch,
                at: Lsn(1),
                records,
                head: Lsn(1),
            },
            Request::Trim {
                stream,
                epoch,
                through: Lsn(1),
            },
            Request::Check { stream, epoch },
            Request::Recover {
                stream,
                epoch,
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
                from: ensemble,
                to: [KeeperId(1), KeeperId(2), KeeperId(4)],
            },
        ] {
            let body = encode_request(&request).unwrap();
            assert_eq!(decode_request(body.clone()).unwrap(), request);
            assert!(decode_request(body.slice(..body.len() - 1)).is_err());
        }

        let view = StreamView {
            promised: Some((epoch, Identity::from_static("urn:logkeeper:client:1"), 17)),
            synced: Some(epoch),
            tail: Lsn(2),
            floor: Lsn(1),
            head: Lsn(1),
            runs,
            ensemble,
            learner: true,
        };
        let refusals = [
            Refusal::Fenced { promised: epoch },
            Refusal::NotSynced,
            Refusal::Gap { head: Lsn(2) },
            Refusal::Conflict { head: Lsn(2) },
            Refusal::BelowFloor { floor: Lsn(1) },
            Refusal::AboveHead { head: Lsn(1) },
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
            Reply::Synced { tail: Lsn(2) },
            Reply::Appended { tail: Lsn(2) },
            Reply::Trimmed { floor: Lsn(1) },
            Reply::Checked(view),
            Reply::Records {
                floor: Lsn(1),
                records: vec![(Lsn(1), Bytes::from_static(b"record"))],
                head: Lsn(1),
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

    #[test]
    fn requires_a_proposal_id_on_seal_and_in_a_promise() {
        let ensemble = [KeeperId(1), KeeperId(2), KeeperId(3)];
        for proposal in [Bytes::new(), Bytes::from_static(b"short")] {
            let frame = RequestFrame {
                stream: encode_id(6),
                body: Some(RequestBody::Seal(request::Seal {
                    ensemble: encode_ensemble(&ensemble),
                    epoch: 2,
                    proposal: proposal.clone(),
                })),
                batch: Vec::new(),
            };
            let view = View {
                promised: Some(Promise {
                    epoch: 2,
                    identity: "urn:logkeeper:client:1".to_owned(),
                    proposal,
                }),
                floor: 1,
                ensemble: encode_ensemble(&ensemble),
                ..View::default()
            };
            assert!(
                decode_request(encode(&frame, MAX_FRAME_BYTES).unwrap()).is_err(),
                "decoded a Seal without a valid proposal ID"
            );
            let reply = ReplyFrame {
                body: Some(ReplyBody::Sealed(view.clone())),
                batch: Vec::new(),
            };
            assert!(
                decode_reply(encode(&reply, MAX_FRAME_BYTES).unwrap()).is_err(),
                "decoded a reply promise without a valid proposal ID"
            );
            assert!(
                decode_checkpoint_view(encode(&view, MAX_FRAME_BYTES).unwrap()).is_err(),
                "decoded a checkpoint promise without a valid proposal ID"
            );
        }
    }

    #[test]
    fn batch_envelopes_round_trip_and_reject_nesting() {
        let stream = StreamId(6);
        let check = Request::Check {
            stream,
            epoch: Epoch(1),
        };
        let append = Request::Append {
            stream: StreamId(7),
            epoch: Epoch(1),
            at: Lsn(1),
            records: vec![Bytes::from_static(b"record")],
            head: Lsn(0),
        };
        let batch = Request::Batch(vec![check.clone(), append]);
        let body = encode_request(&batch).unwrap();
        assert_eq!(decode_request(body).unwrap(), batch);
        let replies = Reply::Batch(vec![
            Reply::Appended { tail: Lsn(1) },
            Reply::Refused(Refusal::NotFound),
        ]);
        assert_eq!(
            decode_reply(encode_reply(&replies).unwrap()).unwrap(),
            replies
        );
        for malformed in [
            Request::Batch(Vec::new()),
            Request::Batch(vec![Request::Batch(vec![check.clone()])]),
        ] {
            assert!(encode_request(&malformed).is_err(), "encoded {malformed:?}");
        }
        assert!(encode_reply(&Reply::Batch(Vec::new())).is_err());
        assert!(encode_reply(&Reply::Batch(vec![replies.clone()])).is_err());
        // Hand-built frames that the encoder refuses must not decode either.
        let nested = RequestFrame {
            stream: Bytes::new(),
            body: None,
            batch: vec![RequestFrame::from(&Request::Batch(vec![check.clone()]))],
        };
        let mixed = RequestFrame {
            batch: vec![RequestFrame::from(&check)],
            ..RequestFrame::from(&check)
        };
        for frame in [nested, mixed] {
            assert!(decode_request(encode(&frame, MAX_FRAME_BYTES).unwrap()).is_err());
        }
        let nested = ReplyFrame {
            body: None,
            batch: vec![ReplyFrame::from(&replies)],
        };
        assert!(decode_reply(encode(&nested, MAX_FRAME_BYTES).unwrap()).is_err());
        assert_eq!(
            batched_request_len(&check),
            encode_request(&Request::Batch(vec![check.clone()]))
                .unwrap()
                .len()
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
