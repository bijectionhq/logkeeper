use std::{
    collections::{HashMap, HashSet},
    fmt,
    future::Future,
    io,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Duration,
};

use bincode::Options;
use futures::FutureExt;
use journal_contract::{Epoch, Lsn, StreamId};
use openraft::{
    BasicNode, EntryPayload, OptionalSend,
    errors::{NetworkError, RPCError, RaftError, ReplicationClosed, StreamingError, Unreachable},
    network::{Backoff, RPCOption, RaftNetworkFactory, RaftNetworkV2},
    raft::{
        AppendEntriesRequest, AppendEntriesResponse, AppendError, AppendResult, SnapshotResponse,
        VoteRequest, VoteResponse,
    },
};
use parking_lot::Mutex;
use serde::{
    Deserialize, Deserializer, Serialize,
    de::{self, DeserializeOwned, SeqAccess, Visitor},
};
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncSeekExt, AsyncWrite, AsyncWriteExt, ReadHalf, WriteHalf},
    sync::{OwnedSemaphorePermit, Semaphore, mpsc, oneshot, watch},
    time::{Instant, timeout},
};
use tokio_rustls::TlsConnector;

use super::decisions::{self, AppendFit, EntryKind, PeerKind, PeerLane};
use super::{
    ALPN, BULK_ALPN, CONTROL_ALPN, Entry, Fence, Genesis, KeeperStatus, Keepers, LogId,
    MAX_MESSAGE, NodeId, REPLICATION_ALPN, RaftTypes, SnapshotMeta, Stage, Vote, decode, encode,
    invalid, options,
    state::{Command, Outcome},
    storage::{SnapshotFile, StateMachine},
};
use crate::stream::transport::{Channel, connect_protocol};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Lane {
    Application,
    Control,
    Replication,
    Bulk,
}

/// Entries in one AppendEntries. The lane's frame limit still splits larger
/// batches by bytes through `fit_append`.
pub(super) const MAX_PEER_ENTRIES: usize = 64;
/// Retry delays after a refused or failed peer append: 5 ms doubling to
/// 500 ms. A follower's momentary `Busy` then costs milliseconds, where
/// OpenRaft's default waits a flat 500 ms.
const PEER_BACKOFF_FIRST: Duration = Duration::from_millis(5);
const PEER_BACKOFF_LAST: Duration = Duration::from_millis(500);

fn peer_backoff() -> impl Iterator<Item = Duration> {
    std::iter::successors(Some(PEER_BACKOFF_FIRST), |delay| {
        Some((*delay * 2).min(PEER_BACKOFF_LAST))
    })
}

impl Lane {
    pub fn alpn(self) -> &'static [u8] {
        match self {
            Self::Application => ALPN,
            Self::Control => CONTROL_ALPN,
            Self::Replication => REPLICATION_ALPN,
            Self::Bulk => BULK_ALPN,
        }
    }

    pub fn frame_limit(self) -> u64 {
        match self {
            Self::Application => 5 * 1024 * 1024,
            Self::Control => 64 * 1024,
            Self::Replication => 18 * 1024 * 1024,
            Self::Bulk => 2 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub(super) enum Request {
    Claim(Genesis),
    Locate(StreamId),
    Stage(Stage),
    Bootstrap(StreamId),
    Create(StreamId),
    Seal {
        stream: StreamId,
        expected: Epoch,
        writer: uuid::Uuid,
    },
    Append {
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payload: bytes::Bytes,
    },
    Read {
        stream: StreamId,
        from: Lsn,
        limit: usize,
        wait_ms: u32,
    },
    Head(StreamId),
    Trim {
        stream: StreamId,
        fence: Fence,
        through: Lsn,
    },
    Delete(StreamId),
    Configuration(StreamId),
    Replace {
        stream: StreamId,
        expected: u64,
        voters: [uuid::Uuid; 3],
    },
    PlacementProof(StreamId),
    StageReplica {
        genesis: Genesis,
        stage: Stage,
    },
    InstallReplica {
        genesis: Genesis,
        stage: Stage,
        generation: u64,
        through: super::LogId,
    },
    LocalCopy(StreamId),
    RetireCopy {
        stream: StreamId,
        authority: uuid::Uuid,
        revision: u64,
        generation: u64,
    },
    ReadAt {
        genesis: Genesis,
        from: Lsn,
        minimum_head: Lsn,
        limit: usize,
        wait_ms: u32,
    },
    AppendBatch {
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payloads: Vec<bytes::Bytes>,
    },
    /// Stage a timed original on one signing voter of `revision`.
    StageOriginal {
        stream: StreamId,
        revision: u64,
        original: Vec<u8>,
        payload: bytes::Bytes,
    },
    /// Append a timed original with its encoded evidence.
    AppendOriginal {
        stream: StreamId,
        fence: Fence,
        evidence: Vec<u8>,
        payload: bytes::Bytes,
    },
    ProveOriginal {
        stream: StreamId,
        at: Lsn,
    },
    /// The keeper's own status, with its replica of `stream`.
    KeeperStatus(StreamId),
    /// A writer asks the leader to hand `stream` to `keeper`, a voter in the
    /// writer's own failure domain.
    PreferLeader {
        stream: StreamId,
        keeper: uuid::Uuid,
    },
    /// The survivor of an operator recovery stages an installed empty copy
    /// on one of its two replacements.
    StageRecovered {
        genesis: Genesis,
        stage: Stage,
    },
    /// An administrator clears the recovery fence of `stream`.
    AcknowledgeRecovery(StreamId),
    /// A writer whose append went unanswered and whose retry was refused
    /// asks whether a writer of `fence`'s epoch committed exactly
    /// `payloads` from `at`. Added last, so an older keeper refuses it
    /// and the writer reports the outcome unknown.
    Written {
        stream: StreamId,
        fence: Fence,
        at: Lsn,
        payloads: Vec<bytes::Bytes>,
    },
    /// A keeper about to vote in `stream` asks another keeper for the
    /// configuration its own copy finalized, open or parked, without a
    /// leader. Added last; an older keeper refuses it.
    LocalConfiguration(StreamId),
}

impl Request {
    pub fn stream(&self) -> StreamId {
        match *self {
            Self::Claim(ref genesis) => genesis.stream,
            Self::ReadAt { ref genesis, .. } => genesis.stream,
            Self::StageReplica { ref genesis, .. }
            | Self::InstallReplica { ref genesis, .. }
            | Self::StageRecovered { ref genesis, .. } => genesis.stream,
            Self::Locate(stream)
            | Self::Bootstrap(stream)
            | Self::Create(stream)
            | Self::Head(stream)
            | Self::PlacementProof(stream)
            | Self::LocalCopy(stream)
            | Self::Delete(stream)
            | Self::KeeperStatus(stream)
            | Self::AcknowledgeRecovery(stream)
            | Self::LocalConfiguration(stream)
            | Self::Configuration(stream) => stream,
            Self::Stage(ref stage) => stage.stream,
            Self::Seal { stream, .. }
            | Self::Append { stream, .. }
            | Self::AppendBatch { stream, .. }
            | Self::StageOriginal { stream, .. }
            | Self::AppendOriginal { stream, .. }
            | Self::ProveOriginal { stream, .. }
            | Self::Read { stream, .. }
            | Self::Trim { stream, .. }
            | Self::RetireCopy { stream, .. }
            | Self::PreferLeader { stream, .. }
            | Self::Written { stream, .. }
            | Self::Replace { stream, .. } => stream,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub(super) enum Frame {
    Client(Request),
    Peer(Genesis, PeerRequest),
    /// A keeper-level liveness ping on the control lane, carrying the
    /// sender's media incarnation and answered with a `Pong`.
    Liveness(uuid::Uuid),
}

/// The answer to a liveness ping.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub(super) struct Pong {
    /// The receiver's keeper-wide status.
    pub status: KeeperStatus,
    /// The receiver's media incarnation.
    pub incarnation: uuid::Uuid,
    /// The incarnation the receiver first saw the sender under, `None` on
    /// their first contact.
    pub known_as: Option<uuid::Uuid>,
}

#[derive(Serialize, Deserialize)]
pub(super) enum PeerRequest {
    Append(#[serde(deserialize_with = "bounded_append")] AppendEntriesRequest<RaftTypes>),
    Vote(VoteRequest<RaftTypes>),
    Snapshot(SnapshotChunk, [u8; 32]),
    PreVote(VoteRequest<RaftTypes>),
    TransferLeader(openraft::raft::TransferLeaderRequest<RaftTypes>),
    /// The leader asks a follower holding exactly `last` under `vote` to park
    /// the idle stream.
    Park {
        vote: Vote,
        last: Option<LogId>,
    },
}

/// One chunk of a snapshot transfer, in the OpenRaft 0.9
/// `InstallSnapshotRequest` layout.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct SnapshotChunk {
    pub vote: Vote,
    pub meta: SnapshotMeta,
    pub offset: u64,
    pub data: Vec<u8>,
    pub done: bool,
}

/// The receiver holds no transfer that `got` continues; the sender restarts
/// from offset zero.
#[derive(Debug, Serialize, Deserialize)]
pub(super) struct SnapshotMismatch {
    pub expect: u64,
    pub got: u64,
}

impl fmt::Display for SnapshotMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "snapshot chunk at {} does not continue the transfer at {}",
            self.got, self.expect
        )
    }
}

impl std::error::Error for SnapshotMismatch {}

pub(super) type ChunkReply =
    Result<SnapshotResponse<RaftTypes>, RaftError<RaftTypes, SnapshotMismatch>>;

impl PeerRequest {
    pub fn lane(&self) -> Lane {
        let (kind, application) = match self {
            Self::Append(request) => (PeerKind::Append, has_application_entries(&request.entries)),
            Self::Vote(_) | Self::PreVote(_) | Self::TransferLeader(_) | Self::Park { .. } => {
                (PeerKind::Vote, false)
            }
            Self::Snapshot(..) => (PeerKind::Snapshot, false),
        };
        match decisions::peer_lane(kind, application) {
            PeerLane::Control => Lane::Control,
            PeerLane::Replication => Lane::Replication,
            PeerLane::Bulk => Lane::Bulk,
        }
    }

    pub fn sender(&self) -> Option<NodeId> {
        match self {
            Self::Append(request) => Some(request.vote.leader_id().voted_for),
            Self::Vote(request) | Self::PreVote(request) => {
                Some(request.vote.leader_id().voted_for)
            }
            Self::TransferLeader(request) => Some(request.from_leader().leader_id().voted_for),
            Self::Park { vote, .. } => Some(vote.leader_id().voted_for),
            Self::Snapshot(request, _) => Some(request.vote.leader_id().voted_for),
        }
    }
}

pub(super) fn has_application_entries(entries: &[Entry]) -> bool {
    let kinds = entries
        .iter()
        .map(|entry| match &entry.payload {
            EntryPayload::Blank => EntryKind::Blank,
            EntryPayload::Membership(_) => EntryKind::Membership,
            EntryPayload::Normal(command) => match command.body() {
                Command::Stage(_) | Command::StageOwned(_) => EntryKind::Staging,
                _ => EntryKind::Application,
            },
        })
        .collect::<Vec<_>>();
    decisions::carries_application(&kinds)
}

fn bounded_append<'de, D: Deserializer<'de>>(
    decoder: D,
) -> Result<AppendEntriesRequest<RaftTypes>, D::Error> {
    // This field order is the pinned OpenRaft 0.9 AppendEntries wire layout.
    #[derive(Deserialize)]
    struct Append {
        vote: Vote,
        prev_log_id: Option<LogId>,
        #[serde(deserialize_with = "bounded_entries")]
        entries: Vec<Entry>,
        leader_commit: Option<LogId>,
    }
    let Append {
        vote,
        prev_log_id,
        entries,
        leader_commit,
    } = Append::deserialize(decoder)?;
    Ok(AppendEntriesRequest {
        vote,
        prev_log_id,
        entries,
        leader_commit,
    })
}

fn bounded_entries<'de, D: Deserializer<'de>>(decoder: D) -> Result<Vec<Entry>, D::Error> {
    struct Entries;
    impl<'de> Visitor<'de> for Entries {
        type Value = Vec<Entry>;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "at most {MAX_PEER_ENTRIES} Raft entries")
        }
        fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<Self::Value, S::Error> {
            if seq
                .size_hint()
                .is_some_and(|count| count > MAX_PEER_ENTRIES)
            {
                return Err(de::Error::custom("too many peer append entries"));
            }
            let mut entries = Vec::new();
            while let Some(entry) = seq.next_element()? {
                if entries.len() == MAX_PEER_ENTRIES {
                    return Err(de::Error::custom("too many peer append entries"));
                }
                entries.push(entry);
            }
            Ok(entries)
        }
    }
    decoder.deserialize_seq(Entries)
}

/// A valid batch that exceeds its lane is split at the sender, so the
/// receiver never needs to allocate it. A single oversized entry cannot be
/// split and stays unreachable. `size` includes the message's batch header.
fn fit_append(lane: Lane, size: u64, count: usize) -> Result<Option<usize>, RPCError<RaftTypes>> {
    match decisions::fit_append(size, lane.frame_limit(), count, MAX_PEER_ENTRIES) {
        AppendFit::Fits => Ok(None),
        AppendFit::Split(hint) => Ok(Some(hint)),
        AppendFit::Unfit => Err(unreachable(&invalid("peer append cannot fit its lane")).into()),
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub(super) enum AppendReply {
    Raft(Result<AppendEntriesResponse<RaftTypes>, RaftError<RaftTypes>>),
    Busy,
}

#[derive(Clone, Serialize, Deserialize)]
pub(super) enum Reply {
    Decision(Outcome),
    Leader(Option<uuid::Uuid>),
    Catalog(Genesis, Vec<uuid::Uuid>),
    Staged(Stage),
    Placement(Proof),
    Generation(u64),
    ScopedPage {
        genesis: Genesis,
        configuration: Option<super::Configuration>,
        outcome: Outcome,
    },
    Status(super::KeeperStatus),
    /// The configuration a keeper's own copy finalized, if it holds one.
    /// Added last.
    Configured(Option<super::Configuration>),
}

#[derive(Clone, Serialize, Deserialize)]
pub(super) struct Proof {
    pub genesis: Genesis,
    pub configuration: super::Configuration,
    pub joint: Option<[uuid::Uuid; 3]>,
    pub stage: Option<Stage>,
}

pub(super) async fn receive<T: DeserializeOwned>(
    channel: &mut (impl AsyncRead + Unpin),
    limit: u64,
) -> io::Result<T> {
    let size = receive_size(channel, limit).await?;
    receive_body(channel, size).await
}

pub(super) async fn receive_size(
    channel: &mut (impl AsyncRead + Unpin),
    limit: u64,
) -> io::Result<usize> {
    let size = u64::from(channel.read_u32().await?);
    if size == 0 || size > limit {
        return Err(invalid("invalid consensus frame length"));
    }
    Ok(size as usize)
}

pub(super) async fn receive_body<T: DeserializeOwned>(
    channel: &mut (impl AsyncRead + Unpin),
    size: usize,
) -> io::Result<T> {
    let mut body = vec![0; size];
    channel.read_exact(&mut body).await?;
    decode(&body)
}

pub(super) async fn send<T: Serialize>(
    channel: &mut (impl AsyncWrite + Unpin),
    message: &T,
) -> io::Result<()> {
    send_encoded(channel, &encode(message)?).await
}

pub(super) async fn send_encoded(
    channel: &mut (impl AsyncWrite + Unpin),
    bytes: &[u8],
) -> io::Result<()> {
    channel.write_u32(bytes.len() as u32).await?;
    channel.write_all(bytes).await?;
    channel.flush().await
}

// The control and replication lanes carry batch frames. A frame is the usual
// 4-byte length and a body of messages, each an 8-byte request id, a 4-byte
// length and an encoded `Frame`. The receiver answers each message under its
// id, in batch frames of replies: the id, a status byte (0 for an encoded
// reply, 1 for a failure text), a 4-byte length and the bytes. Replies may
// arrive in any order.

/// Bytes ahead of each message in a batch frame.
pub(super) const MESSAGE_HEADER: usize = 12;
/// Messages in one batch frame. A frame closes at this many, when the next
/// message would pass the lane's frame limit, or when the queue is empty
/// after the writer yielded once for more, which it does only within
/// `FLUSH_WINDOW` of the first message. The writer never sleeps on an empty
/// queue: tokio timers round up to the next millisecond, which cost every
/// message about that much.
pub(super) const BATCH_MESSAGES: usize = 256;
const FLUSH_WINDOW: Duration = Duration::from_millis(1);
/// A reply batch stops growing past this size.
pub(super) const REPLY_BATCH_BYTES: usize = 1024 * 1024;

/// A frame under construction, with room for its length.
pub(super) fn batch_frame() -> Vec<u8> {
    vec![0; 4]
}

/// Fills in the length of a frame from `batch_frame` and returns its bytes.
pub(super) fn seal_frame(frame: &mut [u8]) -> &[u8] {
    let size = (frame.len() - 4) as u32;
    frame[..4].copy_from_slice(&size.to_be_bytes());
    frame
}

fn push_message(frame: &mut Vec<u8>, id: u64, message: &[u8]) {
    frame.extend_from_slice(&id.to_be_bytes());
    frame.extend_from_slice(&(message.len() as u32).to_be_bytes());
    frame.extend_from_slice(message);
}

pub(super) fn push_reply(frame: &mut Vec<u8>, id: u64, reply: &Result<Vec<u8>, String>) {
    let (status, bytes) = match reply {
        Ok(bytes) => (0, bytes.as_slice()),
        Err(text) => (1, text.as_bytes()),
    };
    frame.extend_from_slice(&id.to_be_bytes());
    frame.push(status);
    frame.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    frame.extend_from_slice(bytes);
}

fn take<'a>(body: &mut &'a [u8], count: usize) -> io::Result<&'a [u8]> {
    if body.len() < count {
        return Err(invalid("truncated peer batch"));
    }
    let (head, rest) = body.split_at(count);
    *body = rest;
    Ok(head)
}

fn take_u32(body: &mut &[u8]) -> io::Result<usize> {
    Ok(u32::from_be_bytes(take(body, 4)?.try_into().unwrap()) as usize)
}

fn take_u64(body: &mut &[u8]) -> io::Result<u64> {
    Ok(u64::from_be_bytes(take(body, 8)?.try_into().unwrap()))
}

/// Splits a batch frame body into its messages.
pub(super) fn messages(mut body: &[u8]) -> io::Result<Vec<(u64, &[u8])>> {
    let mut messages = Vec::new();
    while !body.is_empty() {
        if messages.len() == BATCH_MESSAGES {
            return Err(invalid("too many messages in a peer batch"));
        }
        let id = take_u64(&mut body)?;
        let size = take_u32(&mut body)?;
        messages.push((id, take(&mut body, size)?));
    }
    Ok(messages)
}

fn replies(mut body: &[u8]) -> io::Result<Vec<(u64, Result<&[u8], &[u8]>)>> {
    let mut replies = Vec::new();
    while !body.is_empty() {
        let id = take_u64(&mut body)?;
        let status = take(&mut body, 1)?[0];
        let size = take_u32(&mut body)?;
        let bytes = take(&mut body, size)?;
        replies.push((
            id,
            match status {
                0 => Ok(bytes),
                1 => Err(bytes),
                _ => return Err(invalid("invalid peer reply status")),
            },
        ));
    }
    Ok(replies)
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RpcFault {
    /// Deliver normally.
    Allow,
    /// Drop before sending (optional delay before returning error).
    Drop(Duration),
    /// Delay before sending.
    Delay(Duration),
    /// Deliver to the receiver, then discard the reply so the caller sees an
    /// ambiguous transport failure.
    DropReply(Duration),
    /// Deliver normally, and also send a duplicate copy after `Duration` when
    /// the frame is an idempotent peer message.
    Duplicate(Duration),
}

#[cfg(test)]
pub(super) type TransportFilter =
    Arc<dyn Fn(uuid::Uuid, uuid::Uuid, Lane) -> RpcFault + Send + Sync>;

#[derive(Clone)]
pub(super) struct Rpc {
    inner: Arc<Connections>,
}

struct Connections {
    tls: TlsConnector,
    keepers: Keepers,
    idle: Mutex<HashMap<uuid::Uuid, Vec<Channel>>>,
    /// In-flight snapshot chunks per target on the bulk lane.
    in_flight: Mutex<HashMap<uuid::Uuid, Arc<Semaphore>>>,
    /// The multiplexed channel to each target on the control and
    /// replication lanes.
    channels: Mutex<HashMap<uuid::Uuid, Arc<PeerChannel>>>,
    /// Batch frames written on multiplexed channels.
    frames: AtomicU64,
    lane: Lane,
    /// Replaces the TLS connection to every target in unit tests.
    #[cfg(test)]
    dial: Mutex<Option<Arc<dyn Fn() -> tokio::io::DuplexStream + Send + Sync>>>,
    /// Fault filter `(sender_id, filter)` for fault-injection tests.
    #[cfg(test)]
    filter: Mutex<Option<(uuid::Uuid, TransportFilter)>>,
}

const PEER_IN_FLIGHT: usize = 16;
const POOLED_CHANNELS: usize = 16;
/// A multiplexed channel with nothing in flight closes after this long,
/// before the receiver's 60 s idle limit can race a new message.
const CHANNEL_IDLE: Duration = Duration::from_secs(30);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(3);

/// One long-lived connection to a target on a multiplexed lane, opened on
/// first use and again after it fails. Each sender keeps at most the
/// receiver's per-sender share of messages in flight and queues the rest.
struct PeerChannel {
    permits: Arc<Semaphore>,
    queue: Mutex<Option<mpsc::UnboundedSender<Outgoing>>>,
}

/// A message on its way to the writer. Its permit is held until the reply
/// arrives or the connection fails, even if the caller gave up, so the
/// sender never exceeds the receiver's share.
struct Outgoing {
    message: Vec<u8>,
    permit: OwnedSemaphorePermit,
    reply: oneshot::Sender<Answer>,
}

enum Answer {
    Reply(Vec<u8>),
    Failed(io::Error),
    /// The connection closed before writing the message, so a fresh one may
    /// send it.
    NotSent(Vec<u8>, OwnedSemaphorePermit),
}

type Waiting = Mutex<HashMap<u64, (oneshot::Sender<Answer>, OwnedSemaphorePermit)>>;

fn closed() -> io::Error {
    io::Error::new(io::ErrorKind::ConnectionAborted, "peer connection closed")
}

impl Connections {
    async fn connect(
        &self,
        target: uuid::Uuid,
        address: &std::net::SocketAddr,
    ) -> io::Result<Channel> {
        let (peer, channel) =
            connect_protocol(&self.tls, &address.to_string(), self.lane.alpn()).await?;
        if peer.0 != target.as_u128() {
            return Err(invalid("keeper certificate does not match route"));
        }
        Ok(channel)
    }

    async fn run(
        self: Arc<Self>,
        target: uuid::Uuid,
        address: std::net::SocketAddr,
        queue: mpsc::UnboundedReceiver<Outgoing>,
    ) {
        #[cfg(test)]
        let dial = self.dial.lock().clone();
        #[cfg(test)]
        if let Some(dial) = dial {
            return self.drive(Ok(dial()), queue).await;
        }
        let connected = timeout(CONNECT_TIMEOUT, self.connect(target, &address))
            .await
            .unwrap_or_else(|elapsed| Err(elapsed.into()));
        self.drive(connected, queue).await
    }

    /// Runs one multiplexed connection until it fails or idles out. Written
    /// messages then fail and unwritten ones are handed back unsent.
    async fn drive<S: AsyncRead + AsyncWrite>(
        &self,
        connected: io::Result<S>,
        mut queue: mpsc::UnboundedReceiver<Outgoing>,
    ) {
        let waiting = Waiting::default();
        let mut carry = None;
        let refused = match connected {
            Err(error) => Some(error),
            Ok(channel) => {
                let (read, write) = tokio::io::split(channel);
                tokio::select! {
                    _ = self.write_batches(write, &mut queue, &mut carry, &waiting) => {}
                    _ = read_replies(read, &waiting) => {}
                }
                None
            }
        };
        queue.close();
        for (_, (reply, _)) in waiting.lock().drain() {
            let _ = reply.send(Answer::Failed(closed()));
        }
        let unsent = carry
            .into_iter()
            .chain(std::iter::from_fn(|| queue.try_recv().ok()));
        for outgoing in unsent {
            let answer = match &refused {
                Some(error) => Answer::Failed(io::Error::new(error.kind(), error.to_string())),
                None => Answer::NotSent(outgoing.message, outgoing.permit),
            };
            let _ = outgoing.reply.send(answer);
        }
    }

    async fn write_batches(
        &self,
        mut write: WriteHalf<impl AsyncWrite>,
        queue: &mut mpsc::UnboundedReceiver<Outgoing>,
        carry: &mut Option<Outgoing>,
        waiting: &Waiting,
    ) -> io::Result<()> {
        let limit = self.lane.frame_limit() as usize + 4;
        let mut next = 0u64;
        loop {
            let first = match carry.take() {
                Some(outgoing) => outgoing,
                None => match timeout(CHANNEL_IDLE, queue.recv()).await {
                    Ok(Some(outgoing)) => outgoing,
                    Ok(None) => return Ok(()),
                    Err(_) if waiting.lock().is_empty() => return Ok(()),
                    Err(_) => continue,
                },
            };
            let window = Instant::now() + FLUSH_WINDOW;
            let mut frame = batch_frame();
            let mut count = 0;
            let mut pending = Some(first);
            let mut yielded = false;
            loop {
                let outgoing = match pending.take() {
                    Some(outgoing) => outgoing,
                    None => match queue.try_recv() {
                        Ok(outgoing) => outgoing,
                        // Tasks woken together, such as the heartbeats of
                        // many streams, queue while the writer yields once.
                        Err(mpsc::error::TryRecvError::Empty)
                            if !yielded && Instant::now() < window =>
                        {
                            yielded = true;
                            tokio::task::yield_now().await;
                            continue;
                        }
                        Err(_) => break,
                    },
                };
                // A caller that gave up before the write needs no message.
                if outgoing.reply.is_closed() {
                    continue;
                }
                if count > 0 && frame.len() + MESSAGE_HEADER + outgoing.message.len() > limit {
                    *carry = Some(outgoing);
                    break;
                }
                push_message(&mut frame, next, &outgoing.message);
                waiting
                    .lock()
                    .insert(next, (outgoing.reply, outgoing.permit));
                next += 1;
                count += 1;
                if count == BATCH_MESSAGES {
                    break;
                }
            }
            if count == 0 {
                continue;
            }
            write.write_all(seal_frame(&mut frame)).await?;
            write.flush().await?;
            self.frames.fetch_add(1, Ordering::Relaxed);
        }
    }
}

async fn read_replies(mut read: ReadHalf<impl AsyncRead>, waiting: &Waiting) -> io::Result<()> {
    loop {
        let size = receive_size(&mut read, MAX_MESSAGE).await?;
        let mut body = vec![0; size];
        read.read_exact(&mut body).await?;
        let replies = replies(&body)?;
        let mut waiting = waiting.lock();
        for (id, reply) in replies {
            // A caller that timed out drops its late reply here.
            if let Some((sender, _permit)) = waiting.remove(&id) {
                let _ = sender.send(match reply {
                    Ok(bytes) => Answer::Reply(bytes.to_vec()),
                    Err(text) => {
                        Answer::Failed(io::Error::other(String::from_utf8_lossy(text).into_owned()))
                    }
                });
            }
        }
    }
}

impl PeerChannel {
    fn new(lane: Lane) -> Self {
        let share = match lane {
            Lane::Replication => decisions::SENDER_FRAMES,
            _ => decisions::CONTROL_PER_SENDER,
        };
        Self {
            permits: Arc::new(Semaphore::new(share)),
            queue: Mutex::default(),
        }
    }
}

impl Rpc {
    pub fn new(tls: TlsConnector, keepers: Keepers, lane: Lane) -> Self {
        Self {
            inner: Arc::new(Connections {
                tls,
                keepers,
                idle: Mutex::default(),
                in_flight: Mutex::default(),
                channels: Mutex::default(),
                frames: AtomicU64::new(0),
                lane,
                #[cfg(test)]
                dial: Mutex::default(),
                #[cfg(test)]
                filter: Mutex::default(),
            }),
        }
    }

    #[cfg(test)]
    pub fn set_filter(&self, source: uuid::Uuid, filter: Option<TransportFilter>) {
        *self.inner.filter.lock() = filter.map(|f| (source, f));
    }

    pub fn keepers(&self) -> &Keepers {
        &self.inner.keepers
    }

    pub async fn call<T: DeserializeOwned>(
        &self,
        target: uuid::Uuid,
        request: Frame,
        deadline: Duration,
    ) -> io::Result<T> {
        #[cfg(test)]
        let action = self
            .inner
            .filter
            .lock()
            .as_ref()
            .map(|(source, filter)| filter(*source, target, self.inner.lane))
            .unwrap_or(RpcFault::Allow);
        #[cfg(test)]
        match action {
            RpcFault::Allow => {}
            RpcFault::Drop(delay) => {
                if !delay.is_zero() {
                    timeout(deadline, tokio::time::sleep(delay)).await?;
                }
                return Err(io::Error::new(
                    io::ErrorKind::ConnectionReset,
                    "injected network drop",
                ));
            }
            RpcFault::Delay(delay) => {
                return timeout(deadline, async {
                    if !delay.is_zero() {
                        tokio::time::sleep(delay).await;
                    }
                    self.exchange(target, request).await
                })
                .await?;
            }
            RpcFault::DropReply(delay) => {
                let _ = timeout(deadline, async {
                    let _ = self.exchange::<T>(target, request).await;
                    if !delay.is_zero() {
                        tokio::time::sleep(delay).await;
                    }
                })
                .await;
                return Err(io::Error::new(
                    io::ErrorKind::ConnectionReset,
                    "injected reply drop",
                ));
            }
            RpcFault::Duplicate(delay) => {
                if matches!(request, Frame::Peer(..))
                    && let Ok(encoded) = encode(&request)
                {
                    let dup = self.clone();
                    tokio::spawn(async move {
                        if !delay.is_zero() {
                            tokio::time::sleep(delay).await;
                        }
                        let _ = timeout(deadline, dup.send_duplicate(target, encoded)).await;
                    });
                }
            }
        }
        timeout(deadline, self.exchange(target, request)).await?
    }

    #[cfg(test)]
    async fn send_duplicate(&self, target: uuid::Uuid, encoded: Vec<u8>) -> io::Result<()> {
        let frame: Frame = decode(&encoded)?;
        let address = *self
            .keepers()
            .get(&target)
            .ok_or_else(|| invalid("unknown keeper"))?;
        match self.inner.lane {
            Lane::Control | Lane::Replication => {
                let _ = self.multiplexed(target, address, &frame).await;
            }
            Lane::Bulk => {
                let _ = self.exchange::<ChunkReply>(target, frame).await;
            }
            Lane::Application => {
                let _ = self.exchange::<Reply>(target, frame).await;
            }
        }
        Ok(())
    }

    /// Batch frames this client has written on multiplexed channels.
    #[cfg(test)]
    pub fn frames(&self) -> u64 {
        self.inner.frames.load(Ordering::Relaxed)
    }

    async fn exchange<T: DeserializeOwned>(
        &self,
        target: uuid::Uuid,
        request: Frame,
    ) -> io::Result<T> {
        let address = self
            .keepers()
            .get(&target)
            .ok_or_else(|| invalid("unknown keeper"))?;
        if matches!(self.inner.lane, Lane::Control | Lane::Replication) {
            return decode(&self.multiplexed(target, *address, &request).await?);
        }
        let peer_lane = self.inner.lane != Lane::Application;
        let _permit = if peer_lane {
            let permits = self
                .inner
                .in_flight
                .lock()
                .entry(target)
                .or_insert_with(|| Arc::new(Semaphore::new(PEER_IN_FLIGHT)))
                .clone();
            Some(permits.acquire_owned().await.map_err(io::Error::other)?)
        } else {
            None
        };
        let cached = self.inner.idle.lock().get_mut(&target).and_then(Vec::pop);
        let reused = cached.is_some();
        let mut channel = match cached {
            Some(channel) => channel,
            None => self.connect(target, address).await?,
        };
        let mut result = Self::round_trip(&mut channel, &request).await;
        // The receiver may have closed an idle pooled connection. Peer
        // messages are idempotent, so they retry once on a fresh one.
        if result.is_err() && reused && peer_lane {
            channel = self.connect(target, address).await?;
            result = Self::round_trip(&mut channel, &request).await;
        }
        let result = result?;
        let mut idle = self.inner.idle.lock();
        let idle = idle.entry(target).or_default();
        if idle.len() < POOLED_CHANNELS {
            idle.push(channel);
        }
        Ok(result)
    }

    async fn connect(
        &self,
        target: uuid::Uuid,
        address: &std::net::SocketAddr,
    ) -> io::Result<Channel> {
        self.inner.connect(target, address).await
    }

    /// Sends one message on the target's multiplexed channel and waits for
    /// its reply. A message the connection closed before writing goes once
    /// more on a fresh connection.
    async fn multiplexed(
        &self,
        target: uuid::Uuid,
        address: std::net::SocketAddr,
        request: &Frame,
    ) -> io::Result<Vec<u8>> {
        let mut message = encode(request)?;
        if (message.len() + MESSAGE_HEADER) as u64 > self.inner.lane.frame_limit() {
            return Err(invalid("peer message exceeds its lane"));
        }
        let channel = self
            .inner
            .channels
            .lock()
            .entry(target)
            .or_insert_with(|| Arc::new(PeerChannel::new(self.inner.lane)))
            .clone();
        let mut permit = channel
            .permits
            .clone()
            .acquire_owned()
            .await
            .map_err(io::Error::other)?;
        for _ in 0..2 {
            let (reply, answer) = oneshot::channel();
            let outgoing = Outgoing {
                message,
                permit,
                reply,
            };
            {
                let mut queue = channel.queue.lock();
                if queue.as_ref().is_none_or(mpsc::UnboundedSender::is_closed) {
                    let (sender, receiver) = mpsc::unbounded_channel();
                    tokio::spawn(self.inner.clone().run(target, address, receiver));
                    *queue = Some(sender);
                }
                if let Err(mpsc::error::SendError(outgoing)) =
                    queue.as_ref().expect("open channel").send(outgoing)
                {
                    queue.take();
                    (message, permit) = (outgoing.message, outgoing.permit);
                    continue;
                }
            }
            match answer.await {
                Ok(Answer::Reply(reply)) => return Ok(reply),
                Ok(Answer::Failed(error)) => return Err(error),
                Ok(Answer::NotSent(unsent, held)) => (message, permit) = (unsent, held),
                Err(_) => return Err(closed()),
            }
        }
        Err(closed())
    }

    async fn round_trip<T: DeserializeOwned>(
        channel: &mut Channel,
        request: &Frame,
    ) -> io::Result<T> {
        send(channel, request).await?;
        receive(channel, MAX_MESSAGE).await
    }
}

/// The refusal a replica sends a peer that `decisions::excludes_sender`
/// excludes, instead of an answer that carries its newer vote.
pub(super) const EXCLUDED: &str = "sender is outside the receiver's placement";

#[derive(Clone)]
pub(super) struct Network {
    pub control: Rpc,
    pub replication: Rpc,
    pub bulk: Rpc,
    pub snapshot_rate: Arc<RateLimiter>,
    pub genesis: Genesis,
    pub state: StateMachine,
    pub split_vote: watch::Sender<Option<Vote>>,
    /// The last peer that excluded this replica, and the keeper's wake-up
    /// for an immediate retirement check.
    pub excluded: Arc<Mutex<Option<uuid::Uuid>>>,
    pub retire: Arc<tokio::sync::Notify>,
    /// Peers this keeper saw under another media incarnation. Their vote
    /// and pre-vote grants do not count.
    pub reincarnated: Arc<parking_lot::RwLock<HashSet<NodeId>>>,
}

impl Network {
    /// Refuses a grant from a peer seen under another incarnation, as if the
    /// peer had not answered.
    fn check_grant(
        &self,
        target: NodeId,
        response: VoteResponse<RaftTypes>,
    ) -> Result<VoteResponse<RaftTypes>, RPCError<RaftTypes>> {
        if response.vote_granted
            && !decisions::counts_grant(true, self.reincarnated.read().contains(&target))
        {
            return Err(unreachable(&invalid("vote grant from a reincarnated keeper")).into());
        }
        Ok(response)
    }

    fn observe(&self, target: NodeId, error: &io::Error) {
        if error.to_string().contains(EXCLUDED) {
            *self.excluded.lock() = Some(uuid::Uuid::from_u128(target));
            self.retire.notify_one();
        }
    }
}

pub(super) struct Peer {
    network: Network,
    target: NodeId,
}

/// Paces the bytes a keeper sends in snapshot transfers, across all its
/// streams, so catch-up and repair cannot saturate a cross-zone link. A
/// rate of zero sends without pacing.
pub(super) struct RateLimiter {
    bytes_per_second: u64,
    next: tokio::sync::Mutex<tokio::time::Instant>,
}

impl RateLimiter {
    pub fn new(bytes_per_second: u64) -> Arc<Self> {
        Arc::new(Self {
            bytes_per_second,
            next: tokio::sync::Mutex::new(tokio::time::Instant::now()),
        })
    }

    /// Waits until `bytes` more fit under the rate.
    pub async fn take(&self, bytes: u64) {
        if self.bytes_per_second == 0 || bytes == 0 {
            return;
        }
        let cost = Duration::from_secs_f64(bytes as f64 / self.bytes_per_second as f64);
        let start = {
            let mut next = self.next.lock().await;
            let start = (*next).max(tokio::time::Instant::now());
            *next = start + cost;
            start
        };
        tokio::time::sleep_until(start).await;
    }
}

impl RaftNetworkFactory<RaftTypes> for Network {
    type Network = Peer;

    async fn new_client(&mut self, target: NodeId, _: &BasicNode) -> Peer {
        Peer {
            network: self.clone(),
            target,
        }
    }
}

fn unreachable(error: &(impl std::error::Error + 'static)) -> Unreachable<RaftTypes> {
    Unreachable::new(error)
}

impl Peer {
    async fn request<T: DeserializeOwned>(
        &self,
        request: PeerRequest,
        option: &RPCOption,
    ) -> Result<T, RPCError<RaftTypes>> {
        if !self.network.state.active() {
            return Err(unreachable(&invalid("quarantined stream replica")).into());
        }
        let rpc = match request.lane() {
            Lane::Bulk => &self.network.bulk,
            Lane::Control => &self.network.control,
            Lane::Replication => &self.network.replication,
            Lane::Application => unreachable!("peer request on application lane"),
        };
        let frame = Frame::Peer(self.network.genesis.clone(), request);
        rpc.call(uuid::Uuid::from_u128(self.target), frame, option.hard_ttl())
            .await
            .map_err(|error| {
                self.network.observe(self.target, &error);
                unreachable(&error).into()
            })
    }

    /// Sends one AppendEntries that fits its lane.
    async fn append_part(
        &self,
        range: (Option<LogId>, Option<LogId>),
        lane: Lane,
        frame: Frame,
        option: &RPCOption,
    ) -> Result<AppendResult<RaftTypes>, RPCError<RaftTypes>> {
        #[cfg(feature = "consensus-testing")]
        if let Some(delay) = injected_peer_delay() {
            tokio::time::sleep(delay).await;
        }
        let rpc = if lane == Lane::Replication {
            &self.network.replication
        } else {
            &self.network.control
        };
        match rpc
            .call(uuid::Uuid::from_u128(self.target), frame, option.hard_ttl())
            .await
        {
            Ok(AppendReply::Raft(Ok(reply))) => Ok(reply.into_append_result(range.0, range.1)),
            Ok(AppendReply::Raft(Err(error))) => Err(unreachable(&error).into()),
            Ok(AppendReply::Busy) => {
                super::metrics::count(&super::metrics::COUNTERS.peer_busy);
                Err(unreachable(&io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "replication receiver is busy",
                ))
                .into())
            }
            Err(error) => {
                self.network.observe(self.target, &error);
                super::metrics::count(&super::metrics::COUNTERS.peer_unreachable);
                super::metrics::sample("peer.unreachable", || format!("{error:?}"));
                Err(unreachable(&error).into())
            }
        }
    }
}

/// Consecutive failures of one snapshot chunk before the transfer fails.
const SNAPSHOT_CHUNK_MAX_RETRIES: u64 = 5;
const SNAPSHOT_CHUNK_RETRY_BASE: Duration = Duration::from_millis(10);
const SNAPSHOT_CHUNK_RETRY_MAX: Duration = Duration::from_millis(200);

fn snapshot_chunk_retry_delay(failures: u64) -> Duration {
    let shift = failures.saturating_sub(1).min(4) as u32;
    SNAPSHOT_CHUNK_RETRY_BASE
        .saturating_mul(2u32.saturating_pow(shift))
        .min(SNAPSHOT_CHUNK_RETRY_MAX)
}

impl RaftNetworkV2<RaftTypes> for Peer {
    type SnapshotData = Box<SnapshotFile>;

    fn backoff(&self) -> Option<Backoff> {
        Some(Backoff::new(peer_backoff()))
    }

    /// A request that exceeds its lane goes out in parts, each chained to the
    /// part before it. A failure after an accepted part reports that part as
    /// the follower's progress, and OpenRaft sends the rest again.
    async fn append_entries(
        &mut self,
        request: AppendEntriesRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<AppendResult<RaftTypes>, RPCError<RaftTypes>> {
        if !self.network.state.active() {
            return Err(unreachable(&invalid("quarantined stream replica")).into());
        }
        let mut request = request;
        let mut rest = Vec::new();
        let mut accepted = None;
        loop {
            let count = request.entries.len();
            let (vote, leader_commit) = (request.vote, request.leader_commit);
            let range = (request.prev_log_id, request.last_log_id());
            let message = PeerRequest::Append(request);
            let lane = message.lane();
            let frame = Frame::Peer(self.network.genesis.clone(), message);
            let fit = options()
                .serialized_size(&frame)
                .map_err(|error| unreachable(&error).into())
                .and_then(|size| fit_append(lane, size + MESSAGE_HEADER as u64, count));
            match fit {
                Ok(None) => (),
                Ok(Some(hint)) => {
                    let Frame::Peer(_, PeerRequest::Append(mut part)) = frame else {
                        unreachable!("an append frame holds its request");
                    };
                    rest.splice(0..0, part.entries.split_off(hint));
                    request = part;
                    continue;
                }
                Err(error) => return accepted.map(Ok).ok_or(error),
            }
            match (
                self.append_part(range, lane, frame, &option).await,
                accepted,
            ) {
                (Ok(Ok(matched)), _) if !rest.is_empty() => {
                    accepted = Some(matched);
                    request = AppendEntriesRequest {
                        vote,
                        prev_log_id: matched,
                        entries: std::mem::take(&mut rest),
                        leader_commit,
                    };
                }
                (Ok(Err(AppendError::Conflict { .. })) | Err(_), Some(matched)) => {
                    return Ok(Ok(matched));
                }
                (result, _) => return result,
            }
        }
    }

    async fn vote(
        &mut self,
        request: VoteRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<VoteResponse<RaftTypes>, RPCError<RaftTypes>> {
        let proposed = request.vote;
        let last_log = request.last_log_id;
        let response: Result<VoteResponse<RaftTypes>, RaftError<RaftTypes>> =
            self.request(PeerRequest::Vote(request), &option).await?;
        let response = response.map_err(|error| unreachable(&error))?;
        if !response.vote_granted
            && !response.vote.is_committed()
            && response.vote.leader_id().term == proposed.leader_id().term
            && response.vote != proposed
            && response.last_log_id <= last_log
        {
            // A shorter log keeps OpenRaft's normal election delay.
            self.network.split_vote.send_if_modified(|observed| {
                if *observed == Some(proposed) {
                    return false;
                }
                *observed = Some(proposed);
                true
            });
        }
        self.network.check_grant(self.target, response)
    }

    async fn pre_vote(
        &mut self,
        request: VoteRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<VoteResponse<RaftTypes>, RPCError<RaftTypes>> {
        let response: Result<VoteResponse<RaftTypes>, RaftError<RaftTypes>> =
            self.request(PeerRequest::PreVote(request), &option).await?;
        let response = response.map_err(|error| unreachable(&error))?;
        self.network.check_grant(self.target, response)
    }

    async fn transfer_leader(
        &mut self,
        request: openraft::raft::TransferLeaderRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<openraft::raft::TransferLeaderResponse<RaftTypes>, RPCError<RaftTypes>> {
        let response: Result<
            openraft::raft::TransferLeaderResponse<RaftTypes>,
            openraft::errors::Fatal<RaftTypes>,
        > = self
            .request(PeerRequest::TransferLeader(request), &option)
            .await?;
        Ok(response.map_err(|error| unreachable(&error))?)
    }

    /// Sends the snapshot in chunks on the bulk lane. A chunk that fails to
    /// arrive is retried a few times, and a receiver that lost the transfer
    /// restarts it from the first chunk.
    async fn full_snapshot(
        &mut self,
        vote: Vote,
        snapshot: openraft::type_config::alias::SnapshotOf<RaftTypes, Box<SnapshotFile>>,
        cancel: impl Future<Output = ReplicationClosed> + OptionalSend + 'static,
        option: RPCOption,
    ) -> Result<SnapshotResponse<RaftTypes>, StreamingError<RaftTypes>> {
        let mut cancel = Box::pin(cancel);
        let mut file = snapshot.snapshot;
        // A private spool is a bulk admission, so refusal must be retryable.
        // Once staged, every seek uses the same stable file.
        let end = tokio::select! {
            closed = &mut cancel => return Err(closed.into()),
            staged = file.seek(io::SeekFrom::End(0)) => {
                staged.map_err(|error| unreachable(&error))?
            }
        };
        let meta = file.meta().clone();
        let digest = self
            .network
            .state
            .snapshot_digest(&meta)
            .ok_or_else(|| unreachable(&invalid("snapshot selection changed")))?;
        let chunk_size = option
            .snapshot_chunk_size()
            .ok_or_else(|| unreachable(&invalid("snapshot chunk size is unset")))?;
        let mut offset = 0;
        let mut failures = 0;
        let mut backoff = None::<Backoff>;
        loop {
            if let Some(closed) = cancel.as_mut().now_or_never() {
                return Err(closed.into());
            }
            tokio::time::sleep(Duration::from_millis(1)).await;
            file.seek(io::SeekFrom::Start(offset))
                .await
                .map_err(|error| unreachable(&error))?;
            let mut data = Vec::with_capacity(chunk_size);
            while data.len() < data.capacity() {
                let read = file
                    .read_buf(&mut data)
                    .await
                    .map_err(|error| unreachable(&error))?;
                if read == 0 {
                    break;
                }
            }
            let read = data.len() as u64;
            let done = offset + read == end;
            self.network.snapshot_rate.take(read).await;
            let chunk = SnapshotChunk {
                vote,
                meta: meta.clone(),
                offset,
                data,
                done,
            };
            let sent = timeout(
                option.hard_ttl(),
                self.request::<ChunkReply>(PeerRequest::Snapshot(chunk, digest), &option),
            )
            .await;
            let reply = match sent {
                Err(elapsed) => return Err(NetworkError::new(&elapsed).into()),
                Ok(Ok(Ok(reply))) => {
                    failures = 0;
                    backoff = None;
                    reply
                }
                Ok(Ok(Err(RaftError::APIError(_)))) => {
                    offset = 0;
                    failures = 0;
                    backoff = None;
                    continue;
                }
                Ok(Ok(Err(RaftError::Fatal(fatal)))) => return Err(unreachable(&fatal).into()),
                Ok(Err(error)) => {
                    failures += 1;
                    if failures >= SNAPSHOT_CHUNK_MAX_RETRIES {
                        return Err(error.into());
                    }
                    let delay = if matches!(error, RPCError::Unreachable(_)) {
                        backoff
                            .get_or_insert_with(|| Backoff::new(peer_backoff()))
                            .next()
                            .unwrap_or(PEER_BACKOFF_LAST)
                    } else {
                        snapshot_chunk_retry_delay(failures)
                    };
                    tokio::time::sleep(delay).await;
                    continue;
                }
            };
            if reply.vote > vote || done {
                return Ok(reply);
            }
            offset += read;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test(start_paused = true)]
    async fn snapshot_sends_are_paced_across_streams() {
        let limiter = RateLimiter::new(1024);
        let started = tokio::time::Instant::now();
        limiter.take(1024).await;
        limiter.take(1024).await;
        limiter.take(1024).await;
        // The first kilobyte goes at once; each later one waits a second.
        assert_eq!(started.elapsed(), Duration::from_secs(2));
        let unpaced = RateLimiter::new(0);
        unpaced.take(u64::MAX).await;
        assert_eq!(started.elapsed(), Duration::from_secs(2));
    }

    #[test]
    fn refused_peer_appends_back_off_briefly_then_up_to_half_a_second() {
        let delays = peer_backoff().take(10).collect::<Vec<_>>();
        assert_eq!(delays[0], Duration::from_millis(5));
        assert_eq!(delays[1], Duration::from_millis(10));
        assert!(delays.windows(2).all(|pair| pair[0] <= pair[1]));
        assert_eq!(delays[9], Duration::from_millis(500));
    }

    #[test]
    fn an_oversized_valid_batch_is_split_at_the_sender() {
        let limit = Lane::Replication.frame_limit();
        assert!(matches!(
            fit_append(Lane::Replication, limit, MAX_PEER_ENTRIES),
            Ok(None)
        ));
        for (lane, size, count, hint) in [
            (Lane::Replication, limit + 1, 4, 2),
            (
                Lane::Replication,
                1024,
                MAX_PEER_ENTRIES + 2,
                (MAX_PEER_ENTRIES + 2) / 2,
            ),
            (Lane::Control, Lane::Control.frame_limit() + 1, 2, 1),
        ] {
            match fit_append(lane, size, count) {
                Ok(Some(split)) => assert_eq!(split, hint),
                other => panic!("expected a split, got {other:?}"),
            }
        }
        assert!(matches!(
            fit_append(Lane::Replication, limit + 1, 1),
            Err(RPCError::Unreachable(_))
        ));
    }

    /// How the fake receiver answers a message carrying `n`.
    #[derive(Clone, Copy)]
    enum Answering {
        At(Duration),
        Fail,
        Close,
    }

    /// A control-lane client whose connections reach an in-process fake
    /// receiver. Each message is a client `Head(n)` and is answered with `n`,
    /// after the delay `policy` picks, with every batch answered in reverse.
    fn muxed(
        policy: impl Fn(u128, usize) -> Answering + Send + Sync + 'static,
    ) -> (Rpc, uuid::Uuid, Arc<std::sync::atomic::AtomicUsize>) {
        use tokio_rustls::rustls::{ClientConfig, RootCertStore, crypto::ring};
        let config = ClientConfig::builder_with_provider(Arc::new(ring::default_provider()))
            .with_safe_default_protocol_versions()
            .unwrap()
            .with_root_certificates(RootCertStore::empty())
            .with_no_client_auth();
        let target = uuid::Uuid::from_u128(2);
        let keepers = Keepers::from([(target, "127.0.0.1:1".parse().unwrap())]);
        let rpc = Rpc::new(TlsConnector::from(Arc::new(config)), keepers, Lane::Control);
        let dials = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let policy = Arc::new(policy);
        *rpc.inner.dial.lock() = Some(Arc::new({
            let dials = dials.clone();
            move || {
                let dial = dials.fetch_add(1, Ordering::Relaxed);
                let (client, server) = tokio::io::duplex(1 << 20);
                tokio::spawn(fake_receiver(server, dial, policy.clone()));
                client
            }
        }));
        (rpc, target, dials)
    }

    async fn fake_receiver(
        channel: tokio::io::DuplexStream,
        dial: usize,
        policy: Arc<dyn Fn(u128, usize) -> Answering + Send + Sync>,
    ) {
        let (mut read, write) = tokio::io::split(channel);
        let write = Arc::new(tokio::sync::Mutex::new(write));
        loop {
            let Ok(size) = receive_size(&mut read, Lane::Control.frame_limit()).await else {
                return;
            };
            let mut body = vec![0; size];
            if read.read_exact(&mut body).await.is_err() {
                return;
            }
            for (id, message) in messages(&body).unwrap().into_iter().rev() {
                let Frame::Client(Request::Head(StreamId(n))) = decode(message).unwrap() else {
                    panic!("unexpected message");
                };
                let (delay, reply) = match policy(n, dial) {
                    Answering::Close => return,
                    Answering::Fail => (Duration::ZERO, Err("refused".to_owned())),
                    Answering::At(delay) => (delay, Ok(encode(&n).unwrap())),
                };
                let write = write.clone();
                tokio::spawn(async move {
                    tokio::time::sleep(delay).await;
                    let mut frame = batch_frame();
                    push_reply(&mut frame, id, &reply);
                    let _ = write.lock().await.write_all(seal_frame(&mut frame)).await;
                });
            }
        }
    }

    async fn head(rpc: &Rpc, target: uuid::Uuid, n: u128, deadline: Duration) -> io::Result<u128> {
        rpc.call(target, Frame::Client(Request::Head(StreamId(n))), deadline)
            .await
    }

    #[tokio::test]
    async fn concurrent_messages_share_one_connection_and_frame_and_match_their_ids() {
        let (rpc, target, dials) = muxed(|_, _| Answering::At(Duration::ZERO));
        let count = decisions::CONTROL_PER_SENDER as u128;
        let replies = futures::future::join_all(
            (0..count).map(|n| head(&rpc, target, n, Duration::from_secs(5))),
        )
        .await;
        for (n, reply) in replies.into_iter().enumerate() {
            assert_eq!(reply.unwrap(), n as u128);
        }
        assert_eq!(dials.load(Ordering::Relaxed), 1);
        // Messages queued together, such as heartbeats, travel in one frame.
        assert_eq!(rpc.frames(), 1);
        // A failure answers only its own message.
        let (rpc, target, _) = muxed(|n, _| {
            if n == 3 {
                Answering::Fail
            } else {
                Answering::At(Duration::ZERO)
            }
        });
        let replies = futures::future::join_all(
            (0..8).map(|n| head(&rpc, target, n, Duration::from_secs(5))),
        )
        .await;
        for (n, reply) in replies.into_iter().enumerate() {
            assert_eq!(reply.is_err(), n == 3);
        }
    }

    #[tokio::test]
    async fn a_slow_reply_holds_back_no_other_message_and_a_late_one_is_dropped() {
        let (rpc, target, dials) = muxed(|n, _| match n {
            0 => Answering::At(Duration::from_millis(300)),
            _ => Answering::At(Duration::ZERO),
        });
        let started = tokio::time::Instant::now();
        let slow = head(&rpc, target, 0, Duration::from_millis(100));
        let quick = futures::future::join_all(
            (1..=8).map(|n| head(&rpc, target, n, Duration::from_secs(5))),
        );
        let (slow, quick) = tokio::join!(slow, quick);
        assert_eq!(slow.unwrap_err().kind(), io::ErrorKind::TimedOut);
        assert!(quick.into_iter().all(|reply| reply.is_ok()));
        // The quick replies were not queued behind the slow one.
        assert!(started.elapsed() < Duration::from_millis(250));
        // The late reply finds no caller and the channel keeps serving.
        tokio::time::sleep(Duration::from_millis(300)).await;
        assert_eq!(
            head(&rpc, target, 9, Duration::from_secs(5)).await.unwrap(),
            9
        );
        assert_eq!(dials.load(Ordering::Relaxed), 1);
        assert_eq!(
            rpc.inner.channels.lock()[&target]
                .permits
                .available_permits(),
            decisions::CONTROL_PER_SENDER
        );
    }

    #[tokio::test]
    async fn a_dropped_connection_fails_its_waiters_and_the_next_call_reconnects() {
        let (rpc, target, dials) = muxed(|n, dial| match (n, dial) {
            (0, 0) => Answering::Close,
            _ => Answering::At(Duration::from_millis(50)),
        });
        let waiting = futures::future::join_all(
            (0..4).map(|n| head(&rpc, target, 3 - n, Duration::from_secs(5))),
        )
        .await;
        // The receiver closed before answering any message of the batch.
        assert!(waiting.iter().all(|reply| {
            reply
                .as_ref()
                .is_err_and(|error| error.kind() == io::ErrorKind::ConnectionAborted)
        }));
        assert_eq!(
            head(&rpc, target, 5, Duration::from_secs(5)).await.unwrap(),
            5
        );
        assert_eq!(dials.load(Ordering::Relaxed), 2);
    }

    #[tokio::test]
    async fn oversized_bulk_frame_is_rejected_before_consuming_a_body() {
        let (mut sender, mut receiver) = tokio::io::duplex(32);
        sender
            .write_u32((Lane::Bulk.frame_limit() + 1) as u32)
            .await
            .unwrap();
        let error = timeout(
            Duration::from_millis(100),
            receive::<Frame>(&mut receiver, Lane::Bulk.frame_limit()),
        )
        .await
        .expect("the header is sufficient")
        .err()
        .unwrap();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }
}

/// A round trip that `LOGKEEPER_PEER_DELAY_MS` adds to every replication
/// request, to measure commit latency across links slower than loopback.
#[cfg(feature = "consensus-testing")]
fn injected_peer_delay() -> Option<Duration> {
    static DELAY: std::sync::OnceLock<Option<Duration>> = std::sync::OnceLock::new();
    *DELAY.get_or_init(|| {
        std::env::var("LOGKEEPER_PEER_DELAY_MS")
            .ok()
            .and_then(|value| value.parse().ok())
            .filter(|ms| *ms > 0)
            .map(Duration::from_millis)
    })
}
