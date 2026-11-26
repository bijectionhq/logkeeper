use std::{collections::HashMap, fmt, future::Future, io, sync::Arc, time::Duration};

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
    io::{AsyncRead, AsyncReadExt, AsyncSeekExt, AsyncWrite, AsyncWriteExt},
    sync::watch,
    time::timeout,
};
use tokio_rustls::TlsConnector;

use super::decisions::{self, AppendFit, EntryKind, PeerKind, PeerLane};
use super::{
    ALPN, BULK_ALPN, CONTROL_ALPN, Entry, Fence, Genesis, Keepers, LogId, MAX_MESSAGE, NodeId,
    REPLICATION_ALPN, RaftTypes, SnapshotMeta, Stage, Vote, decode, encode, invalid, options,
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
}

impl Request {
    pub fn stream(&self) -> StreamId {
        match *self {
            Self::Claim(ref genesis) => genesis.stream,
            Self::ReadAt { ref genesis, .. } => genesis.stream,
            Self::StageReplica { ref genesis, .. } | Self::InstallReplica { ref genesis, .. } => {
                genesis.stream
            }
            Self::Locate(stream)
            | Self::Bootstrap(stream)
            | Self::Create(stream)
            | Self::Head(stream)
            | Self::PlacementProof(stream)
            | Self::LocalCopy(stream)
            | Self::Delete(stream)
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
            | Self::Replace { stream, .. } => stream,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub(super) enum Frame {
    Client(Request),
    Peer(Genesis, PeerRequest),
}

#[derive(Serialize, Deserialize)]
pub(super) enum PeerRequest {
    Append(#[serde(deserialize_with = "bounded_append")] AppendEntriesRequest<RaftTypes>),
    Vote(VoteRequest<RaftTypes>),
    Snapshot(SnapshotChunk, [u8; 32]),
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
            Self::Vote(_) => (PeerKind::Vote, false),
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
            Self::Vote(request) => Some(request.vote.leader_id().voted_for),
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
/// split and stays unreachable.
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
    let bytes = encode(message)?;
    channel.write_u32(bytes.len() as u32).await?;
    channel.write_all(&bytes).await?;
    channel.flush().await
}

#[derive(Clone)]
pub(super) struct Rpc {
    inner: Arc<Connections>,
}

struct Connections {
    tls: TlsConnector,
    keepers: Keepers,
    idle: Mutex<HashMap<uuid::Uuid, Vec<Channel>>>,
    lane: Lane,
}

impl Rpc {
    pub fn new(tls: TlsConnector, keepers: Keepers, lane: Lane) -> Self {
        Self {
            inner: Arc::new(Connections {
                tls,
                keepers,
                idle: Mutex::default(),
                lane,
            }),
        }
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
        timeout(deadline, self.exchange(target, request)).await?
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
        let cached = self.inner.idle.lock().get_mut(&target).and_then(Vec::pop);
        let mut channel = match cached {
            Some(channel) => channel,
            None => {
                let (peer, channel) = connect_protocol(
                    &self.inner.tls,
                    &address.to_string(),
                    self.inner.lane.alpn(),
                )
                .await?;
                if peer.0 != target.as_u128() {
                    return Err(invalid("keeper certificate does not match route"));
                }
                channel
            }
        };
        send(&mut channel, &request).await?;
        let result = receive(&mut channel, MAX_MESSAGE).await?;
        let mut idle = self.inner.idle.lock();
        let idle = idle.entry(target).or_default();
        if idle.len() < 4 {
            idle.push(channel);
        }
        Ok(result)
    }
}

#[derive(Clone)]
pub(super) struct Network {
    pub control: Rpc,
    pub replication: Rpc,
    pub bulk: Rpc,
    pub genesis: Genesis,
    pub state: StateMachine,
    pub split_vote: watch::Sender<Option<Vote>>,
}

pub(super) struct Peer {
    network: Network,
    target: NodeId,
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
            .map_err(|error| unreachable(&error).into())
    }

    /// Sends one AppendEntries that fits its lane.
    async fn append_part(
        &self,
        range: (Option<LogId>, Option<LogId>),
        lane: Lane,
        frame: Frame,
        option: &RPCOption,
    ) -> Result<AppendResult<RaftTypes>, RPCError<RaftTypes>> {
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
                super::metrics::count(&super::metrics::COUNTERS.peer_unreachable);
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
                .and_then(|size| fit_append(lane, size, count));
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
        Ok(response)
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
