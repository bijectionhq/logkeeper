use std::{collections::HashMap, future::Future, io, sync::Arc, time::Duration};

use bincode::Options;
use journal_contract::{Epoch, Lsn, StreamId};
use openraft::{
    BasicNode, EntryPayload, Snapshot,
    error::{
        Fatal, InstallSnapshotError, PayloadTooLarge, RPCError, RaftError, RemoteError,
        ReplicationClosed, StreamingError, Unreachable,
    },
    network::{
        RPCOption, RaftNetwork, RaftNetworkFactory,
        snapshot_transport::{Chunked, SnapshotTransport},
    },
    raft::{
        AppendEntriesRequest, AppendEntriesResponse, InstallSnapshotRequest,
        InstallSnapshotResponse, SnapshotResponse, VoteRequest, VoteResponse,
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
    REPLICATION_ALPN, RaftTypes, Stage, Vote, decode, encode, invalid, options,
    state::{Command, Outcome},
    storage::StateMachine,
};
use crate::stream::transport::{Channel, connect_protocol};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Lane {
    Application,
    Control,
    Replication,
    Bulk,
}

pub(super) const MAX_PEER_ENTRIES: usize = 4;

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
    Vote(VoteRequest<NodeId>),
    Snapshot(InstallSnapshotRequest<RaftTypes>, [u8; 32]),
}

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
            Self::Append(request) => request.vote.leader_id().voted_for(),
            Self::Vote(request) => request.vote.leader_id().voted_for(),
            Self::Snapshot(request, _) => request.vote.leader_id().voted_for(),
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

/// A valid batch that exceeds its lane is split by OpenRaft at the sender, so
/// the receiver never needs to allocate it. A single oversized entry cannot be
/// split and stays unreachable.
fn fit_append(
    lane: Lane,
    size: u64,
    count: usize,
) -> Result<(), RPCError<NodeId, BasicNode, RaftError<NodeId>>> {
    match decisions::fit_append(size, lane.frame_limit(), count, MAX_PEER_ENTRIES) {
        AppendFit::Fits => Ok(()),
        AppendFit::Split(hint) => Err(RPCError::PayloadTooLarge(
            PayloadTooLarge::new_entries_hint(hint as u64),
        )),
        AppendFit::Unfit => Err(RPCError::Unreachable(Unreachable::new(&invalid(
            "peer append cannot fit its lane",
        )))),
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub(super) enum AppendReply {
    Raft(Result<AppendEntriesResponse<NodeId>, RaftError<NodeId>>),
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

impl Peer {
    async fn request<T, E>(
        &self,
        request: PeerRequest,
        option: RPCOption,
    ) -> Result<T, RPCError<NodeId, BasicNode, E>>
    where
        T: DeserializeOwned,
        E: std::error::Error + DeserializeOwned,
    {
        if !self.network.state.active() {
            return Err(RPCError::Unreachable(Unreachable::new(&invalid(
                "quarantined stream replica",
            ))));
        }
        let rpc = match request.lane() {
            Lane::Bulk => &self.network.bulk,
            Lane::Control => &self.network.control,
            Lane::Replication => &self.network.replication,
            Lane::Application => unreachable!("peer request on application lane"),
        };
        let frame = Frame::Peer(self.network.genesis.clone(), request);
        let result: Result<T, E> = rpc
            .call(uuid::Uuid::from_u128(self.target), frame, option.hard_ttl())
            .await
            .map_err(|error| RPCError::Unreachable(Unreachable::new(&error)))?;
        result.map_err(|error| RPCError::RemoteError(RemoteError::new(self.target, error)))
    }
}

impl RaftNetwork<RaftTypes> for Peer {
    async fn append_entries(
        &mut self,
        request: AppendEntriesRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<AppendEntriesResponse<NodeId>, RPCError<NodeId, BasicNode, RaftError<NodeId>>> {
        if !self.network.state.active() {
            return Err(RPCError::Unreachable(Unreachable::new(&invalid(
                "quarantined stream replica",
            ))));
        }
        let count = request.entries.len();
        let request = PeerRequest::Append(request);
        let lane = request.lane();
        let frame = Frame::Peer(self.network.genesis.clone(), request);
        let size = options()
            .serialized_size(&frame)
            .map_err(|error| RPCError::Unreachable(Unreachable::new(&error)))?;
        fit_append(lane, size, count)?;
        let rpc = if lane == Lane::Replication {
            &self.network.replication
        } else {
            &self.network.control
        };
        match rpc
            .call(uuid::Uuid::from_u128(self.target), frame, option.hard_ttl())
            .await
        {
            Ok(AppendReply::Raft(reply)) => {
                reply.map_err(|error| RPCError::RemoteError(RemoteError::new(self.target, error)))
            }
            Ok(AppendReply::Busy) => Err(RPCError::Unreachable(Unreachable::new(&io::Error::new(
                io::ErrorKind::WouldBlock,
                "replication receiver is busy",
            )))),
            Err(error) => Err(RPCError::Unreachable(Unreachable::new(&error))),
        }
    }

    async fn vote(
        &mut self,
        request: VoteRequest<NodeId>,
        option: RPCOption,
    ) -> Result<VoteResponse<NodeId>, RPCError<NodeId, BasicNode, RaftError<NodeId>>> {
        let proposed = request.vote;
        let last_log = request.last_log_id;
        let response: VoteResponse<NodeId> =
            self.request(PeerRequest::Vote(request), option).await?;
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

    async fn install_snapshot(
        &mut self,
        request: InstallSnapshotRequest<RaftTypes>,
        option: RPCOption,
    ) -> Result<
        InstallSnapshotResponse<NodeId>,
        RPCError<NodeId, BasicNode, RaftError<NodeId, InstallSnapshotError>>,
    > {
        let digest = self
            .network
            .state
            .snapshot_digest(&request.meta)
            .ok_or_else(|| {
                RPCError::Unreachable(Unreachable::new(&invalid("snapshot selection changed")))
            })?;
        self.request(PeerRequest::Snapshot(request, digest), option)
            .await
    }

    async fn full_snapshot(
        &mut self,
        vote: Vote,
        mut snapshot: Snapshot<RaftTypes>,
        cancel: impl Future<Output = ReplicationClosed> + Send + 'static,
        option: RPCOption,
    ) -> Result<SnapshotResponse<NodeId>, StreamingError<RaftTypes, Fatal<NodeId>>> {
        let mut cancel = Box::pin(cancel);
        // A private spool is a bulk admission, so refusal must be retryable.
        // Once staged, OpenRaft uses the same stable file for all seeks.
        tokio::select! {
            closed = &mut cancel => return Err(closed.into()),
            staged = snapshot.snapshot.seek(io::SeekFrom::End(0)) => {
                staged.map_err(|error| Unreachable::new(&error))?;
            }
        }
        Ok(Chunked::send_snapshot(self, vote, snapshot, cancel, option).await?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_oversized_valid_batch_is_split_at_the_sender() {
        let limit = Lane::Replication.frame_limit();
        assert!(fit_append(Lane::Replication, limit, MAX_PEER_ENTRIES).is_ok());
        for (lane, size, count, hint) in [
            (Lane::Replication, limit + 1, 4, 2),
            (Lane::Replication, 1024, MAX_PEER_ENTRIES + 2, 3),
            (Lane::Control, Lane::Control.frame_limit() + 1, 2, 1),
        ] {
            match fit_append(lane, size, count) {
                Err(RPCError::PayloadTooLarge(error)) => assert_eq!(error.entries_hint(), hint),
                other => panic!("expected a resize hint, got {other:?}"),
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
