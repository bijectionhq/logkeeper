//! TLS admission and frame budgets are independent for each network lane.

use crate::stream::consensus::decisions;
use std::{io, sync::Arc, time::Duration};

use openraft::{
    async_runtime::WatchReceiver,
    errors::RaftError,
    raft::{AppendEntriesRequest, AppendEntriesResponse, SnapshotResponse},
};
use tokio::{
    io::{AsyncReadExt, AsyncSeekExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::{OwnedSemaphorePermit, Semaphore, mpsc},
    task::JoinSet,
    time::{Instant, sleep_until, timeout},
};
use tokio_rustls::TlsAcceptor;
use tokio_util::task::AbortOnDropHandle;
use uuid::Uuid;

use super::admission::{Charge, Control};
use super::{Command, Engine, Group, Identity, Lane, SNAPSHOT_CHUNK_BYTES, invalid, transport};
use crate::stream::consensus::{
    Genesis, MAX_MESSAGE, MAX_RECORD, NodeId, RaftTypes, SnapshotMeta, Vote, encode,
    network::{
        self, AppendReply, BatchReply, ChunkReply, DecodedFrame, Frame, PeerRequest, Reply,
        SnapshotChunk, SnapshotMismatch, WireVersion,
    },
    storage::{Admission, MAX_TRANSFER_FILE, SnapshotFile},
};

pub(super) const MAX_CLIENT_CONNECTIONS: usize = 64;
pub(super) const MAX_BULK_CONNECTIONS: usize = 8;
const CONNECTION_TIMEOUT: Duration = Duration::from_secs(60);
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(3);
const MAX_HANDSHAKES: usize = 32;
const SNAPSHOT_IDLE: Duration = Duration::from_secs(30);

pub(super) struct Incoming {
    session: Uuid,
    vote: Vote,
    meta: SnapshotMeta,
    digest: [u8; 32],
    next: u64,
    expires: Instant,
    file: Box<SnapshotFile>,
    _expiry: AbortOnDropHandle<()>,
}

impl Group {
    // Keep the existing wire protocol. Admit and stage incoming chunks
    // outside Raft so a refused bulk allocation is a retryable transport
    // failure and never a failure of the replica's durable state machine.
    pub(super) async fn receive_chunk(
        self: &Arc<Self>,
        request: SnapshotChunk,
        digest: [u8; 32],
    ) -> io::Result<ChunkReply> {
        let vote = self
            .raft
            .with_raft_state(|state| *state.vote_ref())
            .await
            .map_err(io::Error::other)?;
        if request.vote < vote {
            return Ok(Ok(SnapshotResponse::new(vote)));
        }
        let mut receiving = self.snapshot_receive.lock().await;
        if receiving
            .as_ref()
            .is_some_and(|current| current.expires <= Instant::now())
        {
            receiving.take();
        }
        let same = receiving.as_ref().is_some_and(|current| {
            current.vote == request.vote && current.meta == request.meta && current.digest == digest
        });
        if !same && request.offset == 0 {
            if receiving
                .as_ref()
                .is_some_and(|current| current.vote > request.vote)
            {
                return Err(invalid("a newer snapshot transfer is already in progress"));
            }
            receiving.take();
            *self.leader_matched.lock() = None;
            let file = self
                .state
                .receive_snapshot(digest, request.meta.clone())
                .await?;
            let session = Uuid::new_v4();
            let expires = Instant::now() + SNAPSHOT_IDLE;
            let expiry = self.expire_transfer(session, expires);
            *receiving = Some(Incoming {
                session,
                vote: request.vote,
                meta: request.meta.clone(),
                digest,
                next: 0,
                expires,
                file,
                _expiry: expiry,
            });
        }
        let next = receiving
            .as_ref()
            .filter(|_| same || request.offset == 0)
            .map_or(0, |current| current.next);
        if (!same && request.offset != 0) || request.offset > next {
            return Ok(Err(RaftError::APIError(SnapshotMismatch {
                expect: next,
                got: request.offset,
            })));
        }
        let current = receiving.as_mut().unwrap();
        current.expires = Instant::now() + SNAPSHOT_IDLE;
        let written = async {
            current
                .file
                .seek(io::SeekFrom::Start(request.offset))
                .await?;
            current.file.write_all(&request.data).await?;
            if request.done {
                current.file.shutdown().await?;
            }
            Ok::<_, io::Error>(())
        }
        .await;
        if let Err(error) = written {
            receiving.take();
            return Err(error);
        }
        let chunk_bytes = request.data.len() as u64;
        let end = request.offset + chunk_bytes;
        current.next = current.next.max(end);
        crate::stream::consensus::metrics::add(
            &self.state.metrics().snapshot_bytes_received,
            chunk_bytes,
        );
        if !request.done {
            return Ok(Ok(SnapshotResponse::new(vote)));
        }
        let complete = receiving.take().unwrap();
        if end != complete.next {
            crate::stream::consensus::metrics::count(
                &self.state.metrics().snapshots_received_failed,
            );
            return Err(invalid("final chunk does not end the snapshot"));
        }
        let installed = self
            .raft
            .install_full_snapshot(
                request.vote,
                openraft::Snapshot {
                    meta: complete.meta.raft(),
                    snapshot: complete.file,
                },
            )
            .await
            .map_err(RaftError::Fatal);
        if installed.is_ok() {
            crate::stream::consensus::metrics::count(&self.state.metrics().snapshots_received_ok);
        } else {
            crate::stream::consensus::metrics::count(
                &self.state.metrics().snapshots_received_failed,
            );
        }
        Ok(installed)
    }

    fn expire_transfer(
        self: &Arc<Self>,
        session: Uuid,
        mut expires: Instant,
    ) -> AbortOnDropHandle<()> {
        let group = Arc::downgrade(self);
        AbortOnDropHandle::new(tokio::spawn(async move {
            loop {
                sleep_until(expires).await;
                let Some(group) = group.upgrade() else { break };
                let mut receiving = group.snapshot_receive.lock().await;
                let Some(current) = receiving
                    .as_ref()
                    .filter(|current| current.session == session)
                else {
                    break;
                };
                if current.expires <= Instant::now() {
                    receiving.take();
                    break;
                }
                expires = current.expires;
            }
        }))
    }
}

impl Engine {
    pub(super) async fn listen(
        self: Arc<Self>,
        listener: TcpListener,
        lane: Lane,
        capacity: usize,
    ) -> io::Result<()> {
        let mut tasks = JoinSet::new();
        let handshakes = Arc::new(Semaphore::new(MAX_HANDSHAKES));
        let connections = Arc::new(Semaphore::new(capacity));
        let control = Arc::new(Control::default());
        loop {
            tokio::select! {
                _ = self.stop.cancelled() => return Ok(()),
                result = tasks.join_next(), if !tasks.is_empty() => {
                    if let Some(Err(error)) = result { return Err(error.into()); }
                }
                admitted = async {
                    let pending = handshakes.clone().acquire_owned().await.expect("open handshake semaphore");
                    let (socket, _) = listener.accept().await?;
                    Ok::<_, io::Error>((socket, pending))
                } => {
                    let (socket, pending) = admitted?;
                    let engine = self.clone();
                    let acceptor = self.tls.server(lane);
                    let connections = connections.clone();
                    let control = control.clone();
                    tasks.spawn(async move {
                        let _ = engine.connection(socket, acceptor, lane, pending, connections, &control).await;
                    });
                }
            }
        }
    }

    async fn connection(
        self: &Arc<Self>,
        socket: TcpStream,
        acceptor: TlsAcceptor,
        lane: Lane,
        pending: OwnedSemaphorePermit,
        connections: Arc<Semaphore>,
        control: &Arc<Control>,
    ) -> io::Result<()> {
        socket.set_nodelay(true)?;
        let mut channel = timeout(HANDSHAKE_TIMEOUT, acceptor.accept(socket)).await??;
        let (_, tls) = channel.get_ref();
        let certificate = transport::leaf(tls.peer_certificates())?;
        let identity = match transport::keeper_id(certificate) {
            Ok(id)
                if self
                    .rpc
                    .keepers()
                    .contains_key(&uuid::Uuid::from_u128(id.0)) =>
            {
                Identity::Keeper(id.0)
            }
            Ok(_) => return Err(invalid("unknown peer keeper")),
            Err(_) => Identity::Client(transport::client_identity(certificate)?),
        };
        let negotiated = tls
            .alpn_protocol()
            .and_then(Lane::classify)
            .ok_or_else(|| invalid("invalid consensus channel ALPN"))?;
        let (negotiated_lane, version) = negotiated;
        let allowed_lane =
            negotiated_lane == lane || (lane == Lane::Bulk && negotiated_lane == Lane::Replication);
        if !allowed_lane
            || (negotiated_lane != Lane::Application && !matches!(identity, Identity::Keeper(_)))
        {
            return Err(invalid("invalid consensus channel identity"));
        }
        let lane = negotiated_lane;
        if let (Lane::Control | Lane::Replication, Identity::Keeper(sender)) = (lane, &identity) {
            drop(pending);
            return self
                .multiplexed(channel, lane, version, *sender, control)
                .await;
        }
        let _connection = connections
            .clone()
            .try_acquire_owned()
            .map_err(|_| io::Error::other("consensus lane is full"))?;
        drop(pending);
        loop {
            self.require_media()?;
            let size = timeout(
                CONNECTION_TIMEOUT,
                network::receive_size(&mut channel, lane.frame_limit()),
            )
            .await??;
            let mut body = vec![0; size];
            timeout(CONNECTION_TIMEOUT, channel.read_exact(&mut body)).await??;
            let frame = match network::decode_frame(&body, version)? {
                DecodedFrame::Frame(frame) => frame,
                DecodedFrame::Unsupported(reason) if lane == Lane::Application => {
                    let encoded = network::encode_reply(Reply::Unsupported(reason), version)?;
                    timeout(
                        CONNECTION_TIMEOUT,
                        network::send_encoded(&mut channel, &encoded),
                    )
                    .await??;
                    continue;
                }
                DecodedFrame::Unsupported(reason) => {
                    return Err(network::unsupported(reason));
                }
            };
            match frame {
                Frame::Client(request) if lane == Lane::Application => {
                    let reply = self.request(&identity, request).await?;
                    self.require_media()?;
                    let encoded = network::encode_reply(reply, version)?;
                    timeout(
                        CONNECTION_TIMEOUT,
                        network::send_encoded(&mut channel, &encoded),
                    )
                    .await??;
                }
                Frame::Peer(genesis, request) if lane == Lane::Bulk => {
                    let Identity::Keeper(sender) = identity else {
                        return Err(invalid("application certificate used for consensus"));
                    };
                    check_peer(lane, sender, &request)?;
                    let reply = self.peer(sender, genesis, request, None).await?;
                    timeout(
                        CONNECTION_TIMEOUT,
                        network::send_encoded(&mut channel, &reply),
                    )
                    .await??;
                }
                _ => return Err(invalid("request used the wrong lane")),
            }
        }
    }

    /// Serves one multiplexed peer connection. Each batch frame is split
    /// into messages, each message is admitted on its own and runs
    /// concurrently with the others, and replies go back in batch frames as
    /// they finish. A message the sender may not send on this lane or as
    /// this keeper closes the connection; any other failure answers only
    /// its own message.
    async fn multiplexed(
        self: &Arc<Self>,
        channel: tokio_rustls::server::TlsStream<TcpStream>,
        lane: Lane,
        version: WireVersion,
        sender: NodeId,
        control: &Arc<Control>,
    ) -> io::Result<()> {
        let (mut read, mut write) = tokio::io::split(channel);
        let (answers, mut answered) = mpsc::unbounded_channel::<(u64, BatchReply)>();
        let reading = async {
            let mut work = JoinSet::new();
            loop {
                self.require_media()?;
                let header = timeout(
                    CONNECTION_TIMEOUT,
                    network::receive_size(&mut read, lane.frame_limit()),
                );
                while work.try_join_next().is_some() {}
                // A connection with messages in flight is not idle, so the
                // idle limit never closes it under its own replies.
                let size = if lane == Lane::Control && work.is_empty() {
                    let idle = control.wait_for_header();
                    tokio::select! {
                        biased;
                        _ = idle.cancelled.cancelled() => return Ok(()),
                        header = header => header??,
                    }
                } else {
                    header.await??
                };
                let read_charge = match lane {
                    Lane::Replication => Some(
                        timeout(
                            CONNECTION_TIMEOUT,
                            self.replication_ingress.read(sender, size),
                        )
                        .await?,
                    ),
                    _ => None,
                };
                let mut body = vec![0; size];
                timeout(CONNECTION_TIMEOUT, read.read_exact(&mut body)).await??;
                let mut batch = Vec::new();
                for (id, message) in network::messages(&body)? {
                    let frame = match network::decode_frame(message, version)? {
                        DecodedFrame::Frame(frame) => frame,
                        DecodedFrame::Unsupported(reason) => {
                            let _ = answers.send((id, BatchReply::Unsupported(reason)));
                            continue;
                        }
                    };
                    let (genesis, request) = match frame {
                        Frame::Peer(genesis, request) => (genesis, request),
                        // A ping costs one status read and no admission.
                        Frame::Liveness(incarnation) if lane == Lane::Control => {
                            let (engine, answers) = (self.clone(), answers.clone());
                            work.spawn(async move {
                                let reply = engine.pong(sender, incarnation, version).await;
                                let _ = answers.send((id, reply));
                            });
                            continue;
                        }
                        Frame::Ping {
                            incarnation,
                            version: build,
                            features,
                        } if lane == Lane::Control && version == WireVersion::Current => {
                            self.record_incoming_ping(Uuid::from_u128(sender), build, features);
                            let (engine, answers) = (self.clone(), answers.clone());
                            work.spawn(async move {
                                let reply = engine.pong(sender, incarnation, version).await;
                                let _ = answers.send((id, reply));
                            });
                            continue;
                        }
                        _ => return Err(invalid("request used the wrong lane")),
                    };
                    check_peer(lane, sender, &request)?;
                    batch.push((id, message.len(), genesis, request));
                }
                drop(body);
                let mut charges = match read_charge {
                    Some(read) => {
                        let sizes = batch.iter().map(|(_, size, ..)| *size).collect::<Vec<_>>();
                        self.replication_ingress.split(read, &sizes)
                    }
                    None => Vec::new(),
                }
                .into_iter();
                for (id, _, genesis, request) in batch {
                    let admitted = match lane {
                        Lane::Replication => charges
                            .next()
                            .flatten()
                            .map(|charge| (Some(charge), None))
                            .ok_or_else(|| invalid("replication receiver is busy")),
                        _ => control
                            .admit_waiting(sender)
                            .await
                            .map(|work| (None, Some(work))),
                    };
                    let (body, admission) = match admitted {
                        Ok(admitted) => admitted,
                        Err(refused) => {
                            let answer = match request {
                                PeerRequest::Append(_) => encode(&AppendReply::Busy),
                                _ => Err(refused),
                            };
                            let reply = match answer {
                                Ok(bytes) => BatchReply::Ok(bytes),
                                Err(error) => BatchReply::Err(error.to_string()),
                            };
                            let _ = answers.send((id, reply));
                            continue;
                        }
                    };
                    let (engine, answers) = (self.clone(), answers.clone());
                    work.spawn(async move {
                        let _admission = admission;
                        let reply = match engine.peer(sender, genesis, request, body).await {
                            Ok(bytes) => BatchReply::Ok(bytes),
                            Err(error) if error.kind() == io::ErrorKind::Unsupported => {
                                BatchReply::Unsupported(error.to_string())
                            }
                            Err(error) => BatchReply::Err(error.to_string()),
                        };
                        let _ = answers.send((id, reply));
                    });
                }
            }
        };
        let writing = async {
            while let Some((id, reply)) = answered.recv().await {
                let mut frame = network::batch_frame();
                network::push_reply(&mut frame, id, &reply, version);
                for _ in 1..network::BATCH_MESSAGES {
                    if frame.len() >= network::REPLY_BATCH_BYTES {
                        break;
                    }
                    let Ok((id, reply)) = answered.try_recv() else {
                        break;
                    };
                    network::push_reply(&mut frame, id, &reply, version);
                }
                self.require_media()?;
                timeout(CONNECTION_TIMEOUT, async {
                    write.write_all(network::seal_frame(&mut frame)).await?;
                    write.flush().await
                })
                .await??;
            }
            Ok(())
        };
        tokio::select! {
            result = reading => result,
            result = writing => result,
        }
    }

    /// Serves one decoded peer message and returns its encoded reply.
    pub(super) async fn peer(
        &self,
        sender: NodeId,
        genesis: Genesis,
        request: PeerRequest,
        body: Option<Charge>,
    ) -> io::Result<Vec<u8>> {
        if !self.placement.structural_genesis(&genesis) {
            return Err(invalid("invalid consensus sender or stream genesis"));
        }
        if self.deleted.read().contains(&genesis.stream) {
            return Err(invalid("stream is deleted"));
        }
        if self.is_quarantined(genesis.stream) {
            return Err(invalid("stream replica is quarantined"));
        }
        let parked = self.parked.read().get(&genesis.stream).copied();
        if let Some(since) = parked {
            // An empty heartbeat or a repeated park leaves the stream
            // parked; anything else reopens it. So do heartbeats that go on
            // past the park round: their leader stayed open because another
            // follower declined to park.
            let parked = match &request {
                PeerRequest::Append(append) if append.entries.is_empty() => {
                    decisions::ParkedRequest::Heartbeat
                }
                PeerRequest::Park { .. } => decisions::ParkedRequest::Park,
                _ => decisions::ParkedRequest::Other,
            };
            match decisions::parked_answer(
                parked,
                // A copy closed to free its slot has no park time: it stays
                // closed to heartbeats until other traffic reopens it.
                since.map_or(0, |since| since.elapsed().as_nanos()),
                super::park::PARKED_HEARTBEATS.as_nanos(),
            ) {
                decisions::ParkedAnswer::Busy => return encode(&AppendReply::Busy),
                decisions::ParkedAnswer::Parked => return encode(&true),
                decisions::ParkedAnswer::Reopen => {
                    if self.parked.write().remove(&genesis.stream).is_some() {
                        super::super::metrics::count(&self.disk.metrics.unparked_by_peer);
                    }
                }
            }
        }
        let group = self.group(genesis).await?;
        group.require_healthy()?;
        // Every frame that carries the sender's vote is checked, because
        // every answer to one carries this replica's vote or reveals it: a
        // snapshot chunk's reply holds it, and a refused hand-off names it.
        let campaign = match &request {
            PeerRequest::Append(append) => Some(append.vote),
            PeerRequest::Vote(vote) | PeerRequest::PreVote(vote) => Some(vote.vote),
            PeerRequest::Snapshot(chunk, _) => Some(chunk.vote),
            PeerRequest::TransferLeader(transfer) => Some(*transfer.from_leader()),
            PeerRequest::Park { vote, .. } => Some(*vote),
        };
        if let Some(vote) = campaign {
            let metrics = group.raft.metrics();
            let current = metrics.borrow_watched();
            let membership = current.membership_config.membership();
            if decisions::excludes_sender(
                !membership.get_joint_config().is_empty(),
                membership.get_node(&sender).is_some(),
                vote.leader_id().term,
                current.vote.leader_id().term,
            ) {
                return Err(invalid(network::EXCLUDED));
            }
        }
        if matches!(request, PeerRequest::Vote(_) | PeerRequest::PreVote(_)) {
            self.confirm_placement(&group).await?;
        }
        match request {
            PeerRequest::Append(request) => {
                #[cfg(test)]
                if self
                    .reject_append
                    .read()
                    .as_ref()
                    .is_some_and(|reject| reject(group.genesis.stream, sender, &request))
                {
                    return Err(io::Error::other("injected append loss"));
                }
                self.check_entries(&group, &request)?;
                *group.heard.lock() = tokio::time::Instant::now();
                let reply = self.append(group.clone(), request, body).await?;
                // The leader campaigned certified, so its append certifies
                // this copy unless this copy's vote outranks it.
                if let AppendReply::Raft(Ok(response)) = &reply
                    && !matches!(response, AppendEntriesResponse::HigherVote(_))
                {
                    self.certification
                        .certify(group.genesis.stream, group.state.generation());
                }
                #[cfg(test)]
                if matches!(reply, AppendReply::Busy) {
                    self.busy_replies
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                if !matches!(reply, AppendReply::Raft(Err(_))) {
                    group.require_healthy()?;
                }
                encode(&reply)
            }
            request @ (PeerRequest::Vote(_)
            | PeerRequest::PreVote(_)
            | PeerRequest::TransferLeader(_)
            | PeerRequest::Park { .. }) => {
                let stream = group.genesis.stream;
                let installed = self.disk.installed(stream);
                if !installed {
                    return Err(invalid("staged replica cannot vote"));
                }
                let eligible = {
                    let metrics = group.raft.server_metrics();
                    let current = metrics.borrow_watched();
                    let membership = current.membership_config.membership();
                    let configs = membership.get_joint_config();
                    let recovering = self
                        .disk
                        .ownership(stream)
                        .and_then(|book| book.recovery_stage(self.id).cloned())
                        .is_some_and(|stage| match configs.as_slice() {
                            [] => true,
                            [lost] => lost.iter().copied().eq(stage.old.map(|id| id.as_u128())),
                            _ => false,
                        });
                    decisions::votes(
                        installed,
                        !configs.is_empty(),
                        membership.voter_ids().any(|id| id == self.id.as_u128()),
                        group.genesis.voters.contains(&self.id),
                        recovering,
                    )
                };
                if !eligible {
                    return Err(invalid("vote is outside the effective placement"));
                }
                // Slow media would make this keeper a slow leader: it
                // neither votes nor takes leadership until it keeps up.
                if !matches!(request, PeerRequest::Park { .. }) && !self.disk.responsive() {
                    return Err(invalid("keeper media is slow"));
                }
                match request {
                    PeerRequest::Vote(request) => {
                        let reply = group.raft.vote(request).await;
                        if let Ok(resp) = &reply {
                            if resp.vote_granted {
                                super::super::metrics::count(&self.disk.metrics.votes_granted);
                            } else {
                                super::super::metrics::count(&self.disk.metrics.votes_denied);
                            }
                        }
                        group.require_healthy()?;
                        encode(&reply)
                    }
                    PeerRequest::PreVote(request) => {
                        let reply = group.raft.pre_vote(request).await;
                        if let Ok(resp) = &reply {
                            if resp.vote_granted {
                                super::super::metrics::count(&self.disk.metrics.pre_votes_granted);
                            } else {
                                super::super::metrics::count(&self.disk.metrics.pre_votes_denied);
                            }
                        }
                        group.require_healthy()?;
                        encode(&reply)
                    }
                    PeerRequest::Park { vote, last } => {
                        encode(&self.accept_park(&group, vote, last).await)
                    }
                    PeerRequest::TransferLeader(request) => {
                        *group.handoff.lock() = Some(tokio::time::Instant::now());
                        let reply = group.raft.handle_transfer_leader(request).await;
                        group.require_healthy()?;
                        encode(&reply)
                    }
                    _ => unreachable!("matched a vote-class request"),
                }
            }
            PeerRequest::Snapshot(request, digest) => {
                let data = request.data.len() as u64;
                let capacity = group
                    .genesis
                    .quota_bytes
                    .saturating_mul(9)
                    .saturating_add(MAX_MESSAGE);
                if data > SNAPSHOT_CHUNK_BYTES
                    || request
                        .offset
                        .checked_add(data)
                        .is_none_or(|end| end > capacity.min(MAX_TRANSFER_FILE))
                {
                    return Err(invalid("invalid consensus snapshot chunk range"));
                }
                let response = group.receive_chunk(request, digest).await?;
                group.require_healthy()?;
                encode(&response)
            }
        }
    }

    fn check_entries(
        &self,
        group: &Group,
        request: &AppendEntriesRequest<RaftTypes>,
    ) -> io::Result<()> {
        let ids = request
            .entries
            .iter()
            .map(|entry| (entry.log_id.index, entry.log_id.leader_id.term))
            .collect::<Vec<_>>();
        let previous = request.prev_log_id.map(|id| (id.index, id.leader_id.term));
        if !decisions::consecutive_cut(previous, &ids, request.vote.leader_id().term) {
            return Err(invalid("nonconsecutive peer append cut"));
        }
        for entry in &request.entries {
            let valid = match &entry.payload {
                openraft::EntryPayload::Membership(membership) => {
                    self.placement.structural_membership(membership)
                }
                openraft::EntryPayload::Normal(command) => match command.body() {
                    Command::Stage(stage) | Command::StageOwned(stage) => {
                        stage.stream == group.genesis.stream
                            && self.placement.structural_stage(stage)
                    }
                    Command::Recover(stage) => {
                        stage.stream == group.genesis.stream
                            && self.placement.structural_stage(stage)
                            && stage.recovery()
                    }
                    Command::Append { payload, .. } => payload.len() <= MAX_RECORD,
                    Command::AppendOriginal { record, .. } => {
                        record.len() > crate::stream::timed::EVIDENCE_BYTES
                            && record.len() <= MAX_RECORD
                    }
                    Command::AppendBatch { payloads, .. } => {
                        crate::stream::consensus::state::valid_batch(payloads)
                    }
                    Command::Admitted(..) => false,
                    _ => true,
                },
                openraft::EntryPayload::Blank => true,
            };
            if !valid {
                return Err(invalid("invalid replicated entry"));
            }
        }
        Ok(())
    }

    async fn append(
        &self,
        group: Arc<Group>,
        request: AppendEntriesRequest<RaftTypes>,
        body: Option<Charge>,
    ) -> io::Result<AppendReply> {
        let term = request.vote.leader_id().term;
        let last_entry = request
            .entries
            .last()
            .map(|entry| entry.log_id)
            .or(request.prev_log_id);
        let leader_commit = request.leader_commit;
        let reply = if request.entries.is_empty() {
            raft_reply(group.raft.append_entries(request).await)
        } else {
            let Ok(ordered) = group.append_order.clone().try_lock_owned() else {
                return Ok(AppendReply::Busy);
            };
            let Some(body) = body else {
                let _ordered = ordered;
                let reply = raft_reply(group.raft.append_entries(request).await);
                record_leader_match(&group, term, last_entry, leader_commit, &reply);
                return Ok(reply);
            };
            let destination = match group.follower.admit(
                &self.disk,
                group.genesis.stream,
                request.vote,
                &request.entries,
            ) {
                Ok(reservation) => reservation,
                Err(Admission::FullSuffix) => {
                    group.request_covered_purge().await;
                    return Ok(AppendReply::Busy);
                }
                Err(Admission::Space) => return Ok(AppendReply::Busy),
            };
            // The request task owns the body, ordering gate and disk reservation
            // from before dispatch through resolution, even if the socket closes.
            let target = group.clone();
            tokio::spawn(async move {
                let (_ordered, _body, _destination) = (ordered, body, destination);
                raft_reply(target.raft.append_entries(request).await)
            })
            .await
            .map_err(io::Error::other)?
        };
        record_leader_match(&group, term, last_entry, leader_commit, &reply);
        Ok(reply)
    }
}

fn record_leader_match(
    group: &Group,
    term: u64,
    last_entry: Option<crate::stream::consensus::LogId>,
    leader_commit: Option<crate::stream::consensus::LogId>,
    reply: &AppendReply,
) {
    match reply {
        AppendReply::Raft(Ok(AppendEntriesResponse::Success)) => {
            if leader_commit
                .is_none_or(|commit| last_entry.is_some_and(|last| last.index >= commit.index))
            {
                *group.leader_matched.lock() = Some((term, Instant::now()));
            }
        }
        AppendReply::Raft(Ok(
            AppendEntriesResponse::Conflict | AppendEntriesResponse::HigherVote(_),
        )) => {
            *group.leader_matched.lock() = None;
        }
        _ => {}
    }
}

/// A peer may send a message only on its own lane and only as itself.
fn check_peer(lane: Lane, sender: NodeId, request: &PeerRequest) -> io::Result<()> {
    if request.lane() != lane {
        return Err(invalid("peer request used the wrong lane"));
    }
    if request.sender() != Some(sender) {
        return Err(invalid("invalid consensus sender or stream genesis"));
    }
    Ok(())
}

fn raft_reply(
    result: Result<openraft::raft::AppendResult<RaftTypes>, RaftError<RaftTypes>>,
) -> AppendReply {
    AppendReply::Raft(result.map(AppendEntriesResponse::from))
}
