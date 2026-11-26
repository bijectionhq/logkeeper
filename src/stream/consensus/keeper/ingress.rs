//! TLS admission and frame budgets are independent for each network lane.

use crate::stream::consensus::decisions;
use std::{io, sync::Arc, time::Duration};

use openraft::{
    async_runtime::WatchReceiver,
    errors::RaftError,
    raft::{AppendEntriesRequest, AppendEntriesResponse, SnapshotResponse},
};
use tokio::{
    io::{AsyncSeekExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::{OwnedSemaphorePermit, Semaphore},
    task::JoinSet,
    time::{Instant, sleep_until, timeout},
};
use tokio_rustls::TlsAcceptor;
use tokio_util::task::AbortOnDropHandle;
use uuid::Uuid;

use super::admission::{Charge, Control};
use super::{Command, Engine, Group, Identity, Lane, SNAPSHOT_CHUNK_BYTES, invalid, transport};
use crate::stream::consensus::{
    MAX_MESSAGE, MAX_RECORD, RaftTypes, SnapshotMeta, Vote,
    network::{self, AppendReply, ChunkReply, Frame, PeerRequest, SnapshotChunk, SnapshotMismatch},
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
        let end = request.offset + request.data.len() as u64;
        current.next = current.next.max(end);
        if !request.done {
            return Ok(Ok(SnapshotResponse::new(vote)));
        }
        let complete = receiving.take().unwrap();
        if end != complete.next {
            return Err(invalid("final chunk does not end the snapshot"));
        }
        Ok(self
            .raft
            .install_full_snapshot(
                request.vote,
                openraft::Snapshot {
                    meta: complete.meta.raft(),
                    snapshot: complete.file,
                },
            )
            .await
            .map_err(RaftError::Fatal))
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
        acceptor: TlsAcceptor,
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
                    let acceptor = acceptor.clone();
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
        &self,
        socket: TcpStream,
        acceptor: TlsAcceptor,
        lane: Lane,
        pending: OwnedSemaphorePermit,
        connections: Arc<Semaphore>,
        control: &Control,
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
        let lane = if lane == Lane::Bulk && tls.alpn_protocol() == Some(Lane::Replication.alpn()) {
            Lane::Replication
        } else {
            lane
        };
        if tls.alpn_protocol() != Some(lane.alpn())
            || (lane != Lane::Application && !matches!(identity, Identity::Keeper(_)))
        {
            return Err(invalid("invalid consensus channel identity"));
        }
        let _connection = match lane {
            Lane::Application | Lane::Bulk => Some(
                connections
                    .clone()
                    .try_acquire_owned()
                    .map_err(|_| io::Error::other("consensus lane is full"))?,
            ),
            Lane::Control | Lane::Replication => None,
        };
        let _replication_socket = match (lane, &identity) {
            (Lane::Replication, Identity::Keeper(sender)) => {
                Some(self.replication_ingress.socket(*sender)?)
            }
            _ => None,
        };
        drop(pending);
        loop {
            self.require_media()?;
            let header = timeout(
                CONNECTION_TIMEOUT,
                network::receive_size(&mut channel, lane.frame_limit()),
            );
            let size = if lane == Lane::Control {
                let idle = control.wait_for_header();
                tokio::select! {
                    biased;
                    _ = idle.cancelled.cancelled() => return Ok(()),
                    header = header => header??,
                }
            } else {
                header.await??
            };
            let _control = match (lane, &identity) {
                (Lane::Control, Identity::Keeper(sender)) => Some(control.admit(*sender)?),
                _ => None,
            };
            let body = match (lane, &identity) {
                (Lane::Replication, Identity::Keeper(sender)) => {
                    Some(self.replication_ingress.body(*sender, size)?)
                }
                _ => None,
            };
            let frame = timeout(
                CONNECTION_TIMEOUT,
                network::receive_body(&mut channel, size),
            )
            .await??;
            match frame {
                Frame::Client(request) if lane == Lane::Application => {
                    let reply = self.request(&identity, request).await?;
                    self.require_media()?;
                    timeout(CONNECTION_TIMEOUT, network::send(&mut channel, &reply)).await??;
                }
                Frame::Peer(genesis, request) if lane != Lane::Application => {
                    let Identity::Keeper(sender) = identity else {
                        return Err(invalid("application certificate used for consensus"));
                    };
                    if request.lane() != lane {
                        return Err(invalid("peer request used the wrong lane"));
                    }
                    if request.sender() != Some(sender) || !self.placement.genesis(&genesis) {
                        return Err(invalid("invalid consensus sender or stream genesis"));
                    }
                    if self.deleted.read().contains(&genesis.stream) {
                        return Err(invalid("stream is deleted"));
                    }
                    let group = self.group(genesis).await?;
                    group.require_healthy()?;
                    match request {
                        PeerRequest::Append(request) => {
                            #[cfg(test)]
                            if self.reject_append.read().as_ref().is_some_and(|reject| {
                                reject(group.genesis.stream, sender, &request)
                            }) {
                                return Err(io::Error::other("injected append loss"));
                            }
                            self.check_entries(&group, &request)?;
                            let reply = self.append(group.clone(), request, body).await?;
                            #[cfg(test)]
                            if matches!(reply, AppendReply::Busy) {
                                self.busy_replies
                                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            }
                            if !matches!(reply, AppendReply::Raft(Err(_))) {
                                group.require_healthy()?;
                            }
                            timeout(CONNECTION_TIMEOUT, network::send(&mut channel, &reply))
                                .await??;
                        }
                        PeerRequest::Vote(request) => {
                            if !self.disk.installed(group.genesis.stream) {
                                return Err(invalid("staged replica cannot vote"));
                            }
                            let eligible = {
                                let metrics = group.raft.server_metrics();
                                let current = metrics.borrow_watched();
                                let membership = current.membership_config.membership();
                                if membership.get_joint_config().is_empty() {
                                    group.genesis.voters.contains(&self.id)
                                } else {
                                    membership.voter_ids().any(|id| id == self.id.as_u128())
                                }
                            };
                            if !eligible {
                                return Err(invalid("vote is outside the effective placement"));
                            }
                            let reply = group.raft.vote(request).await;
                            group.require_healthy()?;
                            timeout(CONNECTION_TIMEOUT, network::send(&mut channel, &reply))
                                .await??;
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
                            timeout(CONNECTION_TIMEOUT, network::send(&mut channel, &response))
                                .await??;
                        }
                    }
                }
                _ => return Err(invalid("request used the wrong lane")),
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
                    self.placement.membership(membership)
                }
                openraft::EntryPayload::Normal(command) => match command.body() {
                    Command::Stage(stage) | Command::StageOwned(stage) => {
                        stage.stream == group.genesis.stream && self.placement.stage(stage)
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
        if request.entries.is_empty() {
            return Ok(raft_reply(group.raft.append_entries(request).await));
        }
        let Ok(ordered) = group.append_order.clone().try_lock_owned() else {
            return Ok(AppendReply::Busy);
        };
        let Some(body) = body else {
            let _ordered = ordered;
            return Ok(raft_reply(group.raft.append_entries(request).await));
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
        tokio::spawn(async move {
            let (_ordered, _body, _destination) = (ordered, body, destination);
            raft_reply(group.raft.append_entries(request).await)
        })
        .await
        .map_err(io::Error::other)
    }
}

fn raft_reply(
    result: Result<openraft::raft::AppendResult<RaftTypes>, RaftError<RaftTypes>>,
) -> AppendReply {
    AppendReply::Raft(result.map(AppendEntriesResponse::from))
}
