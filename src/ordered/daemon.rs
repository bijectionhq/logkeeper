//! Installed-group daemon with separate mutually authenticated voter and
//! application protocols.

mod install_decision;
mod management;
mod receipt_keys;
mod repair;
mod sign;
mod tls;

pub use management::{
    DaemonClient, ManagementReply, ManagementRequest, PublishedRoute, RouteBinding,
};
pub use sign::BarrierVerifier;
pub use tls::{Credentials, Endpoint, EndpointAddress};

use crate::ordered::{
    Checkpoint, Command, Enrollment, Fingerprint, Limits, Outcome, Placement, Principal, Refusal,
    Request, RequestId, Window,
    replication::{
        DurableVoter, Group,
        transport::{RemoteVoter, serve_voter},
    },
    service::{
        Coordinator, Session,
        wire::{self, Operation, Reply},
    },
};
use crate::server::durability::sync_directory;
use receipt_keys::ReceiptKeys;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, Read};
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use std::time::Duration;
use tls::{APPLICATION, MANAGEMENT, TlsPeers, VOTER, invalid};
use tokio::io::AsyncReadExt;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{OwnedSemaphorePermit, Semaphore};
use tokio::time::timeout;
use tokio_rustls::{TlsAcceptor, TlsConnector};
use tokio_util::{sync::CancellationToken, task::TaskTracker};
use uuid::Uuid;

const MANIFEST_BYTES: u64 = 8 << 20;
type Failure = Box<dyn std::error::Error + Send + Sync>;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub listen: SocketAddr,
    pub directory: PathBuf,
    pub voter: Uuid,
    pub credentials: Credentials,
    pub barrier_key: PathBuf,
    pub maximum_connections: usize,
    pub exchange_ms: u64,
    #[serde(default)]
    pub groups: Vec<InstalledGroup>,
    #[serde(default)]
    pub management: Vec<ClientPin>,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct InstalledGroup {
    pub placement: Placement,
    #[serde(with = "LimitsDocument")]
    pub limits: Limits,
    pub initial_checkpoint: Checkpoint,
    #[serde(with = "WindowDocument")]
    pub initial_window: Window,
    pub maximum_prefix_bytes: usize,
    pub maximum_application_frame: usize,
    pub voters: Vec<VoterRoute>,
    pub clients: Vec<ClientPin>,
    #[serde(default)]
    pub predecessor: Option<Fingerprint>,
    /// Repair authorities from the immediate predecessor's active voter roster.
    #[serde(default)]
    pub predecessor_keys: Vec<[u8; 32]>,
    /// Historical verification only. These keys cannot authorize repair.
    #[serde(default)]
    pub retained_barrier_keys: Vec<[u8; 32]>,
}

#[derive(Deserialize, Serialize)]
#[serde(remote = "Limits")]
struct LimitsDocument {
    enrolled_workers: usize,
    replay_holds: usize,
    retry_positions: u64,
    retained_data_bytes: u64,
    maintenance_bytes: u64,
    serving_lease: u64,
    clock_drift: u64,
}

#[derive(Deserialize, Serialize)]
#[serde(remote = "Window")]
struct WindowDocument {
    allocation: Uuid,
    serial: u64,
    bytes: u64,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct VoterRoute {
    pub voter: Uuid,
    pub zone: String,
    pub endpoint: Endpoint,
    pub receipt_key: [u8; 32],
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ClientPin {
    pub certificate: Fingerprint,
    pub role: ClientRole,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ClientRole {
    Administrator,
    Worker { enrollment: Enrollment },
    Custodian,
    RouteReader,
}

impl From<ClientRole> for Principal {
    fn from(role: ClientRole) -> Self {
        match role {
            ClientRole::Administrator => Self::Administrator,
            ClientRole::Worker { enrollment } => Self::Worker(enrollment),
            ClientRole::Custodian => Self::Custodian,
            ClientRole::RouteReader => Self::RouteReader,
        }
    }
}

type Voter = RemoteVoter<TlsPeers>;

struct Room {
    placement: Placement,
    voter: DurableVoter,
    coordinator: Coordinator<Voter>,
    voters: BTreeSet<Fingerprint>,
    clients: BTreeMap<Fingerprint, Principal>,
    max_frame: usize,
}

struct GroupConfig {
    group: Group,
    members: BTreeMap<Uuid, Endpoint>,
    voters: BTreeSet<Fingerprint>,
    clients: BTreeMap<Fingerprint, Principal>,
    max_frame: usize,
    keys: ReceiptKeys,
}

struct Admission {
    handshakes: Arc<Semaphore>,
    voters: Arc<Semaphore>,
    applications: Arc<Semaphore>,
}

impl Admission {
    fn new(limit: usize) -> Self {
        Self {
            handshakes: Arc::new(Semaphore::new(limit)),
            voters: Arc::new(Semaphore::new(limit)),
            applications: Arc::new(Semaphore::new(limit)),
        }
    }
}

impl InstalledGroup {
    fn config(self) -> io::Result<GroupConfig> {
        if !valid_frame(self.maximum_application_frame) {
            return Err(invalid("invalid ordered application frame limit"));
        }
        let mut members = BTreeMap::new();
        let mut voters = BTreeSet::new();
        let mut zones = BTreeSet::new();
        let mut addresses = BTreeSet::new();
        let mut receipt_keys = BTreeMap::new();
        let mut unique_keys = BTreeSet::new();
        let mut failure_zones = BTreeMap::new();
        for route in self.voters {
            if route.zone.is_empty()
                || !zones.insert(route.zone.clone())
                || !addresses.insert(route.endpoint.authority())
                || !voters.insert(route.endpoint.certificate)
                || !unique_keys.insert(route.receipt_key)
                || members.insert(route.voter, route.endpoint).is_some()
            {
                return Err(invalid(
                    "ordered voters require distinct identities, routes, and zones",
                ));
            }
            receipt_keys.insert(route.voter, route.receipt_key);
            failure_zones.insert(route.voter, route.zone);
        }
        let mut group = Group::new(
            self.placement,
            self.limits,
            self.initial_checkpoint,
            self.initial_window,
            members.keys().copied(),
            self.maximum_prefix_bytes,
        )
        .map_err(|reason| invalid(format_args!("invalid journal group: {reason:?}")))?;
        let mut anchor = Sha256::new();
        for (voter, endpoint) in &members {
            let zone = &failure_zones[voter];
            anchor.update(voter.as_bytes());
            anchor.update(endpoint.certificate);
            anchor.update(receipt_keys[voter]);
            anchor.update((zone.len() as u64).to_be_bytes());
            anchor.update(zone.as_bytes());
        }
        group = group.bind_voters(anchor.finalize().into());
        if let Some(predecessor) = self.predecessor {
            if self.predecessor_keys.is_empty() {
                return Err(invalid(
                    "a successor requires its predecessor verification keys",
                ));
            }
            group = group
                .successor(predecessor)
                .map_err(|reason| invalid(format_args!("invalid successor: {reason:?}")))?;
        }
        let mut clients = BTreeMap::new();
        for peer in self.clients {
            let principal = Principal::from(peer.role);
            if voters.contains(&peer.certificate)
                || clients.insert(peer.certificate, principal).is_some()
            {
                return Err(invalid("each certificate has one role in a journal group"));
            }
        }
        if clients.is_empty() {
            return Err(invalid("the ordered journal has no application identities"));
        }
        Ok(GroupConfig {
            group,
            members,
            voters,
            clients,
            max_frame: self.maximum_application_frame,
            keys: ReceiptKeys {
                active: receipt_keys,
                predecessor: self.predecessor_keys,
                retained: self.retained_barrier_keys,
            },
        })
    }
}

impl Manifest {
    pub fn read(path: &Path) -> Result<Self, Failure> {
        let mut bytes = Vec::new();
        File::open(path)?
            .take(MANIFEST_BYTES + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MANIFEST_BYTES {
            return Err(invalid("ordered manifest too large").into());
        }
        Ok(serde_json::from_slice(&bytes)?)
    }

    /// Emits public routing coordinates without exposing TLS or signing keys.
    pub fn application_route(self, deployment: Uuid) -> Result<ApplicationRoute, Failure> {
        let (manifest, groups) = self.resolve()?;
        let mut selected = groups
            .into_iter()
            .filter(|(_, group)| group.group.placement().deployment == deployment);
        let (group, config) = selected
            .next()
            .ok_or_else(|| invalid("the deployment has no installed group"))?;
        if selected.next().is_some() {
            return Err(
                invalid("the installation contains several cohorts for the deployment").into(),
            );
        }
        let verification_keys = config.keys.barrier_keys().into_iter().collect();
        Ok(ApplicationRoute {
            group,
            placement: config.group.placement(),
            endpoints: config.members.into_values().collect(),
            maximum_frame: config.max_frame,
            exchange_ms: manifest.exchange_ms,
            verification_keys,
            successors: Vec::new(),
        })
    }

    /// Explicit first provisioning on fresh media. Serving startup uses only
    /// recovery, so lost installed media cannot silently become an empty vote.
    pub fn initialize(self) -> Result<(), Failure> {
        let (manifest, groups) = self.resolve()?;
        fs::create_dir(&manifest.directory)?;
        for (digest, config) in groups {
            let directory = manifest.directory.join(group_directory(digest));
            fs::create_dir(&directory)?;
            DurableVoter::initialize(config.group, manifest.voter, &directory)?;
        }
        sync_directory(&manifest.directory)?;
        let parent = manifest
            .directory
            .parent()
            .filter(|path| !path.as_os_str().is_empty());
        sync_directory(parent.unwrap_or_else(|| Path::new(".")))?;
        Ok(())
    }

    pub async fn run(self, cancelled: CancellationToken) -> Result<(), Failure> {
        let (manifest, groups) = self.resolve()?;
        let deadline = Duration::from_millis(manifest.exchange_ms);
        let acceptor = manifest.credentials.server()?;
        let connector = manifest.credentials.client(VOTER)?;
        let issuer = Arc::new(sign::Issuer::load(&manifest.barrier_key)?);
        let listen = manifest.listen;
        let admission = Arc::new(Admission::new(manifest.maximum_connections));
        let public_key = issuer.public_key();
        let registry = tokio::task::spawn_blocking(move || {
            management::Registry::recover(manifest, groups, connector, public_key)
        })
        .await??;
        let registry = Arc::new(registry);
        let listener = TcpListener::bind(listen).await?;
        let tasks = TaskTracker::new();
        let result = loop {
            tokio::select! {
                _ = cancelled.cancelled() => break Ok(()),
                accepted = listener.accept() => {
                    let (socket, _) = match accepted {
                        Ok(accepted) => accepted,
                        Err(error) => break Err(error),
                    };
                    let Ok(permit) = Arc::clone(&admission.handshakes).try_acquire_owned() else { continue };
                    let acceptor = acceptor.clone();
                    let registry = Arc::clone(&registry);
                    let admission = Arc::clone(&admission);
                    let issuer = Arc::clone(&issuer);
                    let stopping = cancelled.clone();
                    tasks.spawn(async move {
                        tokio::select! {
                            _ = stopping.cancelled() => {}
                            _ = timeout(deadline, dispatch(&registry, acceptor, socket, &admission, permit, &issuer, deadline)) => {}
                        }
                    });
                }
            }
        };
        cancelled.cancel();
        tasks.close();
        tasks.wait().await;
        result?;
        Ok(())
    }

    fn resolve(mut self) -> io::Result<(Self, BTreeMap<Fingerprint, GroupConfig>)> {
        if self.voter.is_nil()
            || self.exchange_ms == 0
            || !(1..=Semaphore::MAX_PERMITS).contains(&self.maximum_connections)
        {
            return Err(invalid("incomplete ordered installation"));
        }
        let local = self.credentials.certificate_pin()?;
        let mut ready = BTreeMap::new();
        for installed in std::mem::take(&mut self.groups) {
            let config = installed.config()?;
            if config
                .members
                .get(&self.voter)
                .is_none_or(|route| route.certificate != local)
                || ready.insert(config.group.identity(), config).is_some()
            {
                return Err(invalid(
                    "the local voter has mismatched identity or the group is repeated",
                ));
            }
        }
        Ok((self, ready))
    }
}

async fn dispatch(
    registry: &Arc<management::Registry>,
    acceptor: TlsAcceptor,
    socket: TcpStream,
    admission: &Admission,
    handshake: OwnedSemaphorePermit,
    issuer: &sign::Issuer,
    deadline: Duration,
) -> Result<(), Failure> {
    socket.set_nodelay(true)?;
    let mut channel = acceptor.accept(socket).await?;
    let (_, peer) = channel.get_ref();
    let certificate = tls::pin(peer.peer_certificates())?;
    let protocol = peer
        .alpn_protocol()
        .ok_or_else(|| invalid("missing peer protocol"))?
        .to_vec();
    let mut digest = [0; 32];
    channel.read_exact(&mut digest).await?;
    drop(handshake);
    if protocol == MANAGEMENT {
        let _permit = admission.applications.try_acquire()?;
        if digest != [0; 32] {
            return Err(invalid("invalid ordered management scope").into());
        }
        return registry.exchange(channel, certificate).await;
    }
    let room = registry
        .room(&digest, protocol == APPLICATION)
        .ok_or_else(|| invalid("unknown installed group"))?;
    match protocol.as_slice() {
        VOTER if room.voters.contains(&certificate) => {
            let _permit = admission.voters.try_acquire()?;
            serve_voter(&room.voter, channel, digest, deadline).await?;
        }
        APPLICATION => {
            let principal = *room.clients.get(&certificate).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "unknown application credential",
                )
            })?;
            let _permit = admission.applications.try_acquire()?;
            let session = Session::authenticated(room.placement, principal);
            wire::serve(
                &room.coordinator,
                channel,
                session,
                room.max_frame,
                deadline,
                |body| issuer.sign_bytes(body),
            )
            .await?;
        }
        _ => {
            return Err(
                io::Error::new(io::ErrorKind::PermissionDenied, "invalid peer role").into(),
            );
        }
    }
    Ok(())
}

/// An application route resolved during installation and usable during
/// directory outage. Each endpoint is independently pinned.
pub struct Client {
    placement: Placement,
    cohorts: Vec<(Fingerprint, Vec<Endpoint>)>,
    current: AtomicUsize,
    connector: TlsConnector,
    max_frame: usize,
    deadline: Duration,
    barriers: BarrierVerifier,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ApplicationRoute {
    pub group: Fingerprint,
    pub placement: Placement,
    pub endpoints: Vec<Endpoint>,
    pub maximum_frame: usize,
    pub exchange_ms: u64,
    /// Trusted public keys for every signing cohort in this logical placement.
    pub verification_keys: Vec<[u8; 32]>,
    #[serde(default)]
    pub successors: Vec<SuccessorRoute>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SuccessorRoute {
    pub predecessor: Fingerprint,
    pub group: Fingerprint,
    pub endpoints: Vec<Endpoint>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ControlManifest {
    credentials: Credentials,
    route: ApplicationRoute,
}

impl ControlManifest {
    pub async fn execute(path: &Path, action: Command) -> Result<Outcome, Failure> {
        let mut bytes = Vec::new();
        File::open(path)?
            .take(MANIFEST_BYTES + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MANIFEST_BYTES {
            return Err(invalid("ordered control manifest too large").into());
        }
        let config: Self = serde_json::from_slice(&bytes)?;
        let client = Client::new(config.route, &config.credentials)?;
        let Reply::Route(route) = client.call(Operation::Route).await? else {
            return Err(invalid("the journal did not return its installed route").into());
        };
        let request = Request {
            placement: route.placement,
            principal: Principal::Administrator,
            id: RequestId::fresh(route.position, route.retry_positions)
                .map_err(|_| invalid("the control invocation horizon is exhausted"))?,
            command: action,
        };
        let Reply::Decision(decision) = client.call(Operation::Execute(request.clone())).await?
        else {
            return Err(invalid("the journal did not return the administrative decision").into());
        };
        if decision.receipt.request != request.id
            || decision.receipt.principal != request.principal
            || decision.receipt.placement != request.placement
        {
            return Err(invalid("the administrative receipt has a different scope").into());
        }
        decision.receipt.outcome.map_err(|reason| {
            invalid(format_args!("ordered control was refused: {reason:?}")).into()
        })
    }
}

impl Client {
    pub fn new(route: ApplicationRoute, credentials: &Credentials) -> io::Result<Self> {
        if route.endpoints.is_empty() || !valid_frame(route.maximum_frame) || route.exchange_ms == 0
        {
            return Err(invalid("incomplete ordered application route"));
        }
        let connector = credentials.client(APPLICATION)?;
        let barriers = BarrierVerifier::new(route.placement, route.verification_keys)?;
        let mut cohorts = vec![(route.group, route.endpoints)];
        for next in route.successors {
            if next.endpoints.is_empty()
                || cohorts
                    .last()
                    .is_none_or(|(prior, _)| *prior != next.predecessor)
                || cohorts.iter().any(|(id, _)| *id == next.group)
            {
                return Err(invalid(
                    "the installed voter routes do not form one successor chain",
                ));
            }
            cohorts.push((next.group, next.endpoints));
        }
        Ok(Self {
            placement: route.placement,
            cohorts,
            current: AtomicUsize::new(0),
            connector,
            max_frame: route.maximum_frame,
            deadline: Duration::from_millis(route.exchange_ms),
            barriers,
        })
    }

    pub async fn call(&self, operation: Operation) -> Result<Reply, wire::WireError> {
        let current = self.current.load(Ordering::Acquire);
        let mut unavailable = wire::WireError::Timeout;
        for (index, (group, endpoints)) in self.cohorts.iter().enumerate().skip(current) {
            match self.call_cohort(*group, endpoints, &operation).await {
                Ok(Reply::Refused(Refusal::CohortSealed)) if index + 1 < self.cohorts.len() => {}
                Ok(reply) => {
                    if !matches!(&reply, Reply::Refused(_)) {
                        self.current.fetch_max(index, Ordering::AcqRel);
                    }
                    return Ok(reply);
                }
                Err(error) => unavailable = error,
            }
        }
        Err(unavailable)
    }

    async fn call_cohort(
        &self,
        group: Fingerprint,
        endpoints: &[Endpoint],
        operation: &Operation,
    ) -> Result<Reply, wire::WireError> {
        let mut unavailable = wire::WireError::Timeout;
        for endpoint in endpoints {
            let reply = timeout(self.deadline, async {
                let channel = tls::open(&self.connector, endpoint, APPLICATION, group).await?;
                let reply = wire::exchange(
                    channel,
                    self.placement,
                    (*operation).clone(),
                    self.max_frame,
                    self.deadline,
                )
                .await?;
                if let (Reply::Decision(decision), Operation::Execute(original)) =
                    (&reply, operation)
                {
                    if let Some(proof) = decision.barrier {
                        self.barriers.verify(proof, original)?;
                    }
                    if let Some(proof) = &decision.rotation {
                        self.barriers
                            .verify_rotation(proof, group, decision.receipt)?;
                    }
                }
                Ok(reply)
            })
            .await;
            match reply {
                Ok(Ok(reply)) => return Ok(reply),
                Ok(Err(error)) => unavailable = error,
                Err(_) => unavailable = wire::WireError::Timeout,
            }
        }
        Err(unavailable)
    }
}

fn valid_frame(maximum: usize) -> bool {
    maximum >= 1024 && u32::try_from(maximum).is_ok()
}

fn group_directory(digest: Fingerprint) -> String {
    digest
        .into_iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
