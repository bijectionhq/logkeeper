use super::{
    ApplicationRoute, Checkpoint, Failure, ManagementReply as Reply, ManagementRequest as Request,
    PublishedRoute, RouteBinding, invalid, read, write,
};
use crate::ordered::daemon::{
    GroupConfig, InstalledGroup, Manifest, Room, TlsPeers, group_directory,
    install_decision::{InstallDecision, install_group, may_serve},
};
use crate::ordered::{
    Fingerprint, Placement, Principal,
    replication::{DurableVoter, transport::RemoteVoter},
    service::Coordinator,
};
use crate::server::durability::{sync_directory, sync_file};
use parking_lot::Mutex;
use serde::{Serialize, de::DeserializeOwned};
use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
    time::Duration,
};
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_rustls::TlsConnector;
use uuid::Uuid;

const DEFINITION: &str = "group.json";
const PUBLICATION: &str = "route.json";
const RETIREMENT: &str = "retired.json";

pub(in crate::ordered::daemon) struct Registry {
    path: PathBuf,
    _lock: File,
    voter: Uuid,
    certificate: Fingerprint,
    public_key: Fingerprint,
    management: BTreeMap<Fingerprint, Principal>,
    connector: TlsConnector,
    exchange_ms: u64,
    state: Mutex<Catalog>,
}

#[derive(Default)]
struct Catalog {
    rooms: BTreeMap<Fingerprint, Arc<Room>>,
    groups: BTreeMap<Uuid, Registered>,
    pending_bindings: BTreeMap<Uuid, RouteBinding>,
}

struct Registered {
    definition: Vec<u8>,
    route: ApplicationRoute,
    binding: Option<RouteBinding>,
    retired: Option<Checkpoint>,
}

impl Registry {
    pub(in crate::ordered::daemon) fn recover(
        manifest: Manifest,
        groups: BTreeMap<Fingerprint, GroupConfig>,
        connector: TlsConnector,
        public_key: Fingerprint,
    ) -> Result<Self, Failure> {
        let certificate = manifest.credentials.certificate_pin()?;
        let mut management = BTreeMap::new();
        for client in manifest.management {
            if client.certificate == certificate
                || management
                    .insert(client.certificate, client.role.into())
                    .is_some()
            {
                return Err(invalid("invalid ordered management credential").into());
            }
        }
        let path = manifest.directory.join("runtime-v1");
        match fs::create_dir(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.into()),
        }
        sync_directory(&manifest.directory)?;
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path.join("lock"))?;
        fs2::FileExt::try_lock_exclusive(&lock)?;
        let mut registry = Self {
            path,
            _lock: lock,
            voter: manifest.voter,
            certificate,
            public_key,
            management,
            connector,
            exchange_ms: manifest.exchange_ms,
            state: Mutex::default(),
        };
        let mut state = Catalog::default();
        for (digest, config) in groups {
            let directory = manifest.directory.join(group_directory(digest));
            let room = registry.open(config, &directory, false)?;
            state.rooms.insert(digest, room);
        }
        sync_directory(&registry.path)?;
        for entry in fs::read_dir(&registry.path)? {
            let entry = entry?;
            if !entry.file_type()?.is_dir()
                || entry.file_name().as_encoded_bytes().starts_with(b".")
            {
                continue;
            }
            let deployment = entry
                .file_name()
                .to_str()
                .and_then(|name| Uuid::parse_str(name).ok())
                .ok_or_else(|| invalid("invalid ordered deployment media path"))?;
            registry.recover_group(&mut state, deployment, &entry.path())?;
        }
        *registry.state.get_mut() = state;
        Ok(registry)
    }

    fn recover_group(
        &self,
        state: &mut Catalog,
        deployment: Uuid,
        path: &Path,
    ) -> Result<(), Failure> {
        let Some(group) = load::<InstalledGroup>(path, DEFINITION)? else {
            return Err(invalid("ordered deployment has no group definition").into());
        };
        if group.placement.deployment != deployment || group.predecessor.is_some() {
            return Err(invalid("invalid runtime deployment definition").into());
        }
        let definition = serde_json::to_vec(&group)?;
        let config = group.config()?;
        let route = self.route(&config);
        if state
            .rooms
            .values()
            .any(|room| room.placement.deployment == deployment)
        {
            return Err(invalid("duplicate ordered deployment").into());
        }
        let binding = load(path, PUBLICATION)?;
        if let Some(binding) = &binding {
            state.check_binding(deployment, binding)?;
        }
        let retired = load(path, RETIREMENT)?;
        let room = self.open(config, path, false)?;
        sync_directory(path)?;
        state.rooms.insert(route.group, room);
        state.groups.insert(
            deployment,
            Registered {
                definition,
                route,
                binding,
                retired,
            },
        );
        Ok(())
    }

    pub(in crate::ordered::daemon) fn room(
        &self,
        digest: &Fingerprint,
        application: bool,
    ) -> Option<Arc<Room>> {
        let state = self.state.lock();
        let room = state.rooms.get(digest);
        let retired = room
            .and_then(|room| state.groups.get(&room.placement.deployment))
            .is_some_and(|group| group.retired.is_some());
        if may_serve(room.is_some(), application && retired) {
            room.cloned()
        } else {
            None
        }
    }

    pub(in crate::ordered::daemon) async fn exchange(
        self: &Arc<Self>,
        mut channel: impl AsyncRead + AsyncWrite + Unpin,
        certificate: Fingerprint,
    ) -> Result<(), Failure> {
        let principal = self.management.get(&certificate).copied();
        let request = read(&mut channel).await?;
        let reply = match (principal, request) {
            (Some(_), Request::RouteByDeployment { deployment }) => self.discover(
                Some(deployment),
                None,
                principal == Some(Principal::Administrator),
            ),
            (Some(_), Request::RouteByName { name }) => self.discover(None, Some(&name), false),
            (
                Some(Principal::Administrator),
                Request::RetireGroup {
                    placement,
                    final_checkpoint,
                },
            ) => self.retire(placement, final_checkpoint).await?,
            (Some(Principal::Administrator), Request::Enrollment { placement, worker }) => {
                match self.runtime_room(placement) {
                    Some(room) => Reply::Enrollment(room.coordinator.enrollment(worker).await?),
                    None => Reply::Absent,
                }
            }
            (Some(Principal::Administrator), Request::RetirementStatus { deployment }) => {
                let state = self.state.lock();
                match state.groups.get(&deployment) {
                    Some(group) if group.retired.is_some() && group.binding.is_some() => {
                        Reply::RetirementStatus {
                            checkpoint: group.retired.unwrap(),
                            route: PublishedRoute {
                                binding: group.binding.clone().unwrap(),
                                route: group.route.clone(),
                            },
                        }
                    }
                    _ => Reply::Absent,
                }
            }
            (Some(Principal::Administrator), Request::RetirementCheckpoint { placement }) => {
                match self.media_room(placement) {
                    Some(room) => {
                        Reply::RetirementCheckpoint(room.coordinator.retirement_checkpoint().await?)
                    }
                    None => Reply::Absent,
                }
            }
            (Some(Principal::Administrator), request) => {
                let registry = self.clone();
                tokio::task::spawn_blocking(move || match request {
                    Request::InstallGroup {
                        group,
                        expected_absent,
                    } => registry.install(*group, expected_absent),
                    Request::PublishRoute { placement, binding } => {
                        registry.publish(placement, binding)
                    }
                    _ => Ok(Reply::Forbidden),
                })
                .await??
            }
            _ => Reply::Forbidden,
        };
        write(&mut channel, &reply).await?;
        Ok(())
    }

    fn install(&self, group: InstalledGroup, expected_absent: bool) -> Result<Reply, Failure> {
        let deployment = group.placement.deployment;
        if deployment.is_nil()
            || group.predecessor.is_some()
            || !group.predecessor_keys.is_empty()
            || !group.retained_barrier_keys.is_empty()
        {
            return Ok(Reply::Conflict);
        }
        let definition = serde_json::to_vec(&group)?;
        let path = self.path.join(deployment.to_string());
        let mut state = self.state.lock();
        if !state.groups.contains_key(&deployment) && path.try_exists()? {
            sync_directory(&self.path)?;
            self.recover_group(&mut state, deployment, &path)?;
        }
        let existing = state.groups.get(&deployment);
        match install_group(
            existing.map(|entry| entry.retired.is_none() && entry.definition == definition),
            expected_absent,
        ) {
            InstallDecision::AlreadyInstalled => {
                return Ok(Reply::Installed(existing.unwrap().route.clone()));
            }
            InstallDecision::Refuse => return Ok(Reply::Conflict),
            InstallDecision::Persist => {}
        }
        if state
            .rooms
            .values()
            .any(|room| room.placement.deployment == deployment)
        {
            return Ok(Reply::Conflict);
        }
        let config = match group.clone().config() {
            Ok(config) => config,
            Err(_) => return Ok(Reply::Conflict),
        };
        if !self.is_local(&config) {
            return Ok(Reply::Conflict);
        }
        let staged = self.path.join(format!(".{deployment}"));
        if staged.try_exists()? {
            fs::remove_dir_all(&staged)?;
        }
        fs::create_dir(&staged)?;
        let route = self.route(&config);
        let room = self.open(config, &staged, true)?;
        save(&staged, DEFINITION, &group)?;
        fs::rename(staged, &path)?;
        sync_directory(&self.path)?;
        state.rooms.insert(route.group, room);
        state.groups.insert(
            deployment,
            Registered {
                definition,
                route: route.clone(),
                binding: None,
                retired: None,
            },
        );
        Ok(Reply::Installed(route))
    }

    fn publish(&self, placement: Placement, binding: RouteBinding) -> Result<Reply, Failure> {
        let mut state = self.state.lock();
        if state.check_binding(placement.deployment, &binding).is_err() {
            return Ok(Reply::Conflict);
        }
        let Some(group) = state.groups.get(&placement.deployment) else {
            return Ok(Reply::Absent);
        };
        if group.route.placement != placement
            || group.retired.is_some()
            || group.binding.as_ref().is_some_and(|old| *old != binding)
        {
            return Ok(Reply::Conflict);
        }
        state
            .pending_bindings
            .insert(placement.deployment, binding.clone());
        let path = self.path.join(placement.deployment.to_string());
        if !agree_or_save(&path, PUBLICATION, &binding)? {
            return Ok(Reply::Conflict);
        }
        state.pending_bindings.remove(&placement.deployment);
        let group = state.groups.get_mut(&placement.deployment).unwrap();
        group.binding = Some(binding.clone());
        Ok(Reply::Published(PublishedRoute {
            binding,
            route: group.route.clone(),
        }))
    }

    fn runtime_room(&self, placement: Placement) -> Option<Arc<Room>> {
        let state = self.state.lock();
        let group = state.groups.get(&placement.deployment)?;
        (group.route.placement == placement && group.retired.is_none())
            .then(|| state.rooms[&group.route.group].clone())
    }

    fn media_room(&self, placement: Placement) -> Option<Arc<Room>> {
        let state = self.state.lock();
        let group = state.groups.get(&placement.deployment)?;
        (group.route.placement == placement).then(|| state.rooms[&group.route.group].clone())
    }

    fn discover(
        &self,
        deployment: Option<Uuid>,
        name: Option<&str>,
        include_retired: bool,
    ) -> Reply {
        let state = self.state.lock();
        let group = match deployment {
            Some(deployment) => state.groups.get(&deployment),
            None => state.groups.values().find(|group| {
                group
                    .binding
                    .as_ref()
                    .is_some_and(|binding| Some(binding.name.as_str()) == name)
            }),
        };
        match group {
            Some(group)
                if may_serve(
                    group.binding.is_some(),
                    !include_retired && group.retired.is_some(),
                ) =>
            {
                Reply::Published(PublishedRoute {
                    binding: group.binding.clone().unwrap(),
                    route: group.route.clone(),
                })
            }
            _ => Reply::Absent,
        }
    }

    async fn retire(
        self: &Arc<Self>,
        placement: Placement,
        final_checkpoint: Checkpoint,
    ) -> Result<Reply, Failure> {
        let room = {
            let state = self.state.lock();
            let Some(group) = state.groups.get(&placement.deployment) else {
                return Ok(Reply::Absent);
            };
            if group.route.placement != placement {
                return Ok(Reply::Conflict);
            }
            if let Some(retired) = group.retired {
                return Ok(if retired == final_checkpoint {
                    Reply::Retired(retired)
                } else {
                    Reply::Conflict
                });
            }
            state.rooms[&group.route.group].clone()
        };
        if !room
            .coordinator
            .seal_for_retirement(final_checkpoint)
            .await?
        {
            return Ok(Reply::Deferred);
        }
        let registry = self.clone();
        tokio::task::spawn_blocking(move || {
            let mut state = registry.state.lock();
            let group = state
                .groups
                .get_mut(&placement.deployment)
                .ok_or_else(|| invalid("the ordered group disappeared during retirement"))?;
            let path = registry.path.join(placement.deployment.to_string());
            if !agree_or_save(&path, RETIREMENT, &final_checkpoint)? {
                return Ok(Reply::Conflict);
            }
            group.retired = Some(final_checkpoint);
            Ok(Reply::Retired(final_checkpoint))
        })
        .await?
    }

    fn route(&self, config: &GroupConfig) -> ApplicationRoute {
        ApplicationRoute {
            placement: config.group.placement(),
            group: config.group.identity(),
            endpoints: config.members.values().cloned().collect(),
            maximum_frame: config.max_frame,
            exchange_ms: self.exchange_ms,
            verification_keys: config.keys.barrier_keys().into_iter().collect(),
            successors: Vec::new(),
        }
    }

    fn is_local(&self, config: &GroupConfig) -> bool {
        config
            .members
            .get(&self.voter)
            .is_some_and(|local| local.certificate == self.certificate)
            && config.keys.active.get(&self.voter) == Some(&self.public_key)
    }

    fn open(
        &self,
        config: GroupConfig,
        path: &Path,
        initialize: bool,
    ) -> Result<Arc<Room>, Failure> {
        if !self.is_local(&config) {
            return Err(invalid(
                "the configured receipt and TLS keys do not identify the installed voter",
            )
            .into());
        }
        let digest = config.group.identity();
        let placement = config.group.placement();
        let voter = if initialize {
            DurableVoter::initialize(config.group.clone(), self.voter, path)?
        } else {
            DurableVoter::recover(config.group.clone(), self.voter, path)?
        };
        let members = Arc::new(config.members);
        let tls = TlsPeers {
            connector: self.connector.clone(),
            group: digest,
            members: members.clone(),
        };
        let deadline = Duration::from_millis(self.exchange_ms);
        let peers = members
            .keys()
            .map(|peer| RemoteVoter::new(&config.group, *peer, tls.clone(), deadline))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Arc::new(Room {
            placement,
            voter,
            coordinator: Coordinator::new(config.group, peers),
            voters: config.voters,
            clients: config.clients,
            max_frame: config.max_frame,
        }))
    }
}

impl Catalog {
    fn check_binding(&self, deployment: Uuid, binding: &RouteBinding) -> io::Result<()> {
        if self.pending_bindings.iter().any(|(id, pending)| {
            if *id == deployment {
                pending != binding
            } else {
                pending.name == binding.name
            }
        }) {
            return Err(invalid("conflicting pending ordered deployment binding"));
        }
        if binding.name.is_empty()
            || binding.name.len() > 255
            || binding.organization.is_empty()
            || binding.organization.len() > 255
            || self.groups.iter().any(|(id, other)| {
                *id != deployment
                    && other
                        .binding
                        .as_ref()
                        .is_some_and(|other| other.name == binding.name)
            })
        {
            return Err(invalid("invalid or conflicting ordered deployment binding"));
        }
        Ok(())
    }
}

fn load<T: DeserializeOwned>(directory: &Path, name: &str) -> Result<Option<T>, Failure> {
    let file = match File::open(directory.join(name)) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    let mut bytes = Vec::new();
    (&file)
        .take(super::MAX_FRAME as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > super::MAX_FRAME {
        return Err(invalid("ordered registry record too large").into());
    }
    let value = serde_json::from_slice(&bytes)?;
    sync_file(&file)?;
    Ok(Some(value))
}

fn save(directory: &Path, name: &str, value: &impl Serialize) -> Result<(), Failure> {
    let pending = directory.join(format!(".{name}"));
    let bytes = serde_json::to_vec(value)?;
    let mut file = File::create(&pending)?;
    file.write_all(&bytes)?;
    sync_file(&file)?;
    fs::rename(pending, directory.join(name))?;
    sync_directory(directory)?;
    Ok(())
}

fn agree_or_save<T: Serialize + DeserializeOwned + PartialEq>(
    directory: &Path,
    name: &str,
    expected: &T,
) -> Result<bool, Failure> {
    if let Some(current) = load::<T>(directory, name)? {
        sync_directory(directory)?;
        return Ok(current == *expected);
    }
    save(directory, name, expected)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered::{
        Custody, Cut, Limits, Window,
        daemon::{ClientPin, ClientRole, Endpoint, VoterRoute},
    };
    use std::net::SocketAddr;
    use tokio_rustls::rustls::{ClientConfig, RootCertStore};

    fn group(voter: Uuid) -> InstalledGroup {
        InstalledGroup {
            placement: Placement {
                deployment: Uuid::new_v4(),
                incarnation: Uuid::new_v4(),
                group: Uuid::new_v4(),
                generation: 1,
            },
            limits: Limits {
                enrolled_workers: 2,
                replay_holds: 2,
                retry_positions: 16,
                retained_data_bytes: 4096,
                maintenance_bytes: 1024,
                serving_lease: 50,
                clock_drift: 2,
            },
            initial_checkpoint: Checkpoint {
                cut: Cut {
                    next_lsn: 0,
                    history: [99; 32],
                },
                root: [0; 32],
                manifest: [0; 32],
                custody: Custody {
                    allocation: Uuid::new_v4(),
                    revision: 1,
                    provider: [0; 32],
                },
            },
            initial_window: Window {
                allocation: Uuid::new_v4(),
                serial: 1,
                bytes: 3072,
            },
            maximum_prefix_bytes: 64 << 10,
            maximum_application_frame: 2048,
            voters: [voter, Uuid::new_v4(), Uuid::new_v4()]
                .into_iter()
                .zip(1..)
                .map(|(voter, index)| VoterRoute {
                    voter,
                    zone: format!("zone-{index}"),
                    endpoint: Endpoint {
                        address: SocketAddr::from(([127, 0, 0, 1], 20000 + u16::from(index)))
                            .into(),
                        server_name: "localhost".into(),
                        certificate: [index; 32],
                    },
                    receipt_key: [index; 32],
                })
                .collect(),
            clients: vec![ClientPin {
                certificate: [4; 32],
                role: ClientRole::RouteReader,
            }],
            predecessor: None,
            predecessor_keys: Vec::new(),
            retained_barrier_keys: Vec::new(),
        }
    }

    fn registry(path: &Path, voter: Uuid) -> Registry {
        let tls = ClientConfig::builder_with_provider(Arc::new(
            tokio_rustls::rustls::crypto::ring::default_provider(),
        ))
        .with_safe_default_protocol_versions()
        .unwrap()
        .with_root_certificates(RootCertStore::empty())
        .with_no_client_auth();
        Registry {
            path: path.to_owned(),
            _lock: File::open(path).unwrap(),
            voter,
            certificate: [1; 32],
            public_key: [1; 32],
            management: BTreeMap::new(),
            connector: TlsConnector::from(Arc::new(tls)),
            exchange_ms: 100,
            state: Mutex::default(),
        }
    }

    #[test]
    fn interrupted_group_install_is_invisible_and_exact_install_recovers() {
        let directory = tempfile::tempdir().unwrap();
        let voter = Uuid::new_v4();
        let group = group(voter);
        let deployment = group.placement.deployment;
        let digest = group.clone().config().unwrap().group.identity();
        let staged = directory.path().join(format!(".{deployment}"));
        fs::create_dir(&staged).unwrap();
        save(&staged, DEFINITION, &group).unwrap();
        let daemon = registry(directory.path(), voter);
        assert!(daemon.room(&digest, false).is_none());
        assert_eq!(
            daemon.install(group.clone(), false).unwrap(),
            Reply::Conflict
        );
        let Reply::Installed(route) = daemon.install(group.clone(), true).unwrap() else {
            panic!()
        };
        assert!(daemon.room(&digest, true).is_some());
        assert_eq!(
            daemon.discover(Some(deployment), None, false),
            Reply::Absent
        );
        assert_eq!(
            daemon.install(group.clone(), true).unwrap(),
            Reply::Installed(route.clone())
        );

        let mut conflicting = group.clone();
        conflicting.maximum_application_frame += 1;
        assert_eq!(daemon.install(conflicting, true).unwrap(), Reply::Conflict);

        let binding = RouteBinding {
            name: "tenant".into(),
            organization: "example".into(),
        };
        let expected = Reply::Published(PublishedRoute {
            binding: binding.clone(),
            route: route.clone(),
        });
        assert_eq!(daemon.publish(group.placement, binding).unwrap(), expected);
        drop(daemon);

        let restored = registry(directory.path(), voter);
        restored
            .recover_group(
                &mut restored.state.lock(),
                deployment,
                &directory.path().join(deployment.to_string()),
            )
            .unwrap();
        assert_eq!(restored.discover(Some(deployment), None, false), expected);
        assert!(restored.room(&digest, true).is_some());
    }
}
