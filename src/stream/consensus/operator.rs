//! `logkeeper admin`: the operator's client. It reaches the keepers'
//! application lane with an administrator's certificate, and their admin
//! listeners over HTTP or mutual TLS, so creating, inspecting, moving and
//! draining streams and keepers needs no program of one's own.

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    path::Path,
    time::Duration,
};

use journal_contract::{JournalError, StreamId};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt},
    net::TcpStream,
    time::timeout,
};
use tokio_rustls::TlsConnector;
use uuid::Uuid;

use super::{Address, Client, Configuration, Credentials, Domains, Keepers, assignment, invalid};
use crate::stream::transport;

/// One admin HTTP request, connect to last byte.
pub(super) const ADMIN_FETCH_TIMEOUT: Duration = Duration::from_secs(10);
/// How often `drain` and `decommission` poll the keeper's progress.
const DRAIN_POLL: Duration = Duration::from_secs(1);
/// How long `drain` waits for leadership to move by default.
const DRAIN_WAIT: Duration = Duration::from_secs(120);
const DECOMMISSION_WAIT: Duration = Duration::from_secs(600);
/// The largest admin answer kept; a `/metrics` page is far smaller.
const MAX_RESPONSE: u64 = 64 * 1024 * 1024;

fn default_deadline_ms() -> u64 {
    10_000
}

fn default_admin_mtls() -> bool {
    true
}

/// What `logkeeper admin` reads from `--config`: an administrator's
/// credentials and where the keepers listen.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OperatorConfig {
    /// A client certificate whose URI is in the keepers' `administrators`.
    pub tls: Credentials,
    /// Application addresses of every keeper.
    pub keepers: Keepers,
    /// The keeper that assigns stream genesis.
    pub catalog: Uuid,
    /// The replicated catalog's voters, when the keepers run one.
    #[serde(default)]
    pub catalog_voters: Option<[Uuid; 3]>,
    /// Every keeper's admin listener. Status, problems, drain and
    /// decommission read them.
    #[serde(default)]
    pub admin: BTreeMap<Uuid, Address>,
    /// Whether the admin listeners require mutual TLS (the default). Plain
    /// HTTP only reaches loopback listeners.
    #[serde(default = "default_admin_mtls")]
    pub admin_mtls: bool,
    /// Failure domains of the keepers eligible for new streams; `create`
    /// without `--voters` places the stream among them.
    #[serde(default)]
    pub placement: Option<Domains>,
    /// Deadline for each client operation, in milliseconds.
    #[serde(default = "default_deadline_ms")]
    pub deadline_ms: u64,
    /// The keepers' offload store, for `export-stream`, `import-stream`
    /// and `restore-stream`.
    #[serde(default)]
    pub offload: Option<super::OffloadConfig>,
}

impl OperatorConfig {
    pub fn read(path: &Path) -> io::Result<Self> {
        Ok(serde_json::from_slice(&std::fs::read(path)?)?)
    }
}

/// An operator session: one consensus client and the admin listeners.
pub struct Operator {
    config: OperatorConfig,
    client: Client,
    admin_tls: Option<TlsConnector>,
}

/// One replica as its keeper reports it.
#[derive(Debug, Serialize)]
pub struct ReplicaReport {
    pub keeper: Uuid,
    pub reachable: bool,
    /// `healthy`, `quarantined`, `none` or `unknown`.
    pub replica: &'static str,
    pub accepting: Option<bool>,
    pub streams: Option<u32>,
    pub led: Option<u32>,
}

/// `logkeeper admin status --stream`.
#[derive(Debug, Serialize)]
pub struct StreamReport {
    pub stream: Uuid,
    pub configuration: Option<Configuration>,
    pub leader: Option<Uuid>,
    pub head: Option<u64>,
    pub replicas: Vec<ReplicaReport>,
    /// The `/problems` entries the voters' admin listeners report for it.
    pub problems: Vec<Value>,
    /// Errors met while collecting the report.
    pub errors: Vec<String>,
}

/// One keeper's answer to a cluster-wide question.
#[derive(Debug, Serialize)]
pub struct KeeperAnswer {
    pub keeper: Uuid,
    pub status: Option<u16>,
    pub error: Option<String>,
}

/// `logkeeper admin problems`: every keeper's `/problems`, merged by stream.
#[derive(Debug, Serialize)]
pub struct ClusterProblems {
    pub keepers: Vec<KeeperAnswer>,
    pub problem_count: usize,
    pub streams: Vec<ClusterProblem>,
}

#[derive(Debug, Serialize)]
pub struct ClusterProblem {
    pub stream: String,
    pub reasons: BTreeSet<String>,
    /// The keepers that report it, with each one's own entry.
    pub reported_by: BTreeMap<Uuid, Value>,
}

impl Operator {
    pub fn new(config: OperatorConfig) -> io::Result<Self> {
        if config.deadline_ms == 0 {
            return Err(invalid("deadline_ms must be positive"));
        }
        let client = Client::new(
            &config.tls,
            config.keepers.clone(),
            config.catalog,
            Duration::from_millis(config.deadline_ms),
        )?;
        let client = match config.catalog_voters {
            Some(voters) => client.with_catalog_voters(voters),
            None => client,
        };
        let admin_tls = if config.admin_mtls {
            Some(config.tls.client_protocol(b"http/1.1")?.0)
        } else {
            None
        };
        Ok(Self {
            config,
            client,
            admin_tls,
        })
    }

    pub fn client(&self) -> &Client {
        &self.client
    }

    /// Creates `stream` on `voters`, or on three keepers of `placement` in
    /// distinct domains. Retrying with the same arguments is safe.
    pub async fn create(
        &self,
        stream: StreamId,
        voters: Option<[Uuid; 3]>,
        quota_bytes: u64,
    ) -> io::Result<Configuration> {
        let voters = match (voters, &self.config.placement) {
            (Some(voters), _) => voters,
            (None, Some(placement)) => assignment::choose(stream, placement).ok_or_else(|| {
                invalid("placement does not hold three keepers in distinct domains")
            })?,
            (None, None) => {
                return Err(invalid(
                    "give --voters, or a placement in the operator configuration",
                ));
            }
        };
        self.client
            .create(stream, voters, quota_bytes)
            .await
            .map_err(journal_error)?;
        self.client
            .configuration(stream)
            .await
            .map_err(journal_error)
    }

    fn offload_store(&self) -> io::Result<super::offload::Store> {
        let config = self.config.offload.as_ref().ok_or_else(|| {
            invalid(
                "name the keepers' offload store under \"offload\" in the operator configuration",
            )
        })?;
        super::offload::Store::open(config)
    }

    /// A stream's configuration, leader, head, replicas and problems. Parts
    /// that cannot be read are left empty and their error recorded.
    pub async fn stream_status(&self, stream: StreamId) -> StreamReport {
        let mut errors = Vec::new();
        let configuration = match self.client.configuration(stream).await {
            Ok(configuration) => Some(configuration),
            Err(error) => {
                errors.push(format!("configuration: {error}"));
                None
            }
        };
        let head = match self.client.head(stream).await {
            Ok(head) => Some(head.0),
            Err(error) => {
                errors.push(format!("head: {error}"));
                None
            }
        };
        let leader = self.client.leader(stream);
        let voters = match configuration {
            Some(configuration) => configuration.voters.to_vec(),
            None => match self.client.claimed_voters(stream).await {
                Ok(Some(voters)) => voters.to_vec(),
                _ => Vec::new(),
            },
        };
        let replicas = futures::future::join_all(voters.iter().map(|keeper| async move {
            match self.client.keeper_status(*keeper, stream).await {
                Ok(status) => ReplicaReport {
                    keeper: *keeper,
                    reachable: true,
                    replica: match status.replica {
                        Some(true) => "healthy",
                        Some(false) => "quarantined",
                        None => "none",
                    },
                    accepting: Some(status.accepting),
                    streams: Some(status.streams),
                    led: Some(status.led),
                },
                Err(_) => ReplicaReport {
                    keeper: *keeper,
                    reachable: false,
                    replica: "unknown",
                    accepting: None,
                    streams: None,
                    led: None,
                },
            }
        }))
        .await;
        let wanted = Uuid::from_u128(stream.0).to_string();
        let mut problems = Vec::new();
        for keeper in &voters {
            if !self.config.admin.contains_key(keeper) {
                continue;
            }
            match self.admin_json(*keeper, "GET", "/problems").await {
                Ok((_, report)) => problems.extend(
                    report["problems"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter(|entry| entry["stream"] == wanted.as_str())
                        .map(|entry| json!({ "keeper": keeper, "problem": entry })),
                ),
                Err(error) => errors.push(format!("problems from {keeper}: {error}")),
            }
        }
        StreamReport {
            stream: Uuid::from_u128(stream.0),
            configuration,
            leader,
            head,
            replicas,
            problems,
            errors,
        }
    }

    /// Replaces `old` with `new` in the stream's current configuration.
    pub async fn replace_voter(
        &self,
        stream: StreamId,
        old: Uuid,
        new: Uuid,
    ) -> io::Result<Configuration> {
        let current = self
            .client
            .configuration(stream)
            .await
            .map_err(journal_error)?;
        if !current.voters.contains(&old) {
            return Err(invalid(format!("{old} is not a voter of the stream")));
        }
        if current.voters.contains(&new) {
            return Err(invalid(format!("{new} is already a voter of the stream")));
        }
        let voters = current
            .voters
            .map(|voter| if voter == old { new } else { voter });
        self.replace(stream, current.revision, voters).await
    }

    /// Replaces the voters at the expected finalized revision.
    pub async fn replace(
        &self,
        stream: StreamId,
        expected: u64,
        voters: [Uuid; 3],
    ) -> io::Result<Configuration> {
        self.client
            .replace(stream, expected, voters)
            .await
            .map_err(journal_error)
    }

    pub async fn prefer_leader(&self, stream: StreamId, keeper: Uuid) -> io::Result<()> {
        self.client
            .prefer_leader(stream, keeper)
            .await
            .map_err(journal_error)
    }

    /// Clears an operator recovery's fence and returns the stream's head.
    pub async fn acknowledge_recovery(&self, stream: StreamId) -> io::Result<u64> {
        self.client
            .acknowledge_recovery(stream)
            .await
            .map(|head| head.0)
            .map_err(journal_error)
    }

    /// Retires `keeper`'s local copy of `stream`, which the current
    /// configuration must no longer name. The stream's leader certifies it.
    pub async fn retire(&self, stream: StreamId, keeper: Uuid) -> io::Result<Value> {
        let configuration = self
            .client
            .configuration(stream)
            .await
            .map_err(journal_error)?;
        if configuration.voters.contains(&keeper) {
            return Err(invalid(format!(
                "{keeper} is still a voter at revision {}; replace it first",
                configuration.revision
            )));
        }
        let authority = self
            .client
            .leader(stream)
            .unwrap_or(configuration.voters[0]);
        let generation = self
            .client
            .replica_generation(stream, keeper)
            .await
            .map_err(journal_error)?;
        self.client
            .retire_copy(
                stream,
                keeper,
                authority,
                configuration.revision,
                generation,
            )
            .await
            .map_err(journal_error)?;
        Ok(json!({
            "stream": Uuid::from_u128(stream.0),
            "keeper": keeper,
            "authority": authority,
            "revision": configuration.revision,
            "generation": generation,
            "retired": true,
        }))
    }

    /// Every keeper's `/problems`, merged by stream.
    pub async fn problems(&self) -> ClusterProblems {
        let answers =
            futures::future::join_all(self.config.admin.keys().map(|keeper| async move {
                (*keeper, self.admin_json(*keeper, "GET", "/problems").await)
            }))
            .await;
        let mut keepers = Vec::new();
        let mut streams = BTreeMap::<String, ClusterProblem>::new();
        for (keeper, answer) in answers {
            match answer {
                Ok((status, report)) => {
                    keepers.push(KeeperAnswer {
                        keeper,
                        status: Some(status),
                        error: None,
                    });
                    for entry in report["problems"].as_array().into_iter().flatten() {
                        let stream = entry["stream"].as_str().unwrap_or_default().to_owned();
                        let merged =
                            streams
                                .entry(stream.clone())
                                .or_insert_with(|| ClusterProblem {
                                    stream,
                                    reasons: BTreeSet::new(),
                                    reported_by: BTreeMap::new(),
                                });
                        merged.reasons.extend(
                            entry["reasons"]
                                .as_array()
                                .into_iter()
                                .flatten()
                                .filter_map(Value::as_str)
                                .map(str::to_owned),
                        );
                        merged.reported_by.insert(keeper, entry.clone());
                    }
                }
                Err(error) => keepers.push(KeeperAnswer {
                    keeper,
                    status: None,
                    error: Some(error.to_string()),
                }),
            }
        }
        ClusterProblems {
            keepers,
            problem_count: streams.len(),
            streams: streams.into_values().collect(),
        }
    }

    /// Sets `keeper`'s durable operator mode with `POST path` (`/drain`,
    /// `/undrain` or `/decommission`) and returns its `/drain` report.
    pub async fn set_mode(&self, keeper: Uuid, path: &str) -> io::Result<Value> {
        let (status, report) = self.admin_json(keeper, "POST", path).await?;
        if status != 200 {
            return Err(io::Error::other(format!(
                "keeper {keeper} refused {path} with {status}: {report}"
            )));
        }
        Ok(report)
    }

    /// `keeper`'s `/drain` report: its mode and what is left to move.
    pub async fn drain_status(&self, keeper: Uuid) -> io::Result<Value> {
        Ok(self.admin_json(keeper, "GET", "/drain").await?.1)
    }

    /// Polls `keeper`'s `/drain` report until `done` is true in it or
    /// `wait` passes, calling `progress` with each report. Returns the last
    /// report and whether it is done.
    pub async fn wait_for(
        &self,
        keeper: Uuid,
        done: &str,
        wait: Duration,
        mut progress: impl FnMut(&Value),
    ) -> io::Result<(Value, bool)> {
        let end = tokio::time::Instant::now() + wait;
        loop {
            let report = self.drain_status(keeper).await?;
            progress(&report);
            if report[done] == true {
                return Ok((report, true));
            }
            if tokio::time::Instant::now() >= end {
                return Ok((report, false));
            }
            tokio::time::sleep(DRAIN_POLL).await;
        }
    }

    /// `GET /status` from one keeper's admin listener.
    pub async fn keeper_status(&self, keeper: Uuid) -> io::Result<Value> {
        Ok(self.admin_json(keeper, "GET", "/status").await?.1)
    }

    /// Sends one request to `keeper`'s admin listener and decodes its JSON
    /// answer, whatever its status.
    pub(super) async fn admin_json(
        &self,
        keeper: Uuid,
        method: &str,
        path: &str,
    ) -> io::Result<(u16, Value)> {
        let at = self.config.admin.get(&keeper).ok_or_else(|| {
            invalid(format!(
                "no admin listener for keeper {keeper} in the operator configuration"
            ))
        })?;
        let (status, body) = admin_request(
            at.as_str(),
            self.admin_tls.clone(),
            Some(keeper),
            method,
            path,
        )
        .await?;
        let value = serde_json::from_slice(&body).map_err(|error| {
            invalid(format!(
                "keeper {keeper} answered {path} with {status}: {error}"
            ))
        })?;
        Ok((status, value))
    }
}

fn journal_error(error: JournalError) -> io::Error {
    io::Error::other(error.to_string())
}

/// Sends `method path` to an admin listener and returns its HTTP status and
/// body. Over mutual TLS the listener must present `keeper`'s certificate
/// when `keeper` is given.
pub(super) async fn admin_request(
    at: &str,
    tls: Option<TlsConnector>,
    keeper: Option<Uuid>,
    method: &str,
    path: &str,
) -> io::Result<(u16, Vec<u8>)> {
    timeout(ADMIN_FETCH_TIMEOUT, async {
        let socket = TcpStream::connect(at).await?;
        match tls {
            Some(connector) => {
                let name = tokio_rustls::rustls::pki_types::ServerName::try_from("logkeeper")
                    .map_err(io::Error::other)?;
                let mut stream = connector.connect(name, socket).await?;
                if let Some(keeper) = keeper {
                    let (_, session) = stream.get_ref();
                    let presented = transport::leaf(session.peer_certificates())
                        .and_then(transport::keeper_id)?;
                    if presented.0 != keeper.as_u128() {
                        return Err(invalid(format!(
                            "admin listener {at} is not keeper {keeper}"
                        )));
                    }
                }
                exchange(&mut stream, method, path).await
            }
            None => {
                let mut stream = socket;
                exchange(&mut stream, method, path).await
            }
        }
    })
    .await
    .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "admin request timed out"))?
}

async fn exchange<S: AsyncRead + AsyncWrite + Unpin>(
    stream: &mut S,
    method: &str,
    path: &str,
) -> io::Result<(u16, Vec<u8>)> {
    let request = format!(
        "{method} {path} HTTP/1.1\r\nHost: logkeeper\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
    );
    stream.write_all(request.as_bytes()).await?;
    stream.flush().await?;
    let mut raw = Vec::new();
    stream.take(MAX_RESPONSE + 1).read_to_end(&mut raw).await?;
    if raw.len() as u64 > MAX_RESPONSE {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "admin answer is too large",
        ));
    }
    let split = raw
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "admin answer has no headers"))?;
    let status = std::str::from_utf8(&raw[..split])
        .ok()
        .and_then(|head| head.split_whitespace().nth(1))
        .and_then(|code| code.parse().ok())
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "admin answer has no status"))?;
    Ok((status, raw[split + 4..].to_vec()))
}

pub const ADMIN_USAGE: &str = "Usage: logkeeper admin COMMAND --config FILE [--json]
Commands:
  create --stream UUID --quota-bytes N [--voters A,B,C]
  status --stream UUID | status --keeper UUID
  replace --stream UUID (--old KEEPER --new KEEPER | --expected REVISION --voters A,B,C)
  prefer-leader --stream UUID --keeper KEEPER
  acknowledge-recovery --stream UUID
  retire --stream UUID --keeper KEEPER
  problems
  drain --keeper KEEPER [--wait-secs N] | undrain --keeper KEEPER | drain-status --keeper KEEPER
  decommission --keeper KEEPER [--wait-secs N]
  clear-quarantine --keeper KEEPER --stream UUID
  finalize-version
  offload-status --stream UUID
  export-stream --stream UUID --to DIRECTORY
  import-stream --from DIRECTORY --stream NEW_UUID --quota-bytes N [--voters A,B,C]
  restore-stream --from-stream UUID --stream NEW_UUID --quota-bytes N [--voters A,B,C] [--floor LSN] --acknowledge-data-loss";

/// The outcome of one `logkeeper admin` command: what to print, and
/// whether the command succeeded.
pub struct AdminOutcome {
    pub report: Value,
    pub ok: bool,
    /// `--json`: print the report as JSON instead of `key: value` lines.
    pub json: bool,
}

/// Parses and runs `logkeeper admin ARGS`.
pub async fn admin_command(args: &[String]) -> io::Result<AdminOutcome> {
    let usage = || invalid(ADMIN_USAGE);
    let (command, rest) = args.split_first().ok_or_else(usage)?;
    let mut flags = BTreeMap::<&str, &str>::new();
    let mut json_output = false;
    let mut iter = rest.iter();
    while let Some(flag) = iter.next() {
        if flag == "--json" {
            json_output = true;
            continue;
        }
        if flag == "--acknowledge-data-loss" {
            flags.insert("acknowledge-data-loss", "yes");
            continue;
        }
        let name = flag.strip_prefix("--").ok_or_else(usage)?;
        let value = iter.next().ok_or_else(usage)?;
        if flags.insert(name, value).is_some() {
            return Err(usage());
        }
    }
    let config = flags.remove("config").ok_or_else(usage)?;
    let operator = Operator::new(OperatorConfig::read(Path::new(config))?)?;
    let mut outcome = operator.run(command, flags).await?;
    outcome.json = json_output;
    Ok(outcome)
}

fn stream_flag(flags: &mut BTreeMap<&str, &str>) -> io::Result<StreamId> {
    let raw = flags.remove("stream").ok_or_else(|| invalid(ADMIN_USAGE))?;
    Ok(StreamId(parse_uuid(raw)?.as_u128()))
}

fn keeper_flag(flags: &mut BTreeMap<&str, &str>, name: &str) -> io::Result<Uuid> {
    parse_uuid(flags.remove(name).ok_or_else(|| invalid(ADMIN_USAGE))?)
}

fn wait_flag(flags: &mut BTreeMap<&str, &str>, default: Duration) -> io::Result<Duration> {
    match flags.remove("wait-secs") {
        Some(raw) => raw
            .parse::<u64>()
            .map(Duration::from_secs)
            .map_err(|error| invalid(format!("--wait-secs: {error}"))),
        None => Ok(default),
    }
}

fn no_remaining_flags(command: &str, flags: &BTreeMap<&str, &str>) -> io::Result<()> {
    if let Some(flag) = flags.keys().next() {
        return Err(invalid(format!("unknown flag --{flag} for {command}")));
    }
    Ok(())
}

fn parse_uuid(raw: &str) -> io::Result<Uuid> {
    Uuid::parse_str(raw).map_err(|error| invalid(format!("{raw}: {error}")))
}

fn parse_voters(raw: &str) -> io::Result<[Uuid; 3]> {
    let voters = raw
        .split(',')
        .map(parse_uuid)
        .collect::<io::Result<Vec<_>>>()?;
    <[Uuid; 3]>::try_from(voters).map_err(|_| invalid("--voters takes three keeper UUIDs"))
}

impl Operator {
    async fn run(
        &self,
        command: &str,
        mut flags: BTreeMap<&str, &str>,
    ) -> io::Result<AdminOutcome> {
        let done = |report: Value| AdminOutcome {
            report,
            ok: true,
            json: false,
        };
        let outcome = match command {
            "offload-status" => {
                let stream = stream_flag(&mut flags)?;
                let status = self
                    .client
                    .offload_status(stream, false)
                    .await
                    .map_err(journal_error)?;
                done(serde_json::to_value(status)?)
            }
            "export-stream" => {
                let stream = stream_flag(&mut flags)?;
                let to = flags.remove("to").ok_or_else(|| invalid(ADMIN_USAGE))?;
                let store = self.offload_store()?;
                let manifest =
                    super::offload::transfer::export(&self.client, &store, stream, Path::new(to))
                        .await?;
                done(json!({
                    "stream": manifest.stream,
                    "floor": manifest.floor.0,
                    "head": manifest.head.0,
                    "epoch": manifest.epoch.0,
                    "objects": manifest.parts.len(),
                    "directory": to,
                }))
            }
            "import-stream" | "restore-stream" => {
                let target = stream_flag(&mut flags)?;
                let quota = flags
                    .remove("quota-bytes")
                    .ok_or_else(|| invalid(ADMIN_USAGE))?
                    .parse::<u64>()
                    .map_err(|error| invalid(format!("--quota-bytes: {error}")))?;
                let voters = flags.remove("voters").map(parse_voters).transpose()?;
                let store = self.offload_store()?;
                let (loaded, source) = if command == "import-stream" {
                    let from = flags.remove("from").ok_or_else(|| invalid(ADMIN_USAGE))?;
                    (
                        super::offload::transfer::read_export(Path::new(from))?,
                        json!(from),
                    )
                } else {
                    let source = parse_uuid(
                        flags
                            .remove("from-stream")
                            .ok_or_else(|| invalid(ADMIN_USAGE))?,
                    )?;
                    if flags.remove("acknowledge-data-loss").is_none() {
                        return Err(invalid(
                            "restore-stream rebuilds a stream from the object store alone: \
                             records acknowledged after the last upload are lost. Add \
                             --acknowledge-data-loss to proceed",
                        ));
                    }
                    let floor = flags
                        .remove("floor")
                        .map(str::parse::<u64>)
                        .transpose()
                        .map_err(|error| invalid(format!("--floor: {error}")))?
                        .unwrap_or(1);
                    (
                        super::offload::transfer::read_store(
                            &store,
                            StreamId(source.as_u128()),
                            journal_contract::Lsn(floor),
                        )
                        .await?,
                        json!(source),
                    )
                };
                no_remaining_flags(command, &flags)?;
                super::offload::transfer::stage(&store, target, &loaded).await?;
                let configuration = self.create(target, voters, quota).await?;
                let head = self
                    .client
                    .restore_from_offload(target, loaded.floor, loaded.head, loaded.epoch)
                    .await
                    .map_err(journal_error)?;
                done(json!({
                    "stream": Uuid::from_u128(target.0),
                    "source": source,
                    "configuration": configuration,
                    "floor": loaded.floor.0,
                    "head": head.0,
                    "epoch": loaded.epoch.0,
                    "kept": format!("records {}..={}", loaded.floor.0, loaded.head.0),
                }))
            }
            "create" => {
                let stream = stream_flag(&mut flags)?;
                let quota = flags
                    .remove("quota-bytes")
                    .ok_or_else(|| invalid(ADMIN_USAGE))?
                    .parse::<u64>()
                    .map_err(|error| invalid(format!("--quota-bytes: {error}")))?;
                let voters = flags.remove("voters").map(parse_voters).transpose()?;
                done(json!({
                    "stream": Uuid::from_u128(stream.0),
                    "configuration": self.create(stream, voters, quota).await?,
                }))
            }
            "status" => match (flags.contains_key("stream"), flags.contains_key("keeper")) {
                (true, false) => {
                    let report = self.stream_status(stream_flag(&mut flags)?).await;
                    let ok = report.errors.is_empty();
                    AdminOutcome {
                        report: serde_json::to_value(report)?,
                        ok,
                        json: false,
                    }
                }
                (false, true) => {
                    let keeper = keeper_flag(&mut flags, "keeper")?;
                    done(self.keeper_status(keeper).await?)
                }
                _ => return Err(invalid(ADMIN_USAGE)),
            },
            "replace" => {
                let stream = stream_flag(&mut flags)?;
                let configuration = match (flags.remove("old"), flags.remove("new")) {
                    (Some(old), Some(new)) => {
                        self.replace_voter(stream, parse_uuid(old)?, parse_uuid(new)?)
                            .await?
                    }
                    (None, None) => {
                        let expected = flags
                            .remove("expected")
                            .ok_or_else(|| invalid(ADMIN_USAGE))?
                            .parse::<u64>()
                            .map_err(|error| invalid(format!("--expected: {error}")))?;
                        let voters = parse_voters(
                            flags.remove("voters").ok_or_else(|| invalid(ADMIN_USAGE))?,
                        )?;
                        self.replace(stream, expected, voters).await?
                    }
                    _ => return Err(invalid(ADMIN_USAGE)),
                };
                done(json!({
                    "stream": Uuid::from_u128(stream.0),
                    "configuration": configuration,
                }))
            }
            "prefer-leader" => {
                let stream = stream_flag(&mut flags)?;
                let keeper = keeper_flag(&mut flags, "keeper")?;
                self.prefer_leader(stream, keeper).await?;
                done(json!({
                    "stream": Uuid::from_u128(stream.0),
                    "preferred": keeper,
                }))
            }
            "acknowledge-recovery" => {
                let stream = stream_flag(&mut flags)?;
                done(json!({
                    "stream": Uuid::from_u128(stream.0),
                    "head": self.acknowledge_recovery(stream).await?,
                }))
            }
            "retire" => {
                let stream = stream_flag(&mut flags)?;
                let keeper = keeper_flag(&mut flags, "keeper")?;
                done(self.retire(stream, keeper).await?)
            }
            "problems" => {
                let report = self.problems().await;
                let ok = report.keepers.iter().all(|answer| answer.error.is_none());
                AdminOutcome {
                    report: serde_json::to_value(report)?,
                    ok,
                    json: false,
                }
            }
            "drain" | "decommission" => {
                let keeper = keeper_flag(&mut flags, "keeper")?;
                let (path, condition, default) = if command == "drain" {
                    ("/drain", "drained", DRAIN_WAIT)
                } else {
                    ("/decommission", "safe_to_delete", DECOMMISSION_WAIT)
                };
                let wait = wait_flag(&mut flags, default)?;
                no_remaining_flags(command, &flags)?;
                self.set_mode(keeper, path).await?;
                let (report, finished) = self
                    .wait_for(keeper, condition, wait, |report| {
                        eprintln!(
                            "keeper {keeper}: leads {} streams, hosts {} replicas",
                            report["led"], report["hosted"]
                        );
                    })
                    .await?;
                AdminOutcome {
                    report,
                    ok: finished,
                    json: false,
                }
            }
            "undrain" => {
                let keeper = keeper_flag(&mut flags, "keeper")?;
                no_remaining_flags(command, &flags)?;
                done(self.set_mode(keeper, "/undrain").await?)
            }
            "drain-status" => {
                let keeper = keeper_flag(&mut flags, "keeper")?;
                done(self.drain_status(keeper).await?)
            }
            "clear-quarantine" => {
                let keeper = keeper_flag(&mut flags, "keeper")?;
                let stream = stream_flag(&mut flags)?;
                no_remaining_flags(command, &flags)?;
                self.client
                    .clear_quarantine(keeper, stream)
                    .await
                    .map_err(journal_error)?;
                done(
                    json!({"keeper": keeper, "stream": Uuid::from_u128(stream.0), "cleared": true}),
                )
            }
            "finalize-version" => {
                no_remaining_flags(command, &flags)?;
                let version = self
                    .client
                    .finalize_version(super::CLUSTER_VERSION_CURRENT)
                    .await
                    .map_err(journal_error)?;
                done(json!({"cluster_version": version}))
            }
            _ => return Err(invalid(ADMIN_USAGE)),
        };
        no_remaining_flags(command, &flags)?;
        Ok(outcome)
    }
}

/// Renders a report as indented `key: value` lines for a terminal.
pub fn render(value: &Value) -> String {
    let mut out = String::new();
    render_into(&mut out, value, 0);
    out
}

fn render_into(out: &mut String, value: &Value, depth: usize) {
    let pad = "  ".repeat(depth);
    match value {
        Value::Object(map) => {
            for (key, value) in map {
                match value {
                    Value::Object(inner) if !inner.is_empty() => {
                        out.push_str(&format!("{pad}{key}:\n"));
                        render_into(out, value, depth + 1);
                    }
                    Value::Array(items) if items.iter().any(|item| item.is_object()) => {
                        out.push_str(&format!("{pad}{key}:\n"));
                        render_into(out, value, depth + 1);
                    }
                    _ => out.push_str(&format!("{pad}{key}: {}\n", scalar(value))),
                }
            }
        }
        Value::Array(items) => {
            for item in items {
                if item.is_object() {
                    out.push_str(&format!("{pad}-\n"));
                    render_into(out, item, depth + 1);
                } else {
                    out.push_str(&format!("{pad}- {}\n", scalar(item)));
                }
            }
        }
        _ => out.push_str(&format!("{pad}{}\n", scalar(value))),
    }
}

fn scalar(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Null => "-".into(),
        Value::Array(items) => items.iter().map(scalar).collect::<Vec<_>>().join(", "),
        Value::Object(map) if map.is_empty() => "{}".into(),
        other => other.to_string(),
    }
}
