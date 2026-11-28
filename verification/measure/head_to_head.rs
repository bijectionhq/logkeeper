//! Head-to-head benchmark of the two `journal_contract::Journal`
//! implementations on separate hosts: the writer-driven journal (client
//! `Writer` over plain keepers) and the consensus keeper (`ConsensusJournal`).
//!
//! The same binary runs in two roles:
//!
//! - `head-to-head agent --listen IP:PORT --root DIR --binary LOGKEEPER --token T`
//!   runs on every keeper host. It writes the files the controller sends,
//!   initializes, spawns and SIGKILLs `logkeeper keeper` processes, reports
//!   their RSS, CPU time and disk use, and echoes bytes for RTT probes. It
//!   only writes below `DIR` and only executes `LOGKEEPER`.
//! - `head-to-head run --backend writer|consensus --keepers IP,IP,IP --token T
//!   CASE [ARGS]` runs on the client host. Each case starts a fresh cluster
//!   (new CA, keeper identities and media) through the agents, runs one
//!   workload through `journal_contract::Journal`, prints one JSON line and
//!   wipes the keepers' media.
//! - `head-to-head rtt --keepers IP,IP,IP --token T` prints the TCP echo RTT
//!   from this host to every agent and between agents.
//!
//! Both backends use 256-byte records, mutual TLS 1.3 from one generated CA,
//! `sync_mode: full` (`F_FULLFSYNC` on macOS), three keepers in three zones
//! (one per host) and the same client concurrency. See `HEAD-TO-HEAD.md`.

use std::{
    collections::{BTreeMap, HashMap},
    error::Error,
    net::{IpAddr, SocketAddr},
    path::{Component, Path, PathBuf},
    process::{Child, Command, Stdio},
    sync::{Arc, Mutex},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use bytes::Bytes;
use futures::{StreamExt, TryStreamExt, future::try_join_all, stream};
use journal_contract::{Epoch, Journal, JournalError, Lsn, StreamId};
use logkeeper::stream::{
    consensus::{CLUSTER_VERSION_CURRENT, ConsensusJournal, JournalConfig},
    keeper::{Sweep, SweepError, sweep_idle},
    transport::{Credentials, TcpTransport},
    wire::KeeperId,
    writer::Writer,
};
use rcgen::{CertificateParams, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair, SanType};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tokio::{
    io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader},
    net::{TcpListener, TcpStream},
    task::JoinSet,
};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

type BenchError = Box<dyn Error + Send + Sync>;
type Result<T> = std::result::Result<T, BenchError>;

const RECORD_BYTES: usize = 256;
const PARALLEL: usize = 64;
const CURRENT: Epoch = Epoch(1);
const NEXT: Epoch = Epoch(2);
const RETRY_LIMIT: Duration = Duration::from_secs(60);
const WRITER: &str = "urn:logkeeper:client:writer";
const SUCCESSOR: &str = "urn:logkeeper:client:successor";
const OBSERVER: &str = "urn:logkeeper:client:observer";

#[tokio::main]
async fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((role, rest)) = args.split_first() else {
        return Err("usage: head-to-head agent|run|rtt ...".into());
    };
    let (flags, positional) = parse(rest)?;
    match role.as_str() {
        "agent" => agent(&flags).await,
        "run" => run(&flags, &positional).await,
        "rtt" => rtt(&Opts::new(&flags)?).await,
        other => Err(format!("unknown role {other}").into()),
    }
}

fn parse(args: &[String]) -> Result<(HashMap<String, String>, Vec<String>)> {
    let mut flags = HashMap::new();
    let mut positional = Vec::new();
    let mut input = args.iter();
    while let Some(arg) = input.next() {
        if let Some(flag) = arg.strip_prefix("--") {
            let value = input
                .next()
                .ok_or_else(|| format!("--{flag} needs a value"))?;
            flags.insert(flag.to_owned(), value.clone());
        } else {
            positional.push(arg.clone());
        }
    }
    Ok((flags, positional))
}

// ---------------------------------------------------------------- agent

struct AgentState {
    root: PathBuf,
    binary: PathBuf,
    token: String,
    children: Mutex<BTreeMap<String, Child>>,
}

async fn agent(flags: &HashMap<String, String>) -> Result<()> {
    let flag = |name: &str| {
        flags
            .get(name)
            .cloned()
            .ok_or_else(|| format!("agent needs --{name}"))
    };
    let root = PathBuf::from(flag("root")?);
    std::fs::create_dir_all(&root)?;
    let state = Arc::new(AgentState {
        root: root.canonicalize()?,
        binary: PathBuf::from(flag("binary")?).canonicalize()?,
        token: flag("token")?,
        children: Mutex::default(),
    });
    let listener = TcpListener::bind(flag("listen")?.parse::<SocketAddr>()?).await?;
    eprintln!(
        "agent on {} root {}",
        listener.local_addr()?,
        state.root.display()
    );
    loop {
        tokio::select! {
            _ = tokio::signal::ctrl_c() => break,
            accepted = listener.accept() => {
                let (socket, _) = accepted?;
                let state = state.clone();
                tokio::spawn(async move {
                    if let Err(error) = serve_agent(socket, state).await {
                        eprintln!("agent request failed: {error}");
                    }
                });
            }
        }
    }
    kill_all(&state);
    Ok(())
}

async fn serve_agent(socket: TcpStream, state: Arc<AgentState>) -> Result<()> {
    socket.set_nodelay(true)?;
    let (read, mut write) = socket.into_split();
    let mut reader = BufReader::new(read);
    let mut line = String::new();
    reader.read_line(&mut line).await?;
    let request: Value = serde_json::from_str(&line)?;
    if request["token"].as_str() != Some(state.token.as_str()) {
        return Err("bad token".into());
    }
    if request["op"] == "echo" {
        write.write_all(b"ok\n").await?;
        let mut byte = [0u8; 1];
        while reader.read(&mut byte).await? != 0 {
            write.write_all(&byte).await?;
        }
        return Ok(());
    }
    let reply = match agent_op(&state, &request).await {
        Ok(reply) => reply,
        Err(error) => json!({"error": error.to_string()}),
    };
    write.write_all(format!("{reply}\n").as_bytes()).await?;
    Ok(())
}

fn below(root: &Path, relative: &str) -> Result<PathBuf> {
    let path = Path::new(relative);
    if path
        .components()
        .any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(format!("path {relative} leaves the agent root").into());
    }
    Ok(root.join(path))
}

fn kill_all(state: &AgentState) {
    let mut children = state.children.lock().unwrap();
    for child in children.values_mut() {
        let _ = child.kill();
        let _ = child.wait();
    }
    children.clear();
}

async fn agent_op(state: &AgentState, request: &Value) -> Result<Value> {
    let text = |name: &str| {
        request[name]
            .as_str()
            .map(str::to_owned)
            .ok_or_else(|| format!("missing {name}"))
    };
    let args = || -> Vec<String> {
        request["args"]
            .as_array()
            .map(|args| {
                args.iter()
                    .filter_map(|arg| arg.as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default()
    };
    match request["op"].as_str().unwrap_or("") {
        "root" => Ok(json!({"root": state.root})),
        "write" => {
            let path = below(&state.root, &text("path")?)?;
            std::fs::create_dir_all(path.parent().unwrap())?;
            std::fs::write(&path, text("data")?)?;
            Ok(json!({"written": path}))
        }
        "mkdir" => {
            let path = below(&state.root, &text("path")?)?;
            std::fs::create_dir_all(&path)?;
            Ok(json!({"created": path}))
        }
        "exec" => {
            let output = Command::new(&state.binary)
                .args(args())
                .current_dir(&state.root)
                .output()?;
            Ok(json!({"status": output.status.code(),
                "stdout": String::from_utf8_lossy(&output.stdout),
                "stderr": String::from_utf8_lossy(&output.stderr)}))
        }
        "spawn" => {
            let name = text("name")?;
            let logs = state.root.join("logs");
            std::fs::create_dir_all(&logs)?;
            let log = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(logs.join(format!("{name}.log")))?;
            let mut children = state.children.lock().unwrap();
            if let Some(child) = children.get_mut(&name)
                && child.try_wait()?.is_none()
            {
                return Err(format!("{name} is already running").into());
            }
            let child = Command::new(&state.binary)
                .args(args())
                .current_dir(&state.root)
                .stdin(Stdio::null())
                .stdout(log.try_clone()?)
                .stderr(log)
                .spawn()?;
            let pid = child.id();
            children.insert(name, child);
            Ok(json!({"pid": pid}))
        }
        "kill" => {
            let name = text("name")?;
            let started = Instant::now();
            let mut child = state
                .children
                .lock()
                .unwrap()
                .remove(&name)
                .ok_or_else(|| format!("{name} is not running"))?;
            // `Child::kill` sends SIGKILL on Unix.
            child.kill()?;
            child.wait()?;
            Ok(json!({"killed": name, "kill_ms": ms(started.elapsed())}))
        }
        "stats" => {
            let mut out = serde_json::Map::new();
            let children = state.children.lock().unwrap();
            for (name, child) in children.iter() {
                let output = Command::new("ps")
                    .args(["-o", "rss=,time=", "-p", &child.id().to_string()])
                    .output()?;
                let text = String::from_utf8_lossy(&output.stdout);
                let mut fields = text.split_whitespace();
                let rss_kib = fields.next().and_then(|v| v.parse::<f64>().ok());
                let cpu = fields.next().map(cpu_seconds);
                out.insert(
                    name.clone(),
                    json!({"rss_mib": rss_kib.map(|v| v / 1024.0), "cpu_seconds": cpu}),
                );
            }
            drop(children);
            let mut disk = serde_json::Map::new();
            for dir in request["dirs"].as_array().into_iter().flatten() {
                if let Some(dir) = dir.as_str() {
                    let (apparent, allocated) = disk_bytes(&below(&state.root, dir)?);
                    disk.insert(
                        dir.into(),
                        json!({"apparent_mib": apparent as f64 / 1048576.0,
                            "allocated_mib": allocated as f64 / 1048576.0}),
                    );
                }
            }
            Ok(json!({"processes": out, "disk": disk}))
        }
        "wipe" => {
            kill_all(state);
            for entry in std::fs::read_dir(&state.root)? {
                let path = entry?.path();
                if path.is_dir() {
                    std::fs::remove_dir_all(&path)?;
                } else {
                    std::fs::remove_file(&path)?;
                }
            }
            Ok(json!({"wiped": state.root}))
        }
        "http" => {
            let port = request["port"].as_u64().ok_or("missing port")? as u16;
            let path = text("path")?;
            let body = tokio::time::timeout(Duration::from_secs(3), async {
                let mut socket = TcpStream::connect(("127.0.0.1", port)).await?;
                socket
                    .write_all(
                        format!("GET {path} HTTP/1.1\r\nHost: keeper\r\nConnection: close\r\n\r\n")
                            .as_bytes(),
                    )
                    .await?;
                let mut body = String::new();
                socket.read_to_string(&mut body).await?;
                Ok::<_, std::io::Error>(body)
            })
            .await;
            match body {
                Ok(Ok(body)) => {
                    let status = body
                        .split_whitespace()
                        .nth(1)
                        .and_then(|code| code.parse::<u16>().ok());
                    Ok(json!({"status": status, "body": body}))
                }
                _ => Ok(json!({"status": null})),
            }
        }
        "probe" => {
            let target: SocketAddr = text("target")?.parse()?;
            let samples = request["n"].as_u64().unwrap_or(200) as usize;
            Ok(echo_rtt(target, &state.token, samples).await?)
        }
        other => Err(format!("unknown op {other}").into()),
    }
}

/// Parses `ps -o time=` output such as `1:02.34` or `1:02:03.45`.
fn cpu_seconds(text: &str) -> f64 {
    let (days, rest) = match text.split_once('-') {
        Some((days, rest)) => (days.parse::<f64>().unwrap_or(0.0), rest),
        None => (0.0, text),
    };
    days * 86400.0
        + rest.split(':').fold(0.0, |total, part| {
            total * 60.0 + part.parse::<f64>().unwrap_or(0.0)
        })
}

/// Apparent and allocated bytes of every file under `path`.
fn disk_bytes(path: &Path) -> (u64, u64) {
    use std::os::unix::fs::MetadataExt;
    std::fs::read_dir(path).map_or((0, 0), |entries| {
        entries
            .flatten()
            .fold((0, 0), |(apparent, allocated), entry| {
                match entry.metadata() {
                    Ok(meta) if meta.is_dir() => {
                        let (a, b) = disk_bytes(&entry.path());
                        (apparent + a, allocated + b)
                    }
                    Ok(meta) => (apparent + meta.len(), allocated + meta.blocks() * 512),
                    Err(_) => (apparent, allocated),
                }
            })
    })
}

async fn echo_rtt(target: SocketAddr, token: &str, samples: usize) -> Result<Value> {
    let mut socket = TcpStream::connect(target).await?;
    socket.set_nodelay(true)?;
    socket
        .write_all(format!("{}\n", json!({"op": "echo", "token": token})).as_bytes())
        .await?;
    let mut ok = [0u8; 3];
    socket.read_exact(&mut ok).await?;
    let mut times = Vec::with_capacity(samples);
    for _ in 0..samples {
        let start = Instant::now();
        socket.write_all(&[1]).await?;
        let mut byte = [0];
        socket.read_exact(&mut byte).await?;
        times.push(start.elapsed());
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    Ok(stats(times))
}

// ----------------------------------------------------------- controller

struct Opts {
    token: String,
    hosts: Vec<IpAddr>,
    agent_port: u16,
    spare_host: usize,
}

impl Opts {
    fn new(flags: &HashMap<String, String>) -> Result<Self> {
        let hosts = flags
            .get("keepers")
            .ok_or("--keepers IP,IP,IP is required")?
            .split(',')
            .map(str::parse)
            .collect::<std::result::Result<Vec<IpAddr>, _>>()?;
        if hosts.len() != 3 {
            return Err("--keepers takes three addresses".into());
        }
        Ok(Self {
            token: flags.get("token").ok_or("--token is required")?.clone(),
            hosts,
            agent_port: flags.get("agent-port").map_or(Ok(7400), |v| v.parse())?,
            spare_host: flags.get("spare-host").map_or(Ok(0), |v| v.parse())?,
        })
    }

    fn agent(&self, host: usize) -> SocketAddr {
        SocketAddr::new(self.hosts[host], self.agent_port)
    }

    async fn call(&self, host: usize, mut request: Value) -> Result<Value> {
        request["token"] = self.token.clone().into();
        let agent = self.agent(host);
        let mut socket = TcpStream::connect(agent).await?;
        socket.write_all(format!("{request}\n").as_bytes()).await?;
        let mut line = String::new();
        BufReader::new(socket).read_line(&mut line).await?;
        let reply: Value = serde_json::from_str(&line)
            .map_err(|error| format!("agent {agent} answered {line:?}: {error}"))?;
        if let Some(error) = reply.get("error") {
            return Err(format!("agent {agent}: {error}").into());
        }
        Ok(reply)
    }
}

async fn rtt(opts: &Opts) -> Result<()> {
    for (host, ip) in opts.hosts.iter().enumerate() {
        let row = echo_rtt(opts.agent(host), &opts.token, 1000).await?;
        println!(
            "{}",
            json!({"case": "rtt", "from": "client", "to": ip, "echo": row})
        );
    }
    for from in 0..3 {
        for to in 0..3 {
            if from == to {
                continue;
            }
            let row = opts
                .call(
                    from,
                    json!({"op": "probe", "target": opts.agent(to).to_string(), "n": 1000}),
                )
                .await?;
            println!(
                "{}",
                json!({"case": "rtt", "from": opts.hosts[from], "to": opts.hosts[to], "echo": row})
            );
        }
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Backend {
    Writer,
    Consensus,
}

impl Backend {
    fn name(self) -> &'static str {
        match self {
            Backend::Writer => "writer",
            Backend::Consensus => "consensus",
        }
    }
}

struct Tuning {
    repair_after_secs: u64,
    park_after_secs: u64,
    repair_limit_secs: u64,
}

struct Node {
    name: &'static str,
    uuid: Uuid,
    host: usize,
    zone: &'static str,
    /// Directory below the agent root.
    dir: String,
    /// Absolute directory on the host.
    path: String,
    app: SocketAddr,
    peer: SocketAddr,
    bulk: SocketAddr,
    admin_port: u16,
    running: bool,
}

impl Node {
    fn id(&self) -> KeeperId {
        KeeperId(self.uuid.as_u128())
    }
}

struct Cluster {
    backend: Backend,
    opts: Opts,
    nodes: Vec<Node>,
    url: String,
    journal_config: Option<JournalConfig>,
    credentials: BTreeMap<&'static str, Credentials>,
    _local: tempfile::TempDir,
}

#[derive(Clone)]
enum Handle {
    Writer(Writer),
    Consensus(ConsensusJournal),
}

impl Handle {
    fn journal(&self) -> &dyn Journal {
        match self {
            Handle::Writer(writer) => writer,
            Handle::Consensus(journal) => journal,
        }
    }

    /// One batch the way RTDB Multi submits it: the writer-driven journal
    /// takes contiguous concurrent `Journal::append` calls and coalesces
    /// them, the consensus journal takes one `append_batch`. A batch of one
    /// is a plain `Journal::append` on both.
    async fn batch(
        &self,
        stream: StreamId,
        epoch: Epoch,
        first: u64,
        count: u64,
        concurrent: bool,
    ) -> Result<Vec<Duration>> {
        let start = Instant::now();
        match self {
            Handle::Consensus(journal) if count > 1 && !concurrent => {
                let records = (first..first + count)
                    .map(|at| (Lsn(at), record()))
                    .collect::<Vec<_>>();
                let last = retry(|| journal.append_batch(stream, epoch, records.clone())).await?;
                assert_eq!(last, Lsn(first + count - 1));
                Ok(vec![start.elapsed(); count as usize])
            }
            _ => {
                try_join_all((first..first + count).map(|at| async move {
                    let lsn =
                        retry(|| self.journal().append(stream, epoch, Lsn(at), record())).await?;
                    assert_eq!(lsn, Lsn(at));
                    Ok::<_, BenchError>(start.elapsed())
                }))
                .await
            }
        }
    }
}

fn now_tag() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

fn pem_credentials(
    dir: &Path,
    issuer: &Issuer<'_, KeyPair>,
    uri: &str,
    purposes: Vec<ExtendedKeyUsagePurpose>,
) -> Result<(String, String, Credentials)> {
    let key = KeyPair::generate()?;
    let mut params = CertificateParams::default();
    params.subject_alt_names = vec![SanType::URI(uri.try_into()?)];
    params.extended_key_usages = purposes;
    let certificate = params.signed_by(&key, issuer)?.pem();
    let private_key = key.serialize_pem();
    let name = uri.rsplit(':').next().unwrap();
    let paths = Credentials {
        certificate: dir.join(format!("{name}.pem")),
        private_key: dir.join(format!("{name}.key")),
        ca: dir.join("ca.pem"),
    };
    std::fs::write(&paths.certificate, &certificate)?;
    std::fs::write(&paths.private_key, &private_key)?;
    Ok((certificate, private_key, paths))
}

impl Cluster {
    async fn start(
        backend: Backend,
        opts: Opts,
        spare: bool,
        tuning: &Tuning,
        max_streams: usize,
    ) -> Result<Self> {
        for host in 0..3 {
            opts.call(host, json!({"op": "wipe"})).await?;
        }
        let mut roots = Vec::new();
        for host in 0..3 {
            let reply = opts.call(host, json!({"op": "root"})).await?;
            roots.push(
                reply["root"]
                    .as_str()
                    .ok_or("agent has no root")?
                    .to_owned(),
            );
        }
        std::fs::create_dir_all("verification/.results/h2h")?;
        let local = tempfile::Builder::new()
            .prefix("client-")
            .tempdir_in("verification/.results/h2h")?;
        let mut params = CertificateParams::default();
        params.is_ca = IsCa::Ca(rcgen::BasicConstraints::Unconstrained);
        let ca_key = KeyPair::generate()?;
        let ca_pem = params.self_signed(&ca_key)?.pem();
        std::fs::write(local.path().join("ca.pem"), &ca_pem)?;
        let issuer = Issuer::new(params, ca_key);
        let mut credentials = BTreeMap::new();
        for uri in [WRITER, SUCCESSOR, OBSERVER] {
            let (_, _, paths) = pem_credentials(
                local.path(),
                &issuer,
                uri,
                vec![ExtendedKeyUsagePurpose::ClientAuth],
            )?;
            credentials.insert(uri, paths);
        }
        let tag = format!("{}-{}", backend.name(), now_tag());
        let layout: &[(&'static str, usize, &'static str, u16)] = &[
            ("a", 0, "zone-a", 0),
            ("b", 1, "zone-b", 0),
            ("c", 2, "zone-c", 0),
            ("spare", opts.spare_host, "zone-a", 1),
        ];
        let count = if spare { 4 } else { 3 };
        let mut nodes = Vec::new();
        for &(name, host, zone, offset) in &layout[..count] {
            let ip = opts.hosts[host];
            let dir = format!("{tag}/{name}");
            let base = match backend {
                Backend::Writer => 7441,
                Backend::Consensus => 5441,
            };
            nodes.push(Node {
                name,
                uuid: Uuid::new_v4(),
                host,
                zone,
                path: format!("{}/{dir}", roots[host]),
                dir,
                app: SocketAddr::new(ip, base + offset),
                peer: SocketAddr::new(ip, 5541 + offset),
                bulk: SocketAddr::new(ip, 5641 + offset),
                admin_port: 5741 + offset,
                running: false,
            });
        }
        let primaries = &nodes[..3];
        let url = format!(
            "logkeeper+tls://{}",
            primaries
                .iter()
                .map(|node| node.app.to_string())
                .collect::<Vec<_>>()
                .join(",")
        );
        let addresses = |pick: fn(&Node) -> SocketAddr| {
            nodes
                .iter()
                .map(|node| (node.uuid.to_string(), Value::from(pick(node).to_string())))
                .collect::<serde_json::Map<_, _>>()
        };
        let domains = nodes
            .iter()
            .map(|node| (node.uuid.to_string(), Value::from(node.zone)))
            .collect::<serde_json::Map<_, _>>();
        let mut catalog_voters = primaries.iter().map(|node| node.uuid).collect::<Vec<_>>();
        catalog_voters.sort();
        let catalog = primaries[0].uuid;
        for node in &nodes {
            let tls_dir = local.path().join(node.name);
            std::fs::create_dir_all(&tls_dir)?;
            std::fs::write(tls_dir.join("ca.pem"), &ca_pem)?;
            let (certificate, private_key, _) = pem_credentials(
                &tls_dir,
                &issuer,
                &format!("urn:logkeeper:keeper:{}", node.uuid),
                vec![
                    ExtendedKeyUsagePurpose::ServerAuth,
                    ExtendedKeyUsagePurpose::ClientAuth,
                ],
            )?;
            let files = [
                ("tls/ca.pem", ca_pem.clone()),
                ("tls/keeper.pem", certificate.clone()),
                ("tls/keeper.key", private_key),
            ];
            for (file, data) in files {
                opts.call(
                    node.host,
                    json!({"op": "write", "path": format!("{}/{file}", node.dir), "data": data}),
                )
                .await?;
            }
            let tls = json!({"certificate": format!("{}/tls/keeper.pem", node.path),
                "private_key": format!("{}/tls/keeper.key", node.path),
                "ca": format!("{}/tls/ca.pem", node.path)});
            let data = format!("{}/data", node.path);
            let config = match backend {
                Backend::Writer => json!({
                    "keeper": node.uuid, "listen": node.app, "data": data, "zone": node.zone,
                    "tls": tls, "clients": [WRITER, SUCCESSOR, OBSERVER], "writers": [WRITER, SUCCESSOR],
                    "limits": {"stream_quota_bytes": 8589934592_u64, "max_record_bytes": 33554432,
                               "round_bytes_per_stream": 4194304, "round_requests": 64},
                    "sync_mode": "full",
                }),
                Backend::Consensus => {
                    let registry = format!("{}/registry", node.dir);
                    opts.call(
                        node.host,
                        json!({"op": "write", "path": format!("{registry}/placement.json"),
                            "data": json!({"catalog": catalog, "domains": domains}).to_string()}),
                    )
                    .await?;
                    let digest = Sha256::digest(certificate.as_bytes());
                    let hex = digest
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect::<String>();
                    opts.call(
                        node.host,
                        json!({"op": "write", "path": format!("{registry}/{}.provision.json", node.uuid),
                            "data": json!({"keeper": node.uuid, "data": data, "domain": node.zone,
                                "certificate_sha256": hex}).to_string()}),
                    )
                    .await?;
                    json!({
                        "keeper": node.uuid, "listen": node.app, "data": data,
                        "enrollment": format!("{}/registry", node.path), "tls": tls,
                        "keepers": addresses(|n| n.app), "peers": addresses(|n| n.peer),
                        "bulk": addresses(|n| n.bulk), "domains": domains,
                        "catalog": catalog, "catalog_voters": catalog_voters,
                        "readers": [OBSERVER], "writers": [WRITER, SUCCESSOR],
                        "administrators": [WRITER, SUCCESSOR],
                        "max_streams": max_streams,
                        "repair_after_secs": tuning.repair_after_secs,
                        "park_after_secs": tuning.park_after_secs,
                        "sync_mode": "full", "async_append": true,
                        "admin": {"listen": format!("127.0.0.1:{}", node.admin_port), "mtls": false},
                    })
                }
            };
            opts.call(
                node.host,
                json!({"op": "write", "path": format!("{}/config.json", node.dir),
                    "data": serde_json::to_string_pretty(&config)?}),
            )
            .await?;
        }
        let journal_config = match backend {
            Backend::Writer => None,
            Backend::Consensus => Some(serde_json::from_value(json!({
                "keepers": addresses(|n| n.app), "catalog": catalog,
                "catalog_voters": catalog_voters,
                "placement": primaries.iter()
                    .map(|node| (node.uuid.to_string(), Value::from(node.zone)))
                    .collect::<serde_json::Map<_, _>>(),
                "quota_bytes": 1u64 << 30, "max_record_bytes": 1 << 20, "deadline_ms": 10000,
                "domain": "zone-a",
            }))?),
        };
        let mut cluster = Self {
            backend,
            opts,
            nodes,
            url,
            journal_config,
            credentials,
            _local: local,
        };
        let started = Instant::now();
        // The writer-driven learner starts on demand; a consensus spare must
        // be in the inventory and running from the start.
        for index in 0..count {
            if backend == Backend::Writer && index == 3 {
                continue;
            }
            cluster.start_node(index).await?;
        }
        for index in 0..count {
            if cluster.nodes[index].running {
                cluster.wait_ready(index).await?;
            }
        }
        if backend == Backend::Consensus {
            cluster.finalize().await?;
        }
        eprintln!(
            "{} cluster ready in {:.1} s",
            backend.name(),
            started.elapsed().as_secs_f64()
        );
        Ok(cluster)
    }

    async fn start_node(&mut self, index: usize) -> Result<()> {
        let node = &self.nodes[index];
        let config = format!("{}/config.json", node.path);
        if self.backend == Backend::Consensus {
            let reply = self
                .opts
                .call(
                    node.host,
                    json!({"op": "exec", "args": ["keeper", "initialize", "--config", config]}),
                )
                .await?;
            if reply["status"] != 0 {
                return Err(format!("initialize {} failed: {reply}", node.name).into());
            }
        }
        self.opts
            .call(
                node.host,
                json!({"op": "spawn", "name": node.name, "args": ["keeper", "--config", config]}),
            )
            .await?;
        self.nodes[index].running = true;
        Ok(())
    }

    async fn wait_ready(&self, index: usize) -> Result<()> {
        let node = &self.nodes[index];
        let deadline = Instant::now() + Duration::from_secs(120);
        loop {
            let ready = match self.backend {
                Backend::Writer => TcpStream::connect(node.app).await.is_ok(),
                Backend::Consensus => {
                    let reply = self
                        .opts
                        .call(
                            node.host,
                            json!({"op": "http", "port": node.admin_port, "path": "/ready"}),
                        )
                        .await?;
                    reply["status"] == 200
                }
            };
            if ready {
                return Ok(());
            }
            if Instant::now() > deadline {
                return Err(format!("keeper {} not ready", node.name).into());
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }

    /// Finalizes this build's cluster level, as a production cluster runs,
    /// so per-keeper catalog leases are enforced, and waits until every
    /// keeper learned it and renewed under it.
    async fn finalize(&self) -> Result<()> {
        let Handle::Consensus(journal) = self.handle(WRITER).await? else {
            unreachable!()
        };
        let deadline = Instant::now() + Duration::from_secs(120);
        while journal.finalize_version(CLUSTER_VERSION_CURRENT).await != Ok(CLUSTER_VERSION_CURRENT)
        {
            if Instant::now() > deadline {
                return Err("cluster level did not finalize".into());
            }
            tokio::time::sleep(Duration::from_millis(250)).await;
        }
        for node in self.nodes.iter().filter(|node| node.running) {
            loop {
                match journal.keeper_status(node.uuid, StreamId(0)).await {
                    Ok(status) if status.cluster_version >= CLUSTER_VERSION_CURRENT => break,
                    _ if Instant::now() > deadline => {
                        return Err(format!("{} did not learn the level", node.name).into());
                    }
                    _ => tokio::time::sleep(Duration::from_millis(250)).await,
                }
            }
        }
        // Keepers enforce leases from their next renewal.
        tokio::time::sleep(Duration::from_secs(12)).await;
        Ok(())
    }

    async fn handle(&self, principal: &str) -> Result<Handle> {
        let credentials = &self.credentials[principal];
        Ok(match self.backend {
            Backend::Writer => {
                let (transport, ensemble) =
                    TcpTransport::discover(&self.url, credentials, Duration::from_secs(5)).await?;
                Handle::Writer(Writer::new(Arc::new(transport), ensemble)?)
            }
            Backend::Consensus => Handle::Consensus(ConsensusJournal::new(
                credentials,
                self.journal_config.as_ref().unwrap(),
            )?),
        })
    }

    async fn kill(&mut self, index: usize) -> Result<Value> {
        let node = &self.nodes[index];
        let reply = self
            .opts
            .call(node.host, json!({"op": "kill", "name": node.name}))
            .await?;
        self.nodes[index].running = false;
        Ok(reply)
    }

    /// Keeper CPU seconds, RSS and disk use, per keeper.
    async fn resources(&self) -> Result<Value> {
        let mut out = serde_json::Map::new();
        for node in &self.nodes {
            let reply = self
                .opts
                .call(
                    node.host,
                    json!({"op": "stats", "dirs": [format!("{}/data", node.dir)]}),
                )
                .await?;
            out.insert(
                node.name.into(),
                json!({"process": reply["processes"][node.name],
                    "disk": reply["disk"][format!("{}/data", node.dir)]}),
            );
        }
        Ok(Value::Object(out))
    }

    async fn wipe(&self) -> Result<()> {
        for host in 0..3 {
            self.opts.call(host, json!({"op": "wipe"})).await?;
        }
        Ok(())
    }
}

fn keeper_cpu(before: &Value, after: &Value) -> Value {
    let mut out = serde_json::Map::new();
    let mut total = 0.0;
    if let Some(nodes) = after.as_object() {
        for (name, row) in nodes {
            if let (Some(a), Some(b)) = (
                row["process"]["cpu_seconds"].as_f64(),
                before[name]["process"]["cpu_seconds"].as_f64(),
            ) {
                total += a - b;
                out.insert(name.clone(), (a - b).into());
            }
        }
    }
    out.insert("total".into(), total.into());
    Value::Object(out)
}

fn client_cpu() -> f64 {
    // SAFETY: getrusage writes into the zeroed struct it is given.
    let mut usage = unsafe { std::mem::zeroed::<libc::rusage>() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
    let seconds = |time: libc::timeval| time.tv_sec as f64 + time.tv_usec as f64 / 1e6;
    seconds(usage.ru_utime) + seconds(usage.ru_stime)
}

fn record() -> Bytes {
    Bytes::from_static(&[7; RECORD_BYTES])
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn stats(mut samples: Vec<Duration>) -> Value {
    if samples.is_empty() {
        return Value::Null;
    }
    samples.sort_unstable();
    let at = |permille: usize| ms(samples[(samples.len() * permille).div_ceil(1000) - 1]);
    json!({"n": samples.len(), "p50_ms": at(500), "p99_ms": at(990), "p999_ms": at(999),
        "max_ms": ms(*samples.last().unwrap())})
}

async fn retry<T, F>(mut call: impl FnMut() -> F) -> Result<T>
where
    F: Future<Output = journal_contract::Result<T>>,
{
    Ok(tokio::time::timeout(RETRY_LIMIT, async {
        loop {
            match call().await {
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(2)).await;
                }
                result => return result,
            }
        }
    })
    .await??)
}

async fn prepare(handle: &Handle, streams: impl IntoIterator<Item = u64>) -> Result<()> {
    stream::iter(streams)
        .map(|id| async move {
            let stream = StreamId(id.into());
            retry(|| handle.journal().create(stream)).await?;
            let head = retry(|| handle.journal().seal(stream, CURRENT)).await?;
            assert_eq!(head, Lsn(0));
            Ok::<_, BenchError>(())
        })
        .buffer_unordered(PARALLEL)
        .try_collect::<Vec<_>>()
        .await?;
    Ok(())
}

async fn seed(handle: &Handle, ids: impl IntoIterator<Item = u64>) -> Result<Vec<(u64, Instant)>> {
    stream::iter(ids)
        .map(|id| async move {
            handle
                .batch(StreamId(id.into()), CURRENT, 1, 1, false)
                .await?;
            Ok((id, Instant::now()))
        })
        .buffer_unordered(PARALLEL)
        .try_collect()
        .await
}

async fn run(flags: &HashMap<String, String>, positional: &[String]) -> Result<()> {
    let backend = match flags.get("backend").map(String::as_str) {
        Some("writer") => Backend::Writer,
        Some("consensus") => Backend::Consensus,
        _ => return Err("--backend writer|consensus is required".into()),
    };
    let opts = Opts::new(flags)?;
    let tuning = Tuning {
        repair_after_secs: flags
            .get("repair-after-secs")
            .map_or(Ok(600), |v| v.parse())?,
        park_after_secs: flags
            .get("park-after-secs")
            .map_or(Ok(600), |v| v.parse())?,
        repair_limit_secs: flags
            .get("repair-limit-secs")
            .map_or(Ok(1200), |v| v.parse())?,
    };
    let concurrent = flags.get("batch-mode").map(String::as_str) == Some("concurrent");
    let [case, rest @ ..] = positional else {
        return Err("usage: head-to-head run ... CASE [ARGS]".into());
    };
    let number = |index: usize, default: u64| -> Result<u64> {
        Ok(rest.get(index).map_or(Ok(default), |v| v.parse())?)
    };
    let spare = case == "repair";
    let mut cluster = Cluster::start(backend, opts, spare, &tuning, 4096).await?;
    let result = match case.as_str() {
        "commit" => {
            let streams = number(0, 1)?;
            let batch = number(1, 1)?;
            let records = number(2, 4000)?;
            let passes = records.div_ceil(streams * batch).max(2);
            commit(
                &cluster,
                streams,
                batch,
                passes,
                number(3, 256)? as usize,
                concurrent,
            )
            .await
        }
        "head" => head(&cluster, number(0, 32)?).await,
        "kill" => kill(&mut cluster, number(0, 1000)?, number(1, 0)? as usize).await,
        "takeover" => takeover(&cluster, number(0, 1000)?, number(1, 32)?).await,
        "repair" => repair(&mut cluster, number(0, 100)?, &tuning).await,
        other => Err(format!("unknown case {other}").into()),
    };
    let wiped = cluster.wipe().await;
    let mut row = result?;
    row["backend"] = backend.name().into();
    row["batch_mode"] = if concurrent { "concurrent" } else { "native" }.into();
    println!("{row}");
    wiped
}

async fn commit(
    cluster: &Cluster,
    streams: u64,
    width: u64,
    passes: u64,
    in_flight: usize,
    concurrent: bool,
) -> Result<Value> {
    let in_flight = in_flight.min(streams as usize);
    let handle = cluster.handle(WRITER).await?;
    prepare(&handle, 1..=streams).await?;
    tokio::time::sleep(Duration::from_millis(500)).await;
    let gate = Arc::new(tokio::sync::Barrier::new(streams as usize + 1));
    let admission = Arc::new(tokio::sync::Semaphore::new(in_flight));
    let mut tasks = JoinSet::new();
    for id in 1..=streams {
        let (handle, gate, admission) = (handle.clone(), gate.clone(), admission.clone());
        tasks.spawn(async move {
            gate.wait().await;
            let (mut queue, mut batches, mut records) = (Vec::new(), Vec::new(), Vec::new());
            for pass in 0..passes {
                let queued = Instant::now();
                let _permit = admission.acquire().await.unwrap();
                queue.push(queued.elapsed());
                let start = Instant::now();
                let acks = handle
                    .batch(
                        StreamId(id.into()),
                        CURRENT,
                        pass * width + 1,
                        width,
                        concurrent,
                    )
                    .await?;
                batches.push(start.elapsed());
                records.extend(acks);
            }
            Ok::<_, BenchError>((queue, batches, records))
        });
    }
    let before = cluster.resources().await?;
    let cpu = client_cpu();
    let start = Instant::now();
    gate.wait().await;
    let (mut queue, mut batches, mut records) = (Vec::new(), Vec::new(), Vec::new());
    while let Some(task) = tasks.join_next().await {
        let (q, b, r) = task??;
        queue.extend(q);
        batches.extend(b);
        records.extend(r);
    }
    let elapsed = start.elapsed();
    let client = client_cpu() - cpu;
    let after = cluster.resources().await?;
    Ok(
        json!({"case": "commit", "streams": streams, "batch": width, "passes": passes,
        "in_flight_streams": in_flight, "seconds": elapsed.as_secs_f64(),
        "records_per_sec": records.len() as f64 / elapsed.as_secs_f64(),
        "record": stats(records), "batch_ack": stats(batches), "producer_queue": stats(queue),
        "keeper_cpu_seconds": keeper_cpu(&before, &after), "client_cpu_seconds": client,
        "resources_after": after}),
    )
}

async fn head(cluster: &Cluster, streams: u64) -> Result<Value> {
    let writer = cluster.handle(WRITER).await?;
    let observer = cluster.handle(OBSERVER).await?;
    prepare(&writer, 1..=streams).await?;
    let mut rows = Vec::new();
    let mut next = vec![1u64; streams as usize + 1];
    for loaded in [false, true] {
        let stop = CancellationToken::new();
        let mut load = JoinSet::new();
        if loaded {
            for id in 1..=streams {
                let (writer, stop) = (writer.clone(), stop.clone());
                let mut at = next[id as usize];
                load.spawn(async move {
                    let mut acks = Vec::new();
                    while !stop.is_cancelled() {
                        acks.extend(
                            writer
                                .batch(StreamId(id.into()), CURRENT, at, 1, false)
                                .await?,
                        );
                        at += 1;
                    }
                    Ok::<_, BenchError>((id, at, acks))
                });
            }
            tokio::time::sleep(Duration::from_millis(500)).await;
        }
        for (caller, handle) in [("writer", &writer), ("observer", &observer)] {
            let start = Instant::now();
            let (times, unavailable) = stream::iter(1..=streams)
                .map(|id| async move {
                    let mut times = Vec::new();
                    let mut unavailable = 0u64;
                    for _ in 0..2000u64.div_ceil(streams).max(32) {
                        let start = Instant::now();
                        match handle.journal().head(StreamId(id.into())).await {
                            Ok(_) => times.push(start.elapsed()),
                            Err(JournalError::Unavailable) => unavailable += 1,
                            Err(error) => return Err(error),
                        }
                    }
                    Ok((times, unavailable))
                })
                .buffer_unordered(PARALLEL)
                .try_fold((Vec::new(), 0), |(mut all, n), (part, failed)| async move {
                    all.extend(part);
                    Ok((all, n + failed))
                })
                .await?;
            rows.push(
                json!({"loaded": loaded, "caller": caller, "head": stats(times),
                "unavailable": unavailable, "seconds": start.elapsed().as_secs_f64()}),
            );
        }
        stop.cancel();
        let mut load_acks = Vec::new();
        while let Some(task) = load.join_next().await {
            let (id, at, acks) = task??;
            next[id as usize] = at;
            load_acks.extend(acks);
        }
        if loaded {
            rows.push(
                json!({"loaded": true, "caller": "background append", "append": stats(load_acks)}),
            );
        }
    }
    Ok(json!({"case": "head", "streams": streams, "rows": rows}))
}

async fn kill(cluster: &mut Cluster, streams: u64, victim: usize) -> Result<Value> {
    let handle = cluster.handle(WRITER).await?;
    prepare(&handle, 1..=streams).await?;
    let warm = seed(&handle, 1..=streams).await?;
    let led_by_victim = match &handle {
        Handle::Consensus(journal) => {
            let victim = cluster.nodes[victim].uuid;
            Value::from(
                (1..=streams)
                    .filter(|id| journal.client().leader(StreamId((*id).into())) == Some(victim))
                    .count(),
            )
        }
        Handle::Writer(_) => Value::Null,
    };
    tokio::time::sleep(Duration::from_millis(500)).await;
    let start = Instant::now();
    let killed = cluster.kill(victim).await?;
    // Every stream retries `Unavailable` until `KILL_LIMIT` after the event;
    // a stream still unacknowledged then is counted, not fatal. A retry that
    // finds its own earlier attempt committed (`Conflict` at head 2) counts
    // as acknowledged at that moment.
    const KILL_LIMIT: Duration = Duration::from_secs(300);
    let outcomes: Vec<std::result::Result<(Duration, Duration), String>> = stream::iter(warm)
        .map(|(id, before)| {
            let journal = handle.journal();
            async move {
                let stream = StreamId(id.into());
                loop {
                    match journal.append(stream, CURRENT, Lsn(2), record()).await {
                        Ok(_) | Err(JournalError::Conflict { head: Lsn(2) }) => {
                            let now = Instant::now();
                            return Ok((now - start, now - before));
                        }
                        Err(JournalError::Unavailable) if start.elapsed() < KILL_LIMIT => {
                            tokio::time::sleep(Duration::from_millis(2)).await;
                        }
                        Err(error) => return Err(format!("{error:?}")),
                    }
                }
            }
        })
        .buffer_unordered(streams as usize)
        .collect()
        .await;
    let samples = outcomes
        .iter()
        .filter_map(|o| o.as_ref().ok())
        .collect::<Vec<_>>();
    let mut errors = BTreeMap::<String, u64>::new();
    for error in outcomes.iter().filter_map(|o| o.as_ref().err()) {
        *errors.entry(error.clone()).or_default() += 1;
    }
    Ok(
        json!({"case": "kill", "streams": streams, "victim": cluster.nodes[victim].name,
        "streams_led_by_victim": led_by_victim, "agent_kill": killed,
        "limit_s": KILL_LIMIT.as_secs(), "acked": samples.len(), "not_acked": errors,
        "event_to_ack": stats(samples.iter().map(|s| s.0).collect()),
        "ack_gap": stats(samples.iter().map(|s| s.1).collect())}),
    )
}

async fn takeover(cluster: &Cluster, streams: u64, records: u64) -> Result<Value> {
    {
        let old = cluster.handle(WRITER).await?;
        prepare(&old, 1..=streams).await?;
        stream::iter(1..=streams)
            .map(|id| {
                let old = &old;
                async move {
                    let mut at = 1;
                    while at <= records {
                        let count = (records - at + 1).min(32);
                        old.batch(StreamId(id.into()), CURRENT, at, count, false)
                            .await?;
                        at += count;
                    }
                    Ok::<_, BenchError>(())
                }
            })
            .buffer_unordered(PARALLEL)
            .try_collect::<Vec<_>>()
            .await?;
        // The old writer and its connections are gone from here on.
    }
    tokio::time::sleep(Duration::from_millis(500)).await;
    let start = Instant::now();
    let successor = cluster.handle(SUCCESSOR).await?;
    let connected = start.elapsed();
    let samples: Vec<[Duration; 4]> = stream::iter(1..=streams)
        .map(|id| {
            let successor = &successor;
            async move {
                let stream = StreamId(id.into());
                let journal = successor.journal();
                let began = Instant::now();
                let head = retry(|| journal.seal(stream, NEXT)).await?;
                assert_eq!(head, Lsn(records));
                let sealed = began.elapsed();
                let mut from = 1;
                while from <= head.0 {
                    let page =
                        retry(|| journal.read(stream, Lsn(from), 1024, Duration::ZERO)).await?;
                    from += page.records.len() as u64;
                }
                let caught_up = began.elapsed();
                successor.batch(stream, NEXT, head.0 + 1, 1, false).await?;
                let appended = began.elapsed();
                Ok::<_, BenchError>([sealed, caught_up, appended, start.elapsed()])
            }
        })
        .buffer_unordered(streams as usize)
        .try_collect()
        .await?;
    Ok(
        json!({"case": "takeover", "streams": streams, "records_per_stream": records,
        "new_writer_construct_ms": ms(connected),
        "seal": stats(samples.iter().map(|s| s[0]).collect()),
        "seal_and_catch_up": stats(samples.iter().map(|s| s[1]).collect()),
        "seal_catch_up_first_append": stats(samples.iter().map(|s| s[2]).collect()),
        "from_takeover_start": stats(samples.iter().map(|s| s[3]).collect()),
        "seconds": start.elapsed().as_secs_f64()}),
    )
}

async fn repair(cluster: &mut Cluster, streams: u64, tuning: &Tuning) -> Result<Value> {
    let handle = cluster.handle(WRITER).await?;
    prepare(&handle, 1..=streams).await?;
    seed(&handle, 1..=streams).await?;
    let mut setup = serde_json::Map::new();
    match cluster.backend {
        Backend::Writer => {
            drop(handle);
            // The learner is an idle keeper started before the loss, as the
            // consensus spare runs from the start.
            cluster.start_node(3).await?;
            cluster.wait_ready(3).await?;
            let transport = TcpTransport::new(
                &cluster.credentials[SUCCESSOR],
                cluster
                    .nodes
                    .iter()
                    .map(|node| (node.id(), node.app.to_string())),
                Duration::from_secs(2),
            )?;
            let ids: [KeeperId; 4] = std::array::from_fn(|i| cluster.nodes[i].id());
            let ensemble = [ids[0], ids[1], ids[2]];
            let start = Instant::now();
            let killed = cluster.kill(0).await?;
            let completion: Vec<Duration> = stream::iter(1..=streams)
                .map(|id| {
                    let transport = &transport;
                    async move {
                        let plan = Sweep::new(
                            StreamId(id.into()),
                            ensemble,
                            [ensemble[1], ensemble[2]],
                            ids[3],
                            NEXT,
                        );
                        loop {
                            match sweep_idle(transport, [plan]).await.pop().unwrap().1 {
                                Err(SweepError::Transport { .. })
                                    if start.elapsed() < RETRY_LIMIT * 10 =>
                                {
                                    tokio::time::sleep(Duration::from_millis(2)).await;
                                }
                                result => {
                                    result.map_err(|error| format!("stream {id}: {error}"))?;
                                    return Ok::<_, BenchError>(start.elapsed());
                                }
                            }
                        }
                    }
                })
                .buffer_unordered(PARALLEL)
                .try_collect()
                .await?;
            Ok(
                json!({"case": "repair", "streams": streams, "agent_kill": killed,
                "detection_wait_s": 0, "sweep_parallelism": PARALLEL,
                "completion": stats(completion.clone()),
                "seconds": completion.iter().max().unwrap().as_secs_f64()}),
            )
        }
        Backend::Consensus => {
            let Handle::Consensus(journal) = handle else {
                unreachable!()
            };
            let [a, b, c, spare] = [0, 1, 2, 3].map(|i| cluster.nodes[i].uuid);
            // Wait until the idle streams park: only the catalog stays open.
            let parking = Instant::now();
            let deadline = parking + Duration::from_secs(tuning.park_after_secs + 240);
            loop {
                let open = journal
                    .keeper_status(b, StreamId(0))
                    .await
                    .map(|s| s.streams);
                if matches!(open, Ok(n) if n <= 1) {
                    break;
                }
                if Instant::now() > deadline {
                    return Err(format!("streams did not park: {open:?}").into());
                }
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
            setup.insert(
                "parked_after_s".into(),
                parking.elapsed().as_secs_f64().into(),
            );
            let start = Instant::now();
            let killed = cluster.kill(0).await?;
            let mut pending = (1..=streams).collect::<Vec<_>>();
            let mut completion = Vec::new();
            // Streams still unrepaired after the limit are reported, not fatal.
            let limit = Duration::from_secs(tuning.repair_limit_secs);
            while !pending.is_empty() && start.elapsed() < limit {
                let done: Vec<u64> = stream::iter(pending.clone())
                    .map(|id| {
                        let journal = &journal;
                        async move {
                            let stream = StreamId(id.into());
                            let holds = matches!(
                                journal.keeper_status(spare, stream).await,
                                Ok(status) if status.replica == Some(true)
                            );
                            if !holds {
                                return None;
                            }
                            match journal.client().configuration(stream).await {
                                Ok(configuration)
                                    if configuration.voters.contains(&spare)
                                        && configuration.voters.contains(&b)
                                        && configuration.voters.contains(&c)
                                        && !configuration.voters.contains(&a) =>
                                {
                                    Some(id)
                                }
                                _ => None,
                            }
                        }
                    })
                    .buffer_unordered(PARALLEL)
                    .filter_map(|done| async move { done })
                    .collect()
                    .await;
                let now = start.elapsed();
                completion.extend(done.iter().map(|_| now));
                pending.retain(|id| !done.contains(id));
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
            let wait = Duration::from_secs(tuning.repair_after_secs);
            Ok(
                json!({"case": "repair", "streams": streams, "agent_kill": killed,
                "setup": setup, "repair_after_secs": tuning.repair_after_secs,
                "park_after_secs": tuning.park_after_secs, "detection_wait_s": tuning.repair_after_secs,
                "poll_interval_s": 1, "limit_s": limit.as_secs(),
                "repaired": completion.len(), "not_repaired": pending,
                "completion": stats(completion.clone()),
                "completion_minus_repair_after": stats(completion.iter().map(|d| d.saturating_sub(wait)).collect()),
                "seconds": completion.iter().max().map(Duration::as_secs_f64)}),
            )
        }
    }
}
