use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    error::Error,
    fs, io,
    net::SocketAddr,
    path::Path,
    process::{Child, Command, Stdio},
    sync::{Arc, mpsc},
    time::{Duration, Instant},
};

use logkeeper::stream::{
    transport::{Credentials, TcpTransport},
    wire::KeeperId,
};
use rcgen::{CertificateParams, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair, SanType};
use serde_json::json;
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::{mpsc as async_mpsc, oneshot},
    task::JoinHandle,
};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

pub type BenchError = Box<dyn Error + Send + Sync>;
pub type Result<T> = std::result::Result<T, BenchError>;
pub const ENSEMBLE: [KeeperId; 3] = [KeeperId(1), KeeperId(2), KeeperId(3)];
pub const LEARNER: KeeperId = KeeperId(4);
const WRITER: &str = "urn:logkeeper:client:writer";
const SUCCESSOR: &str = "urn:logkeeper:client:successor";
const OBSERVER: &str = "urn:logkeeper:client:observer";

pub struct Cluster {
    pub keepers: Vec<Keeper>,
    // Drop the processes and links before deleting their files.
    pub links: Vec<Link>,
    pub writer: Credentials,
    pub successor: Credentials,
    pub observer: Credentials,
    root: tempfile::TempDir,
    issuer: Issuer<'static, KeyPair>,
    timer: Timer,
}

impl Cluster {
    pub async fn start(binary: &Path, rtt: [Duration; 3], cap: usize) -> Result<Self> {
        // Keep WALs on the worktree volume, including on machines with tmpfs /tmp.
        let root = tempfile::Builder::new()
            .prefix("cell-")
            .tempdir_in("verification/.results/measure")?;
        let mut params = CertificateParams::default();
        params.is_ca = IsCa::Ca(rcgen::BasicConstraints::Unconstrained);
        let key = KeyPair::generate()?;
        fs::write(root.path().join("ca.pem"), params.self_signed(&key)?.pem())?;
        let issuer = Issuer::new(params, key);
        let client = |uri| {
            credentials(
                root.path(),
                &issuer,
                uri,
                ExtendedKeyUsagePurpose::ClientAuth,
            )
        };
        let mut cluster = Self {
            keepers: Vec::new(),
            links: Vec::new(),
            writer: client(WRITER)?,
            successor: client(SUCCESSOR)?,
            observer: client(OBSERVER)?,
            root,
            issuer,
            timer: Timer::start()?,
        };
        for (keeper, rtt) in ENSEMBLE.into_iter().zip(rtt) {
            cluster.add(binary, keeper, rtt, cap).await?;
        }
        Ok(cluster)
    }

    pub async fn add(
        &mut self,
        binary: &Path,
        id: KeeperId,
        rtt: Duration,
        cap: usize,
    ) -> Result<()> {
        let keeper = Keeper::start(binary, self.root.path(), &self.issuer, id, cap).await?;
        self.links
            .push(Link::start(keeper.address, rtt, self.timer.clone()).await?);
        self.keepers.push(keeper);
        Ok(())
    }

    pub fn transport(&self, credentials: &Credentials) -> Result<TcpTransport> {
        Ok(TcpTransport::new(
            credentials,
            self.keepers
                .iter()
                .zip(&self.links)
                .map(|(k, p)| (k.id, p.address.to_string())),
            Duration::from_secs(2),
        )?)
    }
}

pub struct Keeper {
    id: KeeperId,
    address: SocketAddr,
    child: Child,
}

impl Keeper {
    async fn start(
        binary: &Path,
        dir: &Path,
        issuer: &Issuer<'_, KeyPair>,
        id: KeeperId,
        cap: usize,
    ) -> Result<Self> {
        let uuid = Uuid::from_u128(id.0);
        let tls = credentials(
            dir,
            issuer,
            &format!("urn:logkeeper:keeper:{uuid}"),
            ExtendedKeyUsagePurpose::ServerAuth,
        )?;
        let reserved = TcpListener::bind("127.0.0.1:0").await?;
        let address = reserved.local_addr()?;
        let config = dir.join(format!("keeper-{}.json", id.0));
        let data = dir.join(format!("wal-{}", id.0));
        fs::write(
            &config,
            serde_json::to_vec(&json!({
                "keeper": uuid, "listen": address, "data": data, "zone": format!("zone-{}", id.0),
                "tls": { "certificate": tls.certificate, "private_key": tls.private_key, "ca": tls.ca },
                "clients": [WRITER, SUCCESSOR, OBSERVER], "writers": [WRITER, SUCCESSOR],
                "limits": { "stream_quota_bytes": 8589934592_u64, "max_record_bytes": 33554432,
                            "round_bytes_per_stream": cap, "round_requests": 64 }
            }))?,
        )?;
        drop(reserved);
        let child = Command::new(binary)
            .args(["keeper", "--config"])
            .arg(config)
            .env("TOKIO_WORKER_THREADS", "2")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .spawn()?;
        let mut keeper = Self { id, address, child };
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            if let Some(status) = keeper.child.try_wait()? {
                return Err(format!("keeper {id:?} exited at startup with {status}").into());
            }
            if TcpStream::connect(address).await.is_ok() && data.join("KEEPER").exists() {
                return Ok(keeper);
            }
            if Instant::now() >= deadline {
                return Err(format!("keeper {id:?} did not start at {address}").into());
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    pub fn kill(&mut self) -> io::Result<()> {
        if self.child.try_wait()?.is_none() {
            self.child.kill()?;
            self.child.wait()?;
        }
        Ok(())
    }
}

impl Drop for Keeper {
    fn drop(&mut self) {
        let _ = self.kill();
    }
}

fn credentials(
    dir: &Path,
    issuer: &Issuer<'_, KeyPair>,
    uri: &str,
    purpose: ExtendedKeyUsagePurpose,
) -> Result<Credentials> {
    let name = uri.rsplit(':').next().unwrap();
    let key = KeyPair::generate()?;
    let mut params = CertificateParams::default();
    params.subject_alt_names = vec![SanType::URI(uri.try_into()?)];
    params.extended_key_usages = vec![purpose];
    let certificate = dir.join(format!("{name}.pem"));
    let private_key = dir.join(format!("{name}.key"));
    fs::write(&certificate, params.signed_by(&key, issuer)?.pem())?;
    fs::write(&private_key, key.serialize_pem())?;
    Ok(Credentials {
        certificate,
        private_key,
        ca: dir.join("ca.pem"),
    })
}

pub struct Link {
    pub address: SocketAddr,
    partition: CancellationToken,
    listener: JoinHandle<()>,
    accepted: Arc<std::sync::atomic::AtomicU64>,
}

impl Link {
    pub async fn start(target: SocketAddr, rtt: Duration, timer: Timer) -> io::Result<Self> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let partition = CancellationToken::new();
        let cut = partition.clone();
        let accepted = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let connections = accepted.clone();
        let listener = tokio::spawn(async move {
            let mut tasks = tokio::task::JoinSet::new();
            loop {
                tokio::select! {
                    Some(_) = tasks.join_next(), if !tasks.is_empty() => {},
                    result = listener.accept() => {
                        let Ok((client, _)) = result else { break };
                        connections.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        tasks.spawn(forward(client, target, cut.clone(), timer.clone(), rtt / 2));
                    }
                }
            }
        });
        Ok(Self {
            address,
            partition,
            listener,
            accepted,
        })
    }

    pub fn partition(&self) {
        self.partition.cancel();
    }

    pub fn connections(&self) -> u64 {
        self.accepted.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl Drop for Link {
    fn drop(&mut self) {
        self.listener.abort();
    }
}

async fn forward(
    mut client: TcpStream,
    target: SocketAddr,
    cut: CancellationToken,
    timer: Timer,
    delay: Duration,
) -> io::Result<()> {
    client.set_nodelay(true)?;
    tokio::select! {
        biased;
        _ = cut.cancelled() => {},
        result = async {
            let mut server = TcpStream::connect(target).await?;
            server.set_nodelay(true)?;
            let (cr, cw) = client.split();
            let (sr, sw) = server.split();
            tokio::try_join!(pipe(cr, sw, &timer, delay), pipe(sr, cw, &timer, delay))?;
            Ok::<_, io::Error>(())
        } => return result,
    }
    // After partition, stop forwarding even on established sessions. Leave the socket
    // open until the client times out or cancels, as it would on a packet blackhole.
    let mut discard = [0; 4096];
    while client.read(&mut discard).await? != 0 {}
    Ok(())
}

async fn pipe(
    mut read: impl AsyncRead + Unpin,
    mut write: impl AsyncWrite + Unpin,
    timer: &Timer,
    delay: Duration,
) -> io::Result<()> {
    if delay.is_zero() {
        tokio::io::copy(&mut read, &mut write).await?;
    } else {
        // A bounded per-direction queue delays bytes without adding an extra RTT for
        // every chunk of a large record. Reuse buffers for long-lived connections.
        let (send, mut ready) = async_mpsc::channel::<(Instant, Vec<u8>)>(32);
        let (recycle, mut buffers) = async_mpsc::channel(32);
        let receive = async {
            loop {
                let mut buf = buffers
                    .try_recv()
                    .unwrap_or_else(|_| Vec::with_capacity(65536));
                buf.clear();
                if read.read_buf(&mut buf).await? == 0 {
                    break;
                }
                if send.send((Instant::now() + delay, buf)).await.is_err() {
                    break;
                }
            }
            drop(send);
            Ok::<_, io::Error>(())
        };
        let send = async {
            while let Some((due, buf)) = ready.recv().await {
                timer.until(due).await;
                write.write_all(&buf).await?;
                let _ = recycle.try_send(buf);
            }
            Ok::<_, io::Error>(())
        };
        tokio::try_join!(receive, send)?;
    }
    write.shutdown().await
}

// Tokio's millisecond timer wheel is too coarse for sub-ms one-way delays.
#[derive(Clone)]
pub struct Timer(mpsc::Sender<(Instant, oneshot::Sender<()>)>);

impl Timer {
    pub fn start() -> io::Result<Self> {
        let (send, receive) = mpsc::channel::<(Instant, oneshot::Sender<()>)>();
        std::thread::Builder::new()
            .name("proxy-clock".into())
            .spawn(move || {
                let mut heap = BinaryHeap::<Reverse<(Instant, u64)>>::new();
                let mut waits = std::collections::HashMap::<u64, oneshot::Sender<()>>::new();
                let mut serial = 0;
                loop {
                    while let Some(&Reverse((due, id))) = heap.peek() {
                        if due > Instant::now() {
                            break;
                        }
                        heap.pop();
                        let _ = waits.remove(&id).unwrap().send(());
                    }
                    let next = match heap.peek() {
                        Some(&Reverse((due, _))) => {
                            receive.recv_timeout(due.saturating_duration_since(Instant::now()))
                        }
                        None => receive
                            .recv()
                            .map_err(|_| mpsc::RecvTimeoutError::Disconnected),
                    };
                    match next {
                        Ok((due, wake)) => {
                            serial += 1;
                            waits.insert(serial, wake);
                            heap.push(Reverse((due, serial)));
                        }
                        Err(mpsc::RecvTimeoutError::Timeout) => {}
                        Err(mpsc::RecvTimeoutError::Disconnected) => break,
                    }
                }
            })?;
        Ok(Self(send))
    }

    async fn until(&self, due: Instant) {
        if due > Instant::now() {
            let (wake, wait) = oneshot::channel();
            if self.0.send((due, wake)).is_ok() {
                let _ = wait.await;
            }
        }
    }
}
