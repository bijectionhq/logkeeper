//! Mutually authenticated keeper TCP connections.
use std::{
    collections::{BTreeMap, HashSet},
    io,
    net::SocketAddr,
    path::{Path, PathBuf},
    sync::Arc,
    time::{Duration, Instant},
};

use journal_contract::BoxFuture;
use parking_lot::Mutex;
use tokio::{
    net::{TcpListener, TcpStream},
    sync::Semaphore,
    task::JoinSet,
    time::{Instant as TokioInstant, sleep, timeout},
};
use tokio_rustls::{
    TlsAcceptor, TlsConnector,
    client::TlsStream,
    rustls::{
        self, CertificateError, ClientConfig, DigitallySignedStruct, RootCertStore, ServerConfig,
        SignatureScheme,
        client::{
            danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier},
            verify_server_cert_signed_by_trust_anchor,
        },
        crypto::{WebPkiSupportedAlgorithms, ring, verify_tls12_signature, verify_tls13_signature},
        pki_types::{CertificateDer, PrivateKeyDer, ServerName, UnixTime, pem::PemObject},
        server::{ParsedCertificate, WebPkiClientVerifier},
        version::TLS13,
    },
};
use tokio_util::sync::CancellationToken;
use x509_parser::{extensions::GeneralName, parse_x509_certificate};

use super::{
    codec::{
        decode_reply, decode_request, encode_reply, encode_request, invalid, read_frame,
        write_frame,
    },
    keeper::{Keeper, Limits, SealPolicy},
    wire::*,
};

const ALPN: &[u8] = b"logkeeper-stream/2";
const KEEPER_URI: &str = "urn:logkeeper:keeper:";
const CLIENT_URI: &str = "urn:logkeeper:client:";
const CONNECTIONS: usize = 256;
const ROUTE_CONNECTIONS: usize = 64;
const WAITING_READS: usize = 16;
const IDLE_CHANNELS: usize = 16;
const IDLE_GRACE: Duration = Duration::from_millis(250);
const FRAME_TIMEOUT: Duration = Duration::from_secs(60);

#[derive(Clone, Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Credentials {
    pub certificate: PathBuf,
    pub private_key: PathBuf,
    pub ca: PathBuf,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub keeper: uuid::Uuid,
    pub listen: SocketAddr,
    pub data: PathBuf,
    pub zone: String,
    pub tls: Credentials,
    pub clients: Vec<String>,
    pub writers: Vec<String>,
    pub limits: Limits,
}

impl Config {
    pub fn read(path: &Path) -> io::Result<Self> {
        Ok(serde_json::from_slice(&std::fs::read(path)?)?)
    }

    pub async fn serve(self, listener: TcpListener, stop: CancellationToken) -> io::Result<()> {
        self.run(listener, stop, None).await
    }

    pub async fn serve_with_policy(
        self,
        listener: TcpListener,
        stop: CancellationToken,
        policy: Arc<dyn SealPolicy>,
    ) -> io::Result<()> {
        self.run(listener, stop, Some(policy)).await
    }

    async fn run(
        self,
        listener: TcpListener,
        stop: CancellationToken,
        policy: Option<Arc<dyn SealPolicy>>,
    ) -> io::Result<()> {
        let id = KeeperId(self.keeper.as_u128());
        let acceptor = self.tls.server(id)?;
        if self.zone.is_empty()
            || self
                .clients
                .iter()
                .chain(&self.writers)
                .any(|uri| !valid_client_uri(uri))
        {
            return Err(invalid("invalid keeper zone or authorized client URI"));
        }
        let clients: Arc<HashSet<String>> = Arc::new(self.clients.into_iter().collect());
        let writers: Arc<HashSet<String>> = Arc::new(self.writers.into_iter().collect());
        let keeper = tokio::task::spawn_blocking(move || match policy {
            Some(policy) => Keeper::open_with_policy(&self.data, id, self.limits, policy),
            None => Keeper::open(&self.data, id, self.limits),
        })
        .await??;
        let mut tasks = JoinSet::new();
        loop {
            tokio::select! {
                _ = stop.cancelled() => break,
                result = tasks.join_next(), if !tasks.is_empty() => {
                    if let Some(Err(error)) = result { return Err(error.into()); }
                }
                connection = listener.accept(), if tasks.len() < CONNECTIONS => {
                    let (socket, _) = connection?;
                    let acceptor = acceptor.clone();
                    let keeper = keeper.clone();
                    let clients = Arc::clone(&clients);
                    let writers = Arc::clone(&writers);
                    tasks.spawn(async move {
                        let _ = serve_connection(socket, acceptor, clients, writers, keeper).await;
                    });
                }
            }
        }
        tasks.shutdown().await;
        Ok(())
    }
}

async fn serve_connection(
    socket: TcpStream,
    acceptor: TlsAcceptor,
    clients: Arc<HashSet<String>>,
    writers: Arc<HashSet<String>>,
    keeper: Keeper,
) -> io::Result<()> {
    socket.set_nodelay(true)?;
    let mut channel = timeout(FRAME_TIMEOUT, acceptor.accept(socket)).await??;
    let (_, peer) = channel.get_ref();
    let leaf = leaf(peer.peer_certificates())?;
    let identity = client_identity(leaf)?;
    let can_read = clients.contains(identity.as_str());
    let can_write = writers.contains(identity.as_str());
    if peer.alpn_protocol() != Some(ALPN) || (!can_read && !can_write) {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "unauthorized keeper client",
        ));
    }
    loop {
        let frame = timeout(FRAME_TIMEOUT, read_frame(&mut channel)).await??;
        let request = decode_request(frame)?;
        let allowed = match request {
            Request::Read { .. } | Request::Check { .. } => can_read,
            _ => can_write,
        };
        let reply = if allowed {
            keeper
                .call(&identity, request)
                .await
                .map_err(|error| io::Error::other(format!("{error:?}")))?
        } else {
            Reply::Refused(Refusal::Unauthorized)
        };
        timeout(
            FRAME_TIMEOUT,
            write_frame(&mut channel, &encode_reply(&reply)?),
        )
        .await??;
    }
}

type Channel = TlsStream<TcpStream>;

struct Route {
    address: String,
    idle: Arc<Mutex<Idle>>,
    connections: Semaphore,
    waiting_reads: Semaphore,
}

struct Idle {
    channels: Vec<(TokioInstant, Channel)>,
    pruning: bool,
}

impl Route {
    fn new(address: String, idle: Vec<Channel>) -> Self {
        Self {
            address,
            idle: Arc::new(Mutex::new(Idle {
                channels: idle
                    .into_iter()
                    .map(|channel| (TokioInstant::now(), channel))
                    .collect(),
                pruning: false,
            })),
            connections: Semaphore::new(ROUTE_CONNECTIONS),
            waiting_reads: Semaphore::new(WAITING_READS),
        }
    }

    fn recycle(&self, channel: Channel) {
        let mut idle = self.idle.lock();
        idle.channels.push((TokioInstant::now(), channel));
        if idle.channels.len() <= IDLE_CHANNELS || idle.pruning {
            return;
        }
        idle.pruning = true;
        let idle = Arc::downgrade(&self.idle);
        tokio::spawn(async move {
            loop {
                sleep(IDLE_GRACE).await;
                let Some(idle) = idle.upgrade() else { return };
                let mut idle = idle.lock();
                let excess = idle.channels.len().saturating_sub(IDLE_CHANNELS);
                let expired = idle
                    .channels
                    .partition_point(|(used, _)| used.elapsed() >= IDLE_GRACE);
                idle.channels.drain(..excess.min(expired));
                if idle.channels.len() <= IDLE_CHANNELS {
                    idle.pruning = false;
                    return;
                }
            }
        });
    }
}

pub struct TcpTransport {
    identity: Identity,
    read_order: Vec<KeeperId>,
    tls: TlsConnector,
    routes: BTreeMap<KeeperId, Route>,
    deadline: Duration,
}

impl TcpTransport {
    /// Use a placement whose keeper identities are already known.
    pub fn new(
        credentials: &Credentials,
        routes: impl IntoIterator<Item = (KeeperId, String)>,
        deadline: Duration,
    ) -> io::Result<Self> {
        let (tls, identity) = credentials.client()?;
        let mut transport = Self {
            identity,
            read_order: Vec::new(),
            tls,
            routes: BTreeMap::new(),
            deadline,
        };
        for (id, address) in routes {
            if id.0 == 0
                || transport
                    .routes
                    .insert(id, Route::new(address, Vec::new()))
                    .is_some()
            {
                return Err(invalid("invalid or duplicate keeper route"));
            }
            transport.read_order.push(id);
        }
        Ok(transport)
    }

    /// Resolve the initial ensemble in URL order from the keepers' authenticated URI SANs.
    pub async fn discover(
        url: &str,
        credentials: &Credentials,
        deadline: Duration,
    ) -> io::Result<(Self, [KeeperId; 3])> {
        let addresses: [&str; 3] = url
            .strip_prefix("logkeeper+tls://")
            .ok_or_else(|| invalid("invalid journal URL scheme"))?
            .split(',')
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|_| invalid("expected three keeper addresses"))?;
        if addresses
            .iter()
            .any(|address| address.is_empty() || address.contains(['/', '?', '#', '@']))
        {
            return Err(invalid("invalid journal URL keeper address"));
        }
        let mut transport = Self::new(credentials, [], deadline)?;
        let connections = timeout(
            deadline,
            futures::future::try_join_all(addresses.iter().map(|address| {
                let tls = &transport.tls;
                async move {
                    let start = Instant::now();
                    let (id, channel) = connect(tls, address).await?;
                    Ok::<_, io::Error>((start.elapsed(), id, channel))
                }
            })),
        )
        .await??;
        let mut ensemble = [KeeperId(0); 3];
        let mut proximity = Vec::with_capacity(ensemble.len());
        for (index, (address, (elapsed, id, channel))) in
            addresses.into_iter().zip(connections).enumerate()
        {
            let route = Route::new(address.into(), vec![channel]);
            if transport.routes.insert(id, route).is_some() {
                return Err(invalid("duplicate keeper identity"));
            }
            proximity.push((elapsed, id));
            ensemble[index] = id;
        }
        proximity.sort_by_key(|(elapsed, _)| *elapsed);
        transport
            .read_order
            .extend(proximity.into_iter().map(|(_, id)| id));
        Ok((transport, ensemble))
    }

    async fn exchange(&self, keeper: KeeperId, request: Request) -> Result<Reply, TransportError> {
        let route = self
            .routes
            .get(&keeper)
            .ok_or(TransportError::Unreachable)?;
        // Leave capacity for mutations and checks while reads wait at the keeper.
        let _read = match request {
            Request::Read { wait_ms: 1.., .. } => {
                Some(route.waiting_reads.acquire().await.expect("open route"))
            }
            _ => None,
        };
        let _connection = route.connections.acquire().await.expect("open route");
        let body = encode_request(&request).map_err(protocol)?;
        let idle = route.idle.lock().channels.pop().map(|(_, channel)| channel);
        let mut channel = match idle {
            Some(channel) => channel,
            None => {
                let (peer, channel) = connect(&self.tls, &route.address)
                    .await
                    .map_err(connection_error)?;
                if peer != keeper {
                    return Err(TransportError::Protocol(
                        "keeper URI does not match route".into(),
                    ));
                }
                channel
            }
        };
        write_frame(&mut channel, &body)
            .await
            .map_err(connection_error)?;
        let reply = decode_reply(read_frame(&mut channel).await.map_err(connection_error)?)
            .map_err(protocol)?;
        route.recycle(channel);
        Ok(reply)
    }
}

impl Transport for TcpTransport {
    fn identity(&self) -> &Identity {
        &self.identity
    }

    fn read_order(&self, mut ensemble: [KeeperId; 3]) -> [KeeperId; 3] {
        ensemble.sort_by_key(|keeper| {
            self.read_order
                .iter()
                .position(|id| id == keeper)
                .unwrap_or(usize::MAX)
        });
        ensemble
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, Result<Reply, TransportError>> {
        let wait = match request {
            Request::Read { wait_ms, .. } => Duration::from_millis(u64::from(wait_ms)),
            _ => Duration::ZERO,
        };
        Box::pin(async move {
            timeout(
                self.deadline.saturating_add(wait),
                self.exchange(keeper, request),
            )
            .await
            .map_err(|_| TransportError::TimedOut)?
        })
    }
}

async fn connect(tls: &TlsConnector, address: &str) -> io::Result<(KeeperId, Channel)> {
    let socket = TcpStream::connect(address).await?;
    socket.set_nodelay(true)?;
    // The server verifier validates a keeper URI identity. SNI and DNS names are unused.
    let name = ServerName::try_from("logkeeper").expect("valid placeholder name");
    let channel = tls.connect(name, socket).await?;
    let (_, peer) = channel.get_ref();
    if peer.alpn_protocol() != Some(ALPN) {
        return Err(invalid("invalid keeper ALPN"));
    }
    let id = keeper_id(leaf(peer.peer_certificates())?)?;
    Ok((id, channel))
}

impl Credentials {
    fn server(&self, keeper: KeeperId) -> io::Result<TlsAcceptor> {
        let provider = Arc::new(ring::default_provider());
        let verifier = WebPkiClientVerifier::builder_with_provider(
            Arc::new(self.root_store()?),
            Arc::clone(&provider),
        )
        .build()
        .map_err(display_error)?;
        let chain = certificates(&self.certificate)?;
        if keeper_id(leaf(Some(&chain))?)? != keeper {
            return Err(invalid("configured keeper does not match certificate URI"));
        }
        let mut config = ServerConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&TLS13])
            .map_err(display_error)?
            .with_client_cert_verifier(verifier)
            .with_single_cert(chain, self.key()?)
            .map_err(display_error)?;
        config.alpn_protocols = vec![ALPN.to_vec()];
        config.send_tls13_tickets = 0;
        Ok(TlsAcceptor::from(Arc::new(config)))
    }

    fn client(&self) -> io::Result<(TlsConnector, Identity)> {
        let provider = Arc::new(ring::default_provider());
        let verifier = Arc::new(KeeperVerifier {
            roots: self.root_store()?,
            algorithms: provider.signature_verification_algorithms,
        });
        let chain = certificates(&self.certificate)?;
        let identity = client_identity(leaf(Some(&chain))?)?;
        let mut config = ClientConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&TLS13])
            .map_err(display_error)?
            .dangerous()
            .with_custom_certificate_verifier(verifier)
            .with_client_auth_cert(chain, self.key()?)
            .map_err(display_error)?;
        config.alpn_protocols = vec![ALPN.to_vec()];
        config.enable_sni = false;
        config.resumption = rustls::client::Resumption::disabled();
        Ok((TlsConnector::from(Arc::new(config)), identity))
    }

    fn key(&self) -> io::Result<PrivateKeyDer<'static>> {
        PrivateKeyDer::from_pem_file(&self.private_key).map_err(display_error)
    }

    fn root_store(&self) -> io::Result<RootCertStore> {
        let mut roots = RootCertStore::empty();
        for certificate in certificates(&self.ca)? {
            roots.add(certificate).map_err(display_error)?;
        }
        Ok(roots)
    }
}

#[derive(Debug)]
struct KeeperVerifier {
    roots: RootCertStore,
    algorithms: WebPkiSupportedAlgorithms,
}

impl ServerCertVerifier for KeeperVerifier {
    fn verify_server_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp: &[u8],
        now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        let certificate = ParsedCertificate::try_from(end_entity)?;
        verify_server_cert_signed_by_trust_anchor(
            &certificate,
            &self.roots,
            intermediates,
            now,
            self.algorithms.all,
        )?;
        keeper_id(end_entity).map_err(|_| CertificateError::NotValidForName)?;
        Ok(ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        signature: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        verify_tls12_signature(message, cert, signature, &self.algorithms)
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        signature: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        verify_tls13_signature(message, cert, signature, &self.algorithms)
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.algorithms.supported_schemes()
    }
}

fn certificates(path: &Path) -> io::Result<Vec<CertificateDer<'static>>> {
    CertificateDer::pem_file_iter(path)
        .map_err(display_error)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(display_error)
}

fn leaf<'cert, 'der>(
    chain: Option<&'cert [CertificateDer<'der>]>,
) -> io::Result<&'cert CertificateDer<'der>> {
    chain
        .and_then(|chain| chain.first())
        .ok_or_else(|| invalid("missing peer certificate"))
}

fn valid_client_uri(uri: &str) -> bool {
    uri.strip_prefix(CLIENT_URI)
        .is_some_and(|name| !name.is_empty() && uri.len() <= 4096)
}

fn certificate_uri(certificate: &CertificateDer<'_>, prefix: &str) -> io::Result<String> {
    let (remaining, certificate) =
        parse_x509_certificate(certificate.as_ref()).map_err(display_error)?;
    if !remaining.is_empty() {
        return Err(invalid("trailing certificate bytes"));
    }
    let san = certificate
        .subject_alternative_name()
        .map_err(display_error)?
        .ok_or_else(|| invalid("missing certificate URI SAN"))?;
    let mut names = san.value.general_names.iter().filter_map(|san| match san {
        GeneralName::URI(uri) if uri.starts_with(prefix) => Some(*uri),
        _ => None,
    });
    let uri = names
        .next()
        .ok_or_else(|| invalid("missing Logkeeper certificate URI"))?;
    if names.next().is_some() || uri.len() <= prefix.len() {
        return Err(invalid("ambiguous or empty Logkeeper certificate URI"));
    }
    Ok(uri.to_owned())
}

fn client_identity(certificate: &CertificateDer<'_>) -> io::Result<Identity> {
    let uri = certificate_uri(certificate, CLIENT_URI)?;
    if !valid_client_uri(&uri) {
        return Err(invalid("invalid client URI"));
    }
    Ok(Identity::from(uri))
}

fn keeper_id(certificate: &CertificateDer<'_>) -> io::Result<KeeperId> {
    let uri = certificate_uri(certificate, KEEPER_URI)?;
    let id = uuid::Uuid::parse_str(&uri[KEEPER_URI.len()..]).map_err(display_error)?;
    if id.is_nil() || id.to_string() != uri[KEEPER_URI.len()..] {
        return Err(invalid("keeper URI requires a nonzero canonical UUID"));
    }
    Ok(KeeperId(id.as_u128()))
}

fn display_error(error: impl std::fmt::Display) -> io::Error {
    invalid(&error.to_string())
}
fn protocol(error: io::Error) -> TransportError {
    TransportError::Protocol(error.to_string())
}
fn connection_error(error: io::Error) -> TransportError {
    match error.kind() {
        io::ErrorKind::InvalidData | io::ErrorKind::PermissionDenied => protocol(error),
        io::ErrorKind::TimedOut => TransportError::TimedOut,
        _ => TransportError::Unreachable,
    }
}

#[cfg(test)]
mod tests;
