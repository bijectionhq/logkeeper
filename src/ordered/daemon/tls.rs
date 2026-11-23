use crate::ordered::{
    Fingerprint,
    replication::{self, transport::Connector},
};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::io;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio::io::AsyncWriteExt;
use tokio::net::TcpStream;
use tokio_rustls::{
    TlsAcceptor, TlsConnector,
    client::TlsStream,
    rustls::{
        ClientConfig, RootCertStore, ServerConfig,
        crypto::ring,
        pki_types::{CertificateDer, PrivateKeyDer, ServerName, pem::PemObject},
        server::WebPkiClientVerifier,
        version::TLS13,
    },
};
use uuid::Uuid;

pub(super) const VOTER: &[u8] = b"logkeeper-voter/1";
pub(super) const APPLICATION: &[u8] = b"logkeeper-application/1";

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Credentials {
    pub certificate: PathBuf,
    pub key: PathBuf,
    pub roots: PathBuf,
}

#[derive(Clone, serde::Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
pub struct Endpoint {
    pub address: SocketAddr,
    pub server_name: String,
    pub certificate: Fingerprint,
}

#[derive(Clone)]
pub(super) struct TlsPeers {
    pub connector: TlsConnector,
    pub group: Fingerprint,
    pub members: Arc<BTreeMap<Uuid, Endpoint>>,
}

impl Connector for TlsPeers {
    type Stream = TlsStream<TcpStream>;

    async fn connect(
        &self,
        group: Fingerprint,
        voter: Uuid,
    ) -> Result<Self::Stream, replication::Error> {
        if group != self.group {
            return Err(replication::Error::Group);
        }
        let endpoint = self.members.get(&voter).ok_or(replication::Error::Group)?;
        Ok(open(&self.connector, endpoint, VOTER, group).await?)
    }
}

impl Credentials {
    pub(super) fn client(&self, protocol: &[u8]) -> io::Result<TlsConnector> {
        let provider = Arc::new(ring::default_provider());
        let mut config = ClientConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&TLS13])
            .map_err(invalid)?
            .with_root_certificates(self.root_store()?)
            .with_client_auth_cert(certificates(&self.certificate)?, self.private_key()?)
            .map_err(invalid)?;
        config.alpn_protocols = vec![protocol.to_vec()];
        // Each connection supplies the exact certificate pin for its route.
        config.resumption = tokio_rustls::rustls::client::Resumption::disabled();
        Ok(TlsConnector::from(Arc::new(config)))
    }

    pub(super) fn server(&self) -> io::Result<TlsAcceptor> {
        let provider = Arc::new(ring::default_provider());
        let verifier = WebPkiClientVerifier::builder_with_provider(
            Arc::new(self.root_store()?),
            Arc::clone(&provider),
        )
        .build()
        .map_err(invalid)?;
        let mut config = ServerConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&TLS13])
            .map_err(invalid)?
            .with_client_cert_verifier(verifier)
            .with_single_cert(certificates(&self.certificate)?, self.private_key()?)
            .map_err(invalid)?;
        config.alpn_protocols = vec![VOTER.to_vec(), APPLICATION.to_vec()];
        config.send_tls13_tickets = 0;
        Ok(TlsAcceptor::from(Arc::new(config)))
    }

    pub(super) fn certificate_pin(&self) -> io::Result<Fingerprint> {
        let certificates = certificates(&self.certificate)?;
        pin(Some(&certificates))
    }

    fn private_key(&self) -> io::Result<PrivateKeyDer<'static>> {
        PrivateKeyDer::from_pem_file(&self.key).map_err(invalid)
    }

    fn root_store(&self) -> io::Result<RootCertStore> {
        let mut roots = RootCertStore::empty();
        for certificate in certificates(&self.roots)? {
            roots.add(certificate).map_err(invalid)?;
        }
        Ok(roots)
    }
}

pub(super) async fn open(
    connector: &TlsConnector,
    endpoint: &Endpoint,
    protocol: &[u8],
    group: Fingerprint,
) -> io::Result<TlsStream<TcpStream>> {
    let name = ServerName::try_from(endpoint.server_name.clone()).map_err(invalid)?;
    let socket = TcpStream::connect(endpoint.address).await?;
    socket.set_nodelay(true)?;
    let mut channel = connector.connect(name, socket).await?;
    let (_, peer) = channel.get_ref();
    if peer.alpn_protocol() != Some(protocol)
        || pin(peer.peer_certificates())? != endpoint.certificate
    {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "wrong journal peer",
        ));
    }
    channel.write_all(&group).await?;
    Ok(channel)
}

pub(super) fn pin(chain: Option<&[CertificateDer<'_>]>) -> io::Result<Fingerprint> {
    let leaf = chain.and_then(|chain| chain.first()).ok_or_else(|| {
        io::Error::new(io::ErrorKind::PermissionDenied, "missing peer certificate")
    })?;
    Ok(Sha256::digest(leaf.as_ref()).into())
}

fn certificates(path: &Path) -> io::Result<Vec<CertificateDer<'static>>> {
    let chain = CertificateDer::pem_file_iter(path)
        .map_err(invalid)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(invalid)?;
    if chain.is_empty() {
        return Err(invalid("empty certificate chain"));
    }
    Ok(chain)
}

pub(super) fn invalid(error: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error.to_string())
}
