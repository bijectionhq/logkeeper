use std::{io, sync::Arc};

use parking_lot::RwLock;
use tokio_rustls::{TlsAcceptor, TlsConnector};

use super::{Config, Lane};
use crate::stream::transport::KeeperTls;

#[derive(Clone)]
pub(in crate::stream::consensus) struct Tls(Arc<RwLock<Bundle>>);

struct Bundle {
    application: TlsAcceptor,
    control: TlsAcceptor,
    bulk: TlsAcceptor,
    admin: TlsAcceptor,
    peer_application: TlsConnector,
    peer_control: TlsConnector,
    peer_bulk: TlsConnector,
    peer_replication: TlsConnector,
}

impl Bundle {
    fn new(material: KeeperTls) -> Self {
        let server = |protocols: &[&[u8]]| {
            let mut config = material.server.clone();
            config.alpn_protocols = protocols.iter().map(|protocol| protocol.to_vec()).collect();
            TlsAcceptor::from(Arc::new(config))
        };
        let client = |lane: Lane| {
            let mut config = material.client.clone();
            config.alpn_protocols = lane
                .alpns()
                .iter()
                .map(|protocol| protocol.to_vec())
                .collect();
            TlsConnector::from(Arc::new(config))
        };
        Self {
            application: server(Lane::Application.alpns()),
            control: server(Lane::Control.alpns()),
            bulk: server(&[Lane::Bulk.alpns(), Lane::Replication.alpns()].concat()),
            admin: server(&[b"http/1.1"]),
            peer_application: client(Lane::Application),
            peer_control: client(Lane::Control),
            peer_bulk: client(Lane::Bulk),
            peer_replication: client(Lane::Replication),
        }
    }
}

impl Tls {
    pub(super) fn new(material: KeeperTls) -> Self {
        Self(Arc::new(RwLock::new(Bundle::new(material))))
    }

    pub(super) fn server(&self, lane: Lane) -> TlsAcceptor {
        let bundle = self.0.read();
        match lane {
            Lane::Application => bundle.application.clone(),
            Lane::Control => bundle.control.clone(),
            Lane::Bulk | Lane::Replication => bundle.bulk.clone(),
        }
    }

    pub(super) fn admin(&self) -> TlsAcceptor {
        self.0.read().admin.clone()
    }

    pub(in crate::stream::consensus) fn client(&self, lane: Lane) -> TlsConnector {
        let bundle = self.0.read();
        match lane {
            Lane::Application => bundle.peer_application.clone(),
            Lane::Control => bundle.peer_control.clone(),
            Lane::Bulk => bundle.peer_bulk.clone(),
            Lane::Replication => bundle.peer_replication.clone(),
        }
    }

    #[cfg(unix)]
    pub(super) fn reload(&self, config: &Config) -> io::Result<()> {
        let material = config
            .tls
            .keeper_tls(super::KeeperId(config.keeper.as_u128()))?;
        config.enrollment_with_certificate_digest(material.certificate_digest)?;
        if let Some(timed) = &config.timed_original {
            timed.check_tls_key(&material.public_key)?;
        }
        *self.0.write() = Bundle::new(material);
        Ok(())
    }

    #[cfg(unix)]
    pub(super) fn listen_for_reload(
        &self,
        config: Config,
        stop: tokio_util::sync::CancellationToken,
    ) -> io::Result<tokio::task::JoinHandle<()>> {
        use tokio::signal::unix::{SignalKind, signal};

        let mut hangup = signal(SignalKind::hangup())?;
        let tls = self.clone();
        let config = Arc::new(config);
        let keeper = config.keeper;
        Ok(tokio::spawn(async move {
            loop {
                tokio::select! {
                    () = stop.cancelled() => return,
                    signal = hangup.recv() => if signal.is_none() { return; }
                }
                let (tls, config) = (tls.clone(), config.clone());
                match tokio::task::spawn_blocking(move || tls.reload(&config)).await {
                    Ok(Ok(())) => tracing::info!(%keeper, "reloaded TLS credentials"),
                    Ok(Err(error)) => tracing::warn!(%keeper, %error, "TLS reload refused"),
                    Err(error) => tracing::error!(%keeper, %error, "TLS reload task failed"),
                }
            }
        }))
    }
}
