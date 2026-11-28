//! `logkeeper repair`: declare lost keepers and repair their streams over mTLS.

use std::{
    collections::BTreeMap,
    io,
    path::Path,
    sync::Arc,
    time::{Duration, Instant},
};

use tokio_util::sync::CancellationToken;

use super::{Member, Outcome, Report, Roster, repair_lost};
use crate::stream::{
    proposer::driver::RPC_TIMEOUT,
    transport::{Credentials, TcpTransport},
    wire::*,
};

pub const USAGE: &str = "Usage: logkeeper repair --config FILE [--lost UUID]";

/// Repairer configuration (JSON). The certificate's client URI must be listed in
/// every keeper's `writers` and `clients`.
#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub tls: Credentials,
    /// Every keeper of the cluster, including spares.
    pub keepers: Vec<KeeperEntry>,
    /// How long a keeper must stay unreachable before it is declared lost.
    #[serde(default = "default_repair_after")]
    pub repair_after_secs: u64,
    /// The interval between probes and repair passes.
    #[serde(default = "default_probe")]
    pub probe_secs: u64,
}

#[derive(Clone, Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct KeeperEntry {
    pub id: uuid::Uuid,
    pub address: String,
    pub zone: String,
}

fn default_repair_after() -> u64 {
    600
}

fn default_probe() -> u64 {
    10
}

impl Config {
    pub fn read(path: &Path) -> io::Result<Self> {
        let config: Self = serde_json::from_slice(&std::fs::read(path)?)?;
        if config.keepers.len() < 4
            || config.probe_secs == 0
            || config
                .keepers
                .iter()
                .any(|keeper| keeper.id.is_nil() || keeper.zone.is_empty())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "repair needs at least four keepers with nonzero IDs and zones",
            ));
        }
        Ok(config)
    }

    fn roster(&self) -> Roster {
        Roster::new(self.keepers.iter().map(|keeper| Member {
            id: KeeperId(keeper.id.as_u128()),
            zone: keeper.zone.clone(),
        }))
    }

    fn transport(&self) -> io::Result<TcpTransport> {
        TcpTransport::new(
            &self.tls,
            self.keepers
                .iter()
                .map(|keeper| (KeeperId(keeper.id.as_u128()), keeper.address.clone())),
            RPC_TIMEOUT,
        )
    }

    /// Repair the streams of an operator-declared lost keeper once.
    pub async fn repair_once(&self, lost: KeeperId) -> io::Result<Report> {
        let transport = self.transport()?;
        Ok(repair_lost(&transport, &self.roster(), lost, &[]).await)
    }

    /// Probe every keeper, declare a keeper lost after `repair_after_secs` without a
    /// reply, and repair its streams on every pass until none remain.
    pub async fn run(&self, stop: CancellationToken) -> io::Result<()> {
        let transport = Arc::new(self.transport()?);
        let roster = self.roster();
        let repair_after = Duration::from_secs(self.repair_after_secs);
        let probe = Duration::from_secs(self.probe_secs);
        let start = Instant::now();
        let mut seen: BTreeMap<KeeperId, Instant> = roster
            .members()
            .iter()
            .map(|member| (member.id, start))
            .collect();
        loop {
            for member in roster.members() {
                if reachable(&*transport, member.id).await {
                    seen.insert(member.id, Instant::now());
                }
            }
            let lost: Vec<_> = seen
                .iter()
                .filter(|(_, at)| at.elapsed() >= repair_after)
                .map(|(id, _)| *id)
                .collect();
            for &keeper in &lost {
                let report = repair_lost(&*transport, &roster, keeper, &lost).await;
                if report.listed > 0 {
                    log(keeper, &report);
                }
            }
            tokio::select! {
                _ = stop.cancelled() => return Ok(()),
                _ = tokio::time::sleep(probe) => {}
            }
        }
    }
}

/// A keeper answers a Check for an absent stream with a refusal, which proves it is up.
async fn reachable(transport: &TcpTransport, keeper: KeeperId) -> bool {
    let check = Request::Check {
        stream: StreamId(0),
        epoch: Epoch(0),
    };
    matches!(
        tokio::time::timeout(RPC_TIMEOUT, transport.call(keeper, check)).await,
        Ok(Ok(_))
    )
}

fn log(lost: KeeperId, report: &Report) {
    for (stream, outcome) in &report.outcomes {
        let stream = uuid::Uuid::from_u128(stream.0);
        let lost = uuid::Uuid::from_u128(lost.0);
        match outcome {
            Outcome::Repaired { learner, epoch } => println!(
                "repaired stream={stream} lost={lost} learner={} epoch={}",
                uuid::Uuid::from_u128(learner.0),
                epoch.0
            ),
            Outcome::AlreadyRepaired => {}
            Outcome::NoSpare => eprintln!("no spare stream={stream} lost={lost}"),
            Outcome::Failed(reason) => {
                eprintln!("repair failed stream={stream} lost={lost}: {reason}")
            }
        }
    }
    println!(
        "repair pass lost={} listed={} pending={}",
        uuid::Uuid::from_u128(lost.0),
        report.listed,
        report.pending()
    );
}

/// Run `logkeeper repair`. With `--lost`, repair that keeper once and fail if any
/// stream remains; otherwise run the probing loop until `stop`.
pub async fn command(args: &[String], stop: CancellationToken) -> io::Result<()> {
    let usage = || io::Error::new(io::ErrorKind::InvalidInput, USAGE);
    let (file, lost) = match args {
        [flag, file] if flag == "--config" => (file, None),
        [flag, file, lost_flag, lost] if flag == "--config" && lost_flag == "--lost" => {
            let lost = uuid::Uuid::parse_str(lost).map_err(|_| usage())?;
            (file, Some(KeeperId(lost.as_u128())))
        }
        _ => return Err(usage()),
    };
    let config = Config::read(Path::new(file))?;
    let Some(lost) = lost else {
        return config.run(stop).await;
    };
    let report = config.repair_once(lost).await?;
    log(lost, &report);
    if report.pending() > 0 {
        return Err(io::Error::other(format!(
            "{} streams still name the lost keeper",
            report.pending()
        )));
    }
    Ok(())
}
