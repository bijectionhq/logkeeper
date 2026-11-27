//! `logkeeper keeper debug-bundle`: one archive an operator can attach to a
//! report. It holds this keeper's configuration with its secrets redacted,
//! the `/metrics`, `/problems`, `/status`, `/ready`, `/safe-to-stop` and
//! `/live` answers of every keeper whose admin listener answers, and, given a
//! stopped data directory, its offline `inspect` and `verify` reports.

use std::{
    collections::BTreeMap,
    io,
    net::SocketAddr,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

use serde::Serialize;
use tokio_rustls::TlsConnector;

use super::Config;
use crate::stream::wire::KeeperId;

/// The admin paths collected from each keeper, and the file each lands in.
const PATHS: [(&str, &str); 6] = [
    ("/metrics", "metrics.txt"),
    ("/problems", "problems.json"),
    ("/status", "status.json"),
    ("/ready", "ready.json"),
    ("/safe-to-stop", "safe-to-stop.json"),
    ("/live", "live.json"),
];
const REDACTED: &str = "<redacted>";

#[derive(Serialize)]
struct Manifest {
    keeper: uuid::Uuid,
    version: &'static str,
    created_unix_secs: u64,
    endpoints: Vec<Collected>,
    offline: Option<String>,
}

#[derive(Serialize)]
struct Collected {
    keeper: Option<uuid::Uuid>,
    address: SocketAddr,
    /// Per path: the HTTP status, or the error that kept it from answering.
    answers: BTreeMap<&'static str, String>,
}

impl Config {
    /// The settings `/status` reports, without key material.
    pub(super) fn summary(&self) -> serde_json::Value {
        serde_json::json!({
            "keeper": self.keeper,
            "listen": self.listen,
            "data": self.data,
            "tls": {
                "certificate": self.tls.certificate,
                "private_key": REDACTED,
                "ca": self.tls.ca,
            },
            "keepers": self.keepers,
            "peers": self.peers,
            "bulk": self.bulk,
            "domains": self.domains,
            "catalog": self.catalog,
            "catalog_voters": self.catalog_voters,
            "readers": self.readers,
            "writers": self.writers,
            "administrators": self.administrators,
            "max_streams": self.max_streams,
            "repair_after_secs": self.repair_after_secs,
            "park_after_secs": self.park_after_secs,
            "snapshot_send_bytes_per_second": self.snapshot_send_bytes_per_second,
            "timed_original": self.timed_original.is_some(),
            "log_format": self.log_format,
            "offload": self.offload.as_ref().map(|offload| serde_json::json!({
                "url": offload.url,
                "endpoint": offload.endpoint,
                "secret_access_key": offload.secret_access_key.as_ref().map(|_| REDACTED),
                "batch_bytes": offload.batch_bytes,
                "batch_interval_ms": offload.batch_interval_ms,
                "max_lag_bytes": offload.max_lag_bytes,
                "backpressure": offload.backpressure,
                "retain_local_bytes": offload.retain_local_bytes,
            })),
            "admin": self.admin.as_ref().map(|admin| serde_json::json!({
                "listen": admin.listen,
                "mtls": admin.mtls,
                "cluster": admin.cluster,
            })),
        })
    }

    /// Collects a debug bundle as an uncompressed tar archive. `raw` is the
    /// configuration file as read, which the bundle holds redacted. `extra`
    /// adds admin listeners to the ones the configuration names. `offline`
    /// is a stopped keeper's data directory to inspect and verify.
    pub async fn debug_bundle(
        &self,
        raw: &serde_json::Value,
        extra: &[SocketAddr],
        offline: Option<PathBuf>,
    ) -> io::Result<Vec<u8>> {
        let mut archive = Tar::default();
        let mut config = raw.clone();
        redact(&mut config);
        archive.add("config.json", &serde_json::to_vec_pretty(&config)?);

        let mut endpoints = Vec::<(Option<uuid::Uuid>, SocketAddr)>::new();
        if let Some(admin) = &self.admin {
            endpoints.push((Some(self.keeper), admin.listen));
            endpoints.extend(admin.cluster.iter().map(|(id, at)| (Some(*id), *at)));
        }
        endpoints.extend(extra.iter().map(|at| (None, *at)));
        endpoints.sort_by_key(|(_, at)| *at);
        endpoints.dedup_by_key(|(_, at)| *at);
        let tls = match &self.admin {
            Some(admin) if admin.mtls => Some(
                self.tls
                    .peer_protocol(KeeperId(self.keeper.as_u128()), b"http/1.1")?,
            ),
            _ => None,
        };
        let fetched = futures::future::join_all(endpoints.iter().map(|(_, at)| {
            let tls = tls.clone();
            async move {
                let mut answers = Vec::new();
                for (path, _) in PATHS {
                    answers.push(fetch(*at, tls.clone(), path).await);
                }
                answers
            }
        }))
        .await;
        let mut collected = Vec::new();
        for ((keeper, at), answers) in endpoints.iter().zip(fetched) {
            let directory = match keeper {
                Some(keeper) => format!("keepers/{keeper}"),
                None => format!("keepers/{}", at.to_string().replace([':', '[', ']'], "_")),
            };
            let mut summary = BTreeMap::new();
            for ((path, file), answer) in PATHS.iter().zip(answers) {
                match answer {
                    Ok((status, body)) => {
                        summary.insert(*path, status.to_string());
                        archive.add(&format!("{directory}/{file}"), &body);
                    }
                    Err(error) => {
                        summary.insert(*path, format!("error: {error}"));
                    }
                }
            }
            collected.push(Collected {
                keeper: *keeper,
                address: *at,
                answers: summary,
            });
        }

        let offline = match offline {
            None => None,
            Some(data) => {
                let mut stopped = self.clone();
                stopped.data = data.clone();
                let outcome = tokio::task::spawn_blocking(move || {
                    let inspect = stopped.inspect(None);
                    let verify = stopped.verify();
                    (inspect, verify)
                })
                .await
                .map_err(io::Error::other)?;
                let mut notes = Vec::new();
                match outcome.0 {
                    Ok(report) => {
                        archive.add("offline/inspect.json", &serde_json::to_vec_pretty(&report)?)
                    }
                    Err(error) => notes.push(format!("inspect: {error}")),
                }
                match outcome.1 {
                    Ok(report) => {
                        archive.add("offline/verify.json", &serde_json::to_vec_pretty(&report)?)
                    }
                    Err(error) => notes.push(format!("verify: {error}")),
                }
                Some(if notes.is_empty() {
                    format!("inspected {}", data.display())
                } else {
                    notes.join("; ")
                })
            }
        };

        let manifest = Manifest {
            keeper: self.keeper,
            version: env!("CARGO_PKG_VERSION"),
            created_unix_secs: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
            endpoints: collected,
            offline,
        };
        archive.add("manifest.json", &serde_json::to_vec_pretty(&manifest)?);
        Ok(archive.finish())
    }
}

/// Replaces every value whose key names key material or a credential.
fn redact(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Object(map) => {
            for (key, value) in map.iter_mut() {
                if secret(key) {
                    *value = serde_json::Value::String(REDACTED.into());
                } else {
                    redact(value);
                }
            }
        }
        serde_json::Value::Array(values) => values.iter_mut().for_each(redact),
        _ => (),
    }
}

fn secret(key: &str) -> bool {
    let key = key.to_ascii_lowercase();
    key == "key"
        || key.ends_with("_key")
        || key.ends_with("-key")
        || [
            "private",
            "secret",
            "password",
            "passphrase",
            "token",
            "credential",
        ]
        .iter()
        .any(|word| key.contains(word))
}

/// GETs `path` from an admin listener: its HTTP status and body.
async fn fetch(
    at: SocketAddr,
    tls: Option<TlsConnector>,
    path: &str,
) -> io::Result<(u16, Vec<u8>)> {
    crate::stream::consensus::operator::admin_request(&at.to_string(), tls, None, "GET", path).await
}

/// A minimal ustar writer: regular files only, names under 100 bytes.
#[derive(Default)]
struct Tar(Vec<u8>);

impl Tar {
    fn add(&mut self, name: &str, body: &[u8]) {
        let name = format!("logkeeper-debug/{name}");
        let mut header = [0u8; 512];
        let bytes = name.as_bytes();
        let length = bytes.len().min(99);
        header[..length].copy_from_slice(&bytes[..length]);
        octal(&mut header[100..108], 0o644);
        octal(&mut header[108..116], 0);
        octal(&mut header[116..124], 0);
        octal(&mut header[124..136], body.len() as u64);
        let mtime = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        octal(&mut header[136..148], mtime);
        header[156] = b'0';
        header[257..263].copy_from_slice(b"ustar\0");
        header[263..265].copy_from_slice(b"00");
        header[148..156].fill(b' ');
        let checksum = header.iter().map(|byte| u64::from(*byte)).sum::<u64>();
        octal(&mut header[148..155], checksum);
        header[155] = b' ';
        self.0.extend_from_slice(&header);
        self.0.extend_from_slice(body);
        let padding = (512 - body.len() % 512) % 512;
        self.0.resize(self.0.len() + padding, 0);
    }

    fn finish(mut self) -> Vec<u8> {
        self.0.resize(self.0.len() + 1024, 0);
        self.0
    }
}

/// Writes `value` as zero-padded octal digits followed by a NUL.
fn octal(field: &mut [u8], value: u64) {
    let digits = field.len() - 1;
    let text = format!("{value:0digits$o}");
    let text = &text.as_bytes()[text.len().saturating_sub(digits)..];
    field[..digits].copy_from_slice(text);
    field[digits] = 0;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn redaction_covers_keys_and_credentials() {
        let mut config = serde_json::json!({
            "keeper": "k",
            "keepers": {"a": "127.0.0.1:1"},
            "tls": {"certificate": "c.pem", "private_key": "k.pem", "ca": "ca.pem"},
            "timed_original": {"signing_key": "s.pem", "token": "t"},
            "list": [{"password": "p"}],
        });
        redact(&mut config);
        assert_eq!(config["keeper"], "k");
        assert_eq!(config["keepers"]["a"], "127.0.0.1:1");
        assert_eq!(config["tls"]["certificate"], "c.pem");
        assert_eq!(config["tls"]["private_key"], REDACTED);
        assert_eq!(config["timed_original"]["signing_key"], REDACTED);
        assert_eq!(config["timed_original"]["token"], REDACTED);
        assert_eq!(config["list"][0]["password"], REDACTED);
    }

    #[test]
    fn tar_entries_are_aligned_and_checksummed() {
        let mut archive = Tar::default();
        archive.add("a.txt", b"hello");
        archive.add("b/c.json", &[b'x'; 513]);
        let bytes = archive.finish();
        assert_eq!(bytes.len() % 512, 0);
        assert_eq!(bytes.len(), 512 + 512 + 512 + 1024 + 1024);
        let header = &bytes[..512];
        assert!(header.starts_with(b"logkeeper-debug/a.txt\0"));
        assert_eq!(&header[257..262], b"ustar");
        let mut copy = header.to_vec();
        copy[148..156].fill(b' ');
        let sum = copy.iter().map(|byte| u64::from(*byte)).sum::<u64>();
        let recorded = std::str::from_utf8(&header[148..154]).unwrap();
        assert_eq!(u64::from_str_radix(recorded, 8).unwrap(), sum);
        assert_eq!(&bytes[512..517], b"hello");
        let size = std::str::from_utf8(&bytes[1024 + 124..1024 + 135]).unwrap();
        assert_eq!(u64::from_str_radix(size, 8).unwrap(), 513);
    }
}
