use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::ExitCode;

use logkeeper::{PreparedJournal, ServerOptions};
use tokio::net::TcpListener;
use tokio_util::sync::CancellationToken;

#[cfg(not(feature = "ordered-daemon"))]
const USAGE: &str = "Usage: logkeeper <listen-address> <journal-directory> <journal-id>";

#[cfg(feature = "ordered-daemon")]
const USAGE: &str = "Usage: logkeeper <listen-address> <journal-directory> <journal-id>\n       logkeeper ordered <initialize|serve> <installed-manifest.json>\n       logkeeper ordered reserve-repair <target-manifest> <deployment-id> <ticket>\n       logkeeper ordered seal-repair <source-manifest> <target-group.json> <package> <ticket>...\n       logkeeper ordered install-repair <target-manifest> <deployment-id> <package>\n       logkeeper ordered route <installed-manifest> <deployment-id>\n       logkeeper ordered enroll <control-manifest> <worker-id> [prior-serial]\n       logkeeper ordered withdraw <control-manifest> <worker-id> <serial>\n       logkeeper ordered dispose-worker <control-manifest> <worker-id> <serial> <disposition-sha256>";

#[tokio::main]
async fn main() -> ExitCode {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.as_slice() == ["--help"] {
        println!("{USAGE}");
        #[cfg(feature = "stream")]
        println!("       logkeeper keeper --config FILE [--log-format human|json]");
        #[cfg(feature = "stream")]
        println!(
            "       logkeeper keeper recover-stream --config FILE --stream UUID --acknowledge-data-loss --lost KEEPER,KEEPER [--with KEEPER,KEEPER]"
        );
        #[cfg(feature = "stream")]
        println!("       logkeeper keeper inspect --config FILE [--stream UUID] [--json]");
        #[cfg(feature = "stream")]
        println!("       logkeeper keeper verify --config FILE [--json]");
        #[cfg(feature = "stream")]
        println!(
            "       logkeeper keeper dump-segment (--config FILE --segment ID | --file PATH) [--limit N] [--json]"
        );
        return ExitCode::SUCCESS;
    }
    match run(&args).await {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

async fn run(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    #[cfg(feature = "stream")]
    if args.first().is_some_and(|arg| arg == "keeper") {
        if let [_, action, flag, file] = args
            && action == "initialize"
            && flag == "--config"
        {
            logkeeper::stream::consensus::Config::read(std::path::Path::new(file))?.initialize()?;
            return Ok(());
        }
        if let [
            _,
            action,
            flag,
            file,
            stream_flag,
            stream,
            snapshot_flag,
            backup,
        ] = args
            && action == "repair-snapshot"
            && flag == "--config"
            && stream_flag == "--stream"
            && snapshot_flag == "--snapshot"
        {
            let stream = journal_contract::StreamId(uuid::Uuid::parse_str(stream)?.as_u128());
            logkeeper::stream::consensus::Config::read(std::path::Path::new(file))?
                .repair_snapshot(stream, std::path::Path::new(backup))
                .await?;
            return Ok(());
        }
        if args.get(1).is_some_and(|action| action == "recover-stream") {
            return recover_stream(&args[2..]).await;
        }
        if args.get(1).is_some_and(|action| action == "inspect") {
            return inspect_keeper(&args[2..]);
        }
        if args.get(1).is_some_and(|action| action == "verify") {
            return verify_keeper(&args[2..]);
        }
        if args.get(1).is_some_and(|action| action == "dump-segment") {
            return dump_segment(&args[2..]);
        }
        let mut config_file = None;
        let mut log_format = None;
        let mut iter = args[1..].iter();
        while let Some(flag) = iter.next() {
            match flag.as_str() {
                "--config" => config_file = iter.next(),
                "--log-format" => {
                    let value = iter
                        .next()
                        .ok_or("Usage: logkeeper keeper --config FILE [--log-format human|json]")?;
                    log_format = Some(
                        logkeeper::stream::consensus::LogFormat::parse(value)
                            .ok_or("invalid --log-format: expected human or json")?,
                    );
                }
                _ => {
                    return Err(
                        "Usage: logkeeper keeper --config FILE [--log-format human|json]".into(),
                    );
                }
            }
        }
        let Some(file) = config_file else {
            return Err("Usage: logkeeper keeper --config FILE [--log-format human|json]".into());
        };
        #[derive(serde::Deserialize)]
        #[serde(untagged)]
        enum KeeperConfig {
            Consensus(logkeeper::stream::consensus::Config),
            Stream(logkeeper::stream::transport::Config),
        }

        let config = serde_json::from_slice::<KeeperConfig>(&std::fs::read(file)?)?;
        let listen = match &config {
            KeeperConfig::Consensus(config) => {
                logkeeper::stream::consensus::logging::init(
                    log_format.unwrap_or(config.log_format),
                );
                config.listen
            }
            KeeperConfig::Stream(config) => config.listen,
        };
        let listener = TcpListener::bind(listen).await?;
        let cancellation = CancellationToken::new();
        let serving = async {
            match config {
                KeeperConfig::Consensus(config) => {
                    config.serve(listener, cancellation.clone()).await
                }
                KeeperConfig::Stream(config) => config.serve(listener, cancellation.clone()).await,
            }
        };
        tokio::pin!(serving);
        tokio::select! {
            result = &mut serving => result?,
            signal = shutdown_signal() => {
                cancellation.cancel();
                serving.await?;
                signal?;
            }
        }
        return Ok(());
    }
    #[cfg(feature = "ordered-daemon")]
    if args.first().is_some_and(|argument| argument == "ordered") {
        return run_ordered(args).await;
    }
    let [listen, data_dir, id] = args else {
        return Err(USAGE.into());
    };
    if !logkeeper::valid_journal_identity(id) {
        return Err("The journal ID must be a nonzero canonical UUID".into());
    }
    let address: SocketAddr = listen.parse()?;
    let listener = TcpListener::bind(address).await?;
    let (journal, installed) = PreparedJournal::open_for_member(
        ServerOptions {
            data_dir: PathBuf::from(data_dir),
            fsync: true,
            cache_bytes: ServerOptions::DEFAULT_CACHE_BYTES,
        },
        id.clone(),
    )
    .await?;
    if installed != *id {
        return Err("The journal directory already belongs to a different identity".into());
    }
    let cancellation = CancellationToken::new();
    let serving = journal.serve(listener, cancellation.clone());
    tokio::pin!(serving);
    tokio::select! {
        result = &mut serving => result?,
        signal = shutdown_signal() => {
            cancellation.cancel();
            serving.await?;
            signal?;
        }
    }
    Ok(())
}

#[cfg(feature = "stream")]
const RECOVER_USAGE: &str = "Usage: logkeeper keeper recover-stream --config FILE --stream UUID \
     --acknowledge-data-loss --lost KEEPER,KEEPER [--with KEEPER,KEEPER]";

/// Recovers a stream that lost two of its three voters from this stopped
/// keeper's replica. Without `--acknowledge-data-loss` it prints what it
/// would do and refuses. `--lost` names the two lost voters the operator
/// found down or fenced.
#[cfg(feature = "stream")]
async fn recover_stream(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut config = None;
    let mut stream = None;
    let mut recovery = logkeeper::stream::consensus::Recovery::default();
    let mut args = args.iter();
    while let Some(flag) = args.next() {
        match flag.as_str() {
            "--config" => config = args.next(),
            "--stream" => stream = args.next(),
            "--acknowledge-data-loss" => recovery.acknowledge_data_loss = true,
            "--with" | "--lost" => {
                let keepers = args
                    .next()
                    .ok_or(RECOVER_USAGE)?
                    .split(',')
                    .map(uuid::Uuid::parse_str)
                    .collect::<Result<Vec<_>, _>>()?;
                let keepers = Some(<[_; 2]>::try_from(keepers).map_err(|_| RECOVER_USAGE)?);
                if flag == "--with" {
                    recovery.with = keepers;
                } else {
                    recovery.lost = keepers;
                }
            }
            _ => return Err(RECOVER_USAGE.into()),
        }
    }
    let (Some(config), Some(stream)) = (config, stream) else {
        return Err(RECOVER_USAGE.into());
    };
    let stream = journal_contract::StreamId(uuid::Uuid::parse_str(stream)?.as_u128());
    let config = logkeeper::stream::consensus::Config::read(std::path::Path::new(config))?;
    logkeeper::stream::consensus::logging::init(config.log_format);
    let recovered = config.recover_stream(stream, recovery).await?;
    println!("{recovered}");
    Ok(())
}

#[cfg(feature = "stream")]
const INSPECT_USAGE: &str =
    "Usage: logkeeper keeper inspect --config FILE [--stream UUID] [--json]";
#[cfg(feature = "stream")]
const VERIFY_USAGE: &str = "Usage: logkeeper keeper verify --config FILE [--json]";
#[cfg(feature = "stream")]
const DUMP_SEGMENT_USAGE: &str = "Usage: logkeeper keeper dump-segment (--config FILE --segment ID | --file PATH) [--limit N] [--json]";

#[cfg(feature = "stream")]
fn inspect_keeper(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut config = None;
    let mut stream = None;
    let mut json = false;
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        match flag.as_str() {
            "--config" => config = iter.next(),
            "--stream" => stream = iter.next(),
            "--json" => json = true,
            _ => return Err(INSPECT_USAGE.into()),
        }
    }
    let Some(config) = config else {
        return Err(INSPECT_USAGE.into());
    };
    let filter = match stream {
        Some(raw) => Some(journal_contract::StreamId(
            uuid::Uuid::parse_str(raw)?.as_u128(),
        )),
        None => None,
    };
    let report = logkeeper::stream::consensus::Config::read(std::path::Path::new(config))?
        .inspect(filter)?;
    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print!("{report}");
    }
    Ok(())
}

#[cfg(feature = "stream")]
fn verify_keeper(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut config = None;
    let mut json = false;
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        match flag.as_str() {
            "--config" => config = iter.next(),
            "--json" => json = true,
            _ => return Err(VERIFY_USAGE.into()),
        }
    }
    let Some(config) = config else {
        return Err(VERIFY_USAGE.into());
    };
    let report =
        logkeeper::stream::consensus::Config::read(std::path::Path::new(config))?.verify()?;
    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print!("{report}");
    }
    if !report.ok {
        return Err("keeper media verification failed".into());
    }
    Ok(())
}

#[cfg(feature = "stream")]
fn dump_segment(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut config = None;
    let mut segment = None;
    let mut file = None;
    let mut limit = None;
    let mut json = false;
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        match flag.as_str() {
            "--config" => config = iter.next(),
            "--segment" => segment = Some(iter.next().ok_or(DUMP_SEGMENT_USAGE)?.parse::<u64>()?),
            "--file" => file = iter.next(),
            "--limit" => limit = Some(iter.next().ok_or(DUMP_SEGMENT_USAGE)?.parse::<usize>()?),
            "--json" => json = true,
            _ => return Err(DUMP_SEGMENT_USAGE.into()),
        }
    }
    let dump = match (config, segment, file) {
        (Some(config), Some(segment), None) => {
            logkeeper::stream::consensus::Config::read(std::path::Path::new(config))?
                .dump_segment(segment, limit)?
        }
        (None, None, Some(path)) => {
            logkeeper::stream::consensus::dump_segment_file(std::path::Path::new(path), limit)?
        }
        _ => return Err(DUMP_SEGMENT_USAGE.into()),
    };
    if json {
        println!("{}", serde_json::to_string_pretty(&dump)?);
    } else {
        print!("{dump}");
    }
    Ok(())
}

#[cfg(feature = "ordered-daemon")]
async fn run_ordered(args: &[String]) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    use logkeeper::ordered::{
        Command, Enrollment, Outcome,
        daemon::{ControlManifest, Manifest},
    };
    use std::path::Path;

    let [_, mode, path, rest @ ..] = args else {
        return Err(USAGE.into());
    };
    let path = Path::new(path);
    let command = match (mode.as_str(), rest) {
        ("enroll", [worker]) => Some(Command::Enroll {
            worker: worker.parse()?,
            expected: None,
        }),
        ("enroll", [worker, serial]) => {
            let worker = worker.parse()?;
            Some(Command::Enroll {
                worker,
                expected: Some(Enrollment {
                    worker,
                    serial: serial.parse()?,
                }),
            })
        }
        ("withdraw", [worker, serial]) => Some(Command::Withdraw {
            enrollment: Enrollment {
                worker: worker.parse()?,
                serial: serial.parse()?,
            },
        }),
        ("dispose-worker", [worker, serial, disposition]) => Some(Command::DisposeWorker {
            enrollment: Enrollment {
                worker: worker.parse()?,
                serial: serial.parse()?,
            },
            disposition: decode_digest(disposition)?,
        }),
        _ => None,
    };
    if let Some(command) = command {
        match ControlManifest::execute(path, command).await? {
            Outcome::Enrolled(enrollment) | Outcome::WorkerDisposed(enrollment) => {
                println!("{}", serde_json::to_string(&enrollment)?);
            }
            Outcome::Withdrawn => println!("withdrawn"),
            _ => return Err("The journal returned a different administrative outcome".into()),
        }
        return Ok(());
    }
    let manifest = Manifest::read(path)?;
    match (mode.as_str(), rest) {
        ("initialize", []) => manifest.initialize()?,
        ("route", [deployment]) => {
            println!(
                "{}",
                serde_json::to_string_pretty(&manifest.application_route(deployment.parse()?)?)?
            );
        }
        ("reserve-repair", [deployment, output]) => {
            manifest.reserve_repair(deployment.parse()?, Path::new(output))?;
        }
        ("seal-repair", [destination, output, tickets @ ..]) => {
            let tickets = tickets.iter().map(Path::new).collect::<Vec<_>>();
            manifest
                .seal_repair(Path::new(destination), &tickets, Path::new(output))
                .await?;
        }
        ("install-repair", [deployment, package]) => {
            manifest.install_repair(deployment.parse()?, Path::new(package))?;
        }
        ("serve", []) => {
            let cancellation = CancellationToken::new();
            let serving = manifest.run(cancellation.clone());
            tokio::pin!(serving);
            tokio::select! {
                result = &mut serving => result?,
                signal = shutdown_signal() => {
                    cancellation.cancel();
                    serving.await?;
                    signal?;
                }
            }
        }
        _ => return Err(USAGE.into()),
    }
    Ok(())
}

#[cfg(feature = "ordered-daemon")]
fn decode_digest(value: &str) -> Result<[u8; 32], &'static str> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("The disposition must be a SHA-256 hex digest");
    }
    let mut digest = [0; 32];
    for (i, byte) in digest.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * i..2 * i + 2], 16)
            .map_err(|_| "Invalid disposition digest")?;
    }
    Ok(digest)
}

#[cfg(unix)]
async fn shutdown_signal() -> std::io::Result<()> {
    use tokio::signal::unix::{SignalKind, signal};

    let mut termination = signal(SignalKind::terminate())?;
    tokio::select! {
        result = tokio::signal::ctrl_c() => result,
        _ = termination.recv() => Ok(()),
    }
}

#[cfg(not(unix))]
async fn shutdown_signal() -> std::io::Result<()> {
    tokio::signal::ctrl_c().await
}
