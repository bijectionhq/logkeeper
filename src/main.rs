use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::ExitCode;

use logkeeper::{PreparedJournal, ServerOptions};
use tokio::net::TcpListener;
use tokio_util::sync::CancellationToken;

const USAGE: &str = "Usage: logkeeper <listen-address> <journal-directory> <journal-id>";

#[tokio::main]
async fn main() -> ExitCode {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.as_slice() == ["--help"] {
        println!("{USAGE}");
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

async fn run(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let [listen, data_dir, id] = args else { return Err(USAGE.into()); };
    if !logkeeper::valid_journal_identity(id) {
        return Err("The journal ID must be a nonzero canonical UUID".into());
    }
    let address: SocketAddr = listen.parse()?;
    let listener = TcpListener::bind(address).await?;
    let (journal, installed) = PreparedJournal::open_for_member(
        ServerOptions { data_dir: PathBuf::from(data_dir), fsync: true, cache_bytes: ServerOptions::DEFAULT_CACHE_BYTES },
        id.clone(),
    ).await?;
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
