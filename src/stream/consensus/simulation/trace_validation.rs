use std::{
    fs::File,
    io::{BufWriter, Write},
    panic::AssertUnwindSafe,
    path::Path,
    process::Command,
    time::Duration,
};

use futures::FutureExt;

use super::{Profile, RunConfig, execute_plan_traced, generate_plan};
use crate::stream::consensus::trace::Capture;

async fn run_traces(cases: &[(u64, Profile, usize)], required: &str) {
    let temporary = match std::env::var_os("LOGKEEPER_TRACE_OUTPUT") {
        Some(root) => {
            std::fs::create_dir_all(&root).unwrap();
            tempfile::tempdir_in(root).unwrap()
        }
        None => tempfile::tempdir().unwrap(),
    };
    let mut inputs = Vec::new();
    for &(seed, profile, replication) in cases {
        let config = RunConfig {
            profile: Some(profile),
            replication,
            ..RunConfig::standard()
        };
        let mut plan = generate_plan(seed, &config);
        plan.options.replicated_catalog = true;
        let capture = Capture::new();
        eprintln!("Recording {profile:?} RF {replication} seed {seed}");
        let result = AssertUnwindSafe(tokio::time::timeout(
            Duration::from_secs(180),
            execute_plan_traced(&plan, Some(&capture)),
        ))
        .catch_unwind()
        .await;
        let path = temporary
            .path()
            .join(format!("{profile:?}-rf{replication}-{seed}.ndjson"));
        let mut out = BufWriter::new(File::create(&path).unwrap());
        capture.write(&mut out).unwrap();
        out.flush().unwrap();
        let error = match result {
            Ok(Ok(Ok(_))) => None,
            Ok(Ok(Err(error))) => Some(error.to_string()),
            Ok(Err(_)) => Some("180 s deadline exceeded".into()),
            Err(panic) => {
                eprintln!("Incomplete trace in {}", temporary.keep().display());
                std::panic::resume_unwind(panic);
            }
        };
        if let Some(error) = error {
            let directory = temporary.keep();
            panic!(
                "fault harness failed on {profile:?} RF {replication} seed {seed}: {error}\ntrace in {}",
                directory.display()
            );
        }
        inputs.push(path);
    }
    let checker = Path::new(env!("CARGO_MANIFEST_DIR")).join("verification/tla/check_traces.py");
    let mut command = Command::new("python3");
    command.arg(checker).args(["--require", required]);
    if !required.is_empty() {
        command.arg("--controls");
    }
    let status = command
        .args(inputs)
        .status()
        .expect("start the TLC trace checker with Python");
    if !status.success() {
        panic!(
            "trace validation failed; inputs in {}",
            temporary.keep().display()
        );
    }
}

const CORE: &str = "Vote,Append,Apply,DurableCommit,Snapshot,BuildSnapshot,Park,\
                    AcceptPark,LeaseGrant,LeaseExpiry,LeaseGate,RecoveryTransaction,RecoveryReady,Recover,\
                    RecoveryMarker,Fence,Upload,Offload";

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_trace_ci() {
    // The CI job supplies Java and the pinned TLC. Ordinary Rust-only test
    // runs can also opt in without extending the Rust toolchain dependencies.
    if std::env::var_os("LOGKEEPER_TRACE_CI").is_none() {
        return;
    }
    run_traces(
        &[
            (1, Profile::ReplicatedCatalog, 3),
            (3, Profile::ParkingAndWake, 3),
            (4, Profile::OperatorRecovery, 5),
            (0, Profile::Offload, 3),
        ],
        CORE,
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "multiple seeded keeper clusters and TLC; requires Python and Java"]
async fn consensus_trace_soak() {
    let first = std::env::var("LOGKEEPER_TRACE_FIRST_SEED").map_or(0, |s| s.parse().unwrap());
    let count = std::env::var("LOGKEEPER_TRACE_SEEDS").map_or(24, |s| s.parse().unwrap());
    assert!(count > 0, "request at least one trace seed");
    let cases: Vec<_> = (first..first + count)
        .map(|seed| {
            let profile = if seed % 7 == 6 {
                Profile::Offload
            } else {
                Profile::ALL[(seed % 7) as usize]
            };
            let replication = if seed % 2 == 0 { 5 } else { 3 };
            (seed, profile, replication)
        })
        .collect();
    run_traces(&cases, "").await;
}
