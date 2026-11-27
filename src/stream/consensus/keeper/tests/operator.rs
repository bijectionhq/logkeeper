//! `logkeeper admin`: the operator client against a running cluster.

use super::ops::start_admin_cluster;
use super::*;
use crate::stream::consensus::{Configuration, Operator, OperatorConfig, admin_command};

pub(super) fn operator(
    cluster: &Cluster,
    admin: &BTreeMap<Uuid, SocketAddr>,
    mtls: bool,
) -> Operator {
    Operator::new(OperatorConfig {
        tls: cluster.credentials.clone(),
        keepers: cluster.keepers.clone(),
        catalog: cluster.catalog,
        catalog_voters: cluster.catalog_voters,
        admin: admin.clone(),
        admin_mtls: mtls,
        placement: None,
        deadline_ms: 10_000,
    })
    .unwrap()
}

/// Writes an operator configuration file for `admin_command`.
pub(super) fn operator_file(
    cluster: &Cluster,
    admin: &BTreeMap<Uuid, SocketAddr>,
    dir: &Path,
) -> String {
    let tls = &cluster.credentials;
    let config = serde_json::json!({
        "tls": {
            "certificate": tls.certificate,
            "private_key": tls.private_key,
            "ca": tls.ca,
        },
        "keepers": cluster.keepers,
        "catalog": cluster.catalog,
        "admin": admin,
    });
    let path = dir.join("operator.json");
    std::fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
    path.to_str().unwrap().to_owned()
}

pub(super) async fn admin(args: &[&str]) -> io::Result<crate::stream::consensus::AdminOutcome> {
    admin_command(&args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>()).await
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn admin_cli_creates_inspects_moves_and_retires_a_stream() {
    let (mut cluster, addrs) = start_admin_cluster(true).await;
    let dir = tempfile::tempdir().unwrap();
    let file = operator_file(&cluster, &addrs, dir.path());
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let stream = Uuid::new_v4();
    let roster = voters.map(|voter| voter.to_string()).join(",");
    let created = admin(&[
        "create",
        "--config",
        &file,
        "--stream",
        &stream.to_string(),
        "--voters",
        &roster,
        "--quota-bytes",
        "67108864",
        "--json",
    ])
    .await
    .unwrap();
    assert!(created.ok && created.json);
    assert_eq!(
        created.report["configuration"]["voters"],
        serde_json::json!(voters)
    );

    let operator = operator(&cluster, &addrs, true);
    let id = StreamId(stream.as_u128());
    let status = operator.stream_status(id).await;
    assert!(status.errors.is_empty(), "{:?}", status.errors);
    assert_eq!(status.configuration.unwrap().voters, voters);
    assert_eq!(status.head, Some(0));
    assert!(status.leader.is_some_and(|leader| voters.contains(&leader)));
    assert_eq!(status.replicas.len(), 3);
    assert!(
        status
            .replicas
            .iter()
            .all(|replica| replica.reachable && replica.replica == "healthy")
    );
    let text = crate::stream::consensus::render_report(&serde_json::to_value(&status).unwrap());
    assert!(text.contains("replica: healthy"), "{text}");

    // An administrator may move leadership and acknowledge a recovery that
    // never happened, which only returns the head.
    let follower = voters
        .into_iter()
        .find(|voter| Some(*voter) != status.leader)
        .unwrap();
    operator.prefer_leader(id, follower).await.unwrap();
    assert_eq!(operator.acknowledge_recovery(id).await.unwrap(), 0);

    // A voter's copy cannot be retired.
    let refused = operator.retire(id, voters[0]).await.unwrap_err();
    assert!(refused.to_string().contains("still a voter"), "{refused}");

    let moved = admin(&[
        "replace",
        "--config",
        &file,
        "--stream",
        &stream.to_string(),
        "--old",
        &voters[0].to_string(),
        "--new",
        &cluster.ids[3].to_string(),
    ])
    .await
    .unwrap();
    let configuration: Configuration =
        serde_json::from_value(moved.report["configuration"].clone()).unwrap();
    assert!(configuration.voters.contains(&cluster.ids[3]));
    assert!(!configuration.voters.contains(&voters[0]));

    // The removed voter's copy retires, by hand or by itself.
    match operator.retire(id, voters[0]).await {
        Ok(report) => assert_eq!(report["retired"], true),
        Err(_) => {}
    }
    timeout(WAIT, async {
        while cluster
            .client(&cluster.credentials)
            .keeper_status(voters[0], id)
            .await
            .is_ok_and(|status| status.replica.is_some())
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the removed copy retires");

    let keeper = operator.keeper_status(voters[1]).await.unwrap();
    assert_eq!(keeper["keeper"], voters[1].to_string());
    let problems = operator.problems().await;
    assert_eq!(problems.keepers.len(), addrs.len());
    assert!(
        problems
            .keepers
            .iter()
            .all(|answer| answer.status == Some(200))
    );

    let unsupported = admin(&["finalize-version", "--config", &file]).await;
    assert_eq!(
        unsupported.err().map(|error| error.kind()),
        Some(io::ErrorKind::Unsupported)
    );
    let unknown = admin(&["problems", "--config", &file, "--bogus", "1"]).await;
    assert!(unknown.is_err());

    cluster.stop_all().await;
}
