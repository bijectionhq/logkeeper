//! `logkeeper admin`: the operator client against a running cluster.

use super::ops::start_admin_cluster;
use super::*;
use crate::stream::consensus::Voters;
use crate::stream::consensus::{Configuration, Operator, OperatorConfig, admin_command};

pub(super) fn operator_config(
    cluster: &Cluster,
    admin: &BTreeMap<Uuid, SocketAddr>,
) -> OperatorConfig {
    OperatorConfig {
        tls: cluster.credentials.clone(),
        keepers: cluster.keepers.clone(),
        catalog: cluster.catalog,
        catalog_voters: cluster.catalog_voters,
        admin: admin.iter().map(|(id, at)| (*id, (*at).into())).collect(),
        admin_mtls: true,
        placement: None,
        deadline_ms: 10_000,
        offload: None,
    }
}

pub(super) fn operator(
    cluster: &Cluster,
    admin: &BTreeMap<Uuid, SocketAddr>,
    mtls: bool,
) -> Operator {
    let mut config = operator_config(cluster, admin);
    config.admin_mtls = mtls;
    Operator::new(config).unwrap()
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

    let finalized = admin(&["finalize-version", "--config", &file])
        .await
        .unwrap();
    assert_eq!(
        finalized.report["cluster_version"],
        crate::stream::consensus::CLUSTER_VERSION_CURRENT
    );
    let unknown = admin(&["problems", "--config", &file, "--bogus", "1"]).await;
    assert!(unknown.is_err());

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn decommission_retires_replicas_without_losing_records() {
    let (mut cluster, addrs) = start_admin_cluster(true).await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let leaving = voters[0];
    let client = cluster.client(&cluster.credentials);
    let stream = StreamId(Uuid::new_v4().as_u128());
    client
        .create(stream, Voters::from(voters), 1 << 26)
        .await
        .unwrap();
    let sealed = client.seal(stream, Epoch(0), Uuid::new_v4()).await.unwrap();
    client
        .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"keep me"))
        .await
        .unwrap();

    let operator = operator(&cluster, &addrs, true);
    assert!(
        operator
            .set_mode(cluster.catalog, "/decommission")
            .await
            .is_err()
    );
    let report = operator.set_mode(leaving, "/decommission").await.unwrap();
    assert_eq!(report["mode"], "decommissioning");
    assert_eq!(report["safe_to_delete"], false);
    cluster.running.remove(&leaving).unwrap().stop().await;
    cluster.restart(leaving).await;
    let (report, finished) = operator
        .wait_for(leaving, "safe_to_delete", WAIT, |_| ())
        .await
        .unwrap();
    assert!(finished, "{report}");
    let configuration = client.configuration(stream).await.unwrap();
    assert!(!configuration.voters.contains(&leaving));
    assert_eq!(client.head(stream).await.unwrap(), Lsn(1));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn drain_moves_leadership_off_a_keeper_and_survives_restart() {
    let (mut cluster, addrs) = start_admin_cluster(true).await;
    let voters = [cluster.ids[0], cluster.ids[1], cluster.ids[2]];
    let client = cluster.client(&cluster.credentials);
    let mut streams = Vec::new();
    for _ in 0..3 {
        let stream = StreamId(Uuid::new_v4().as_u128());
        client
            .create(stream, Voters::from(voters), 1 << 26)
            .await
            .unwrap();
        streams.push(stream);
    }
    let drained = cluster.leader_after_head(&client, streams[0]).await;
    let operator = operator(&cluster, &addrs, true);

    // Only an administrator changes the mode; a writer is refused.
    let mut other = operator_config(&cluster, &addrs);
    other.tls = cluster.other.clone();
    let refused = Operator::new(other)
        .unwrap()
        .set_mode(drained, "/drain")
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("403"), "{refused}");

    let report = operator.set_mode(drained, "/drain").await.unwrap();
    assert_eq!(report["mode"], "draining");
    let (report, done) = operator
        .wait_for(drained, "drained", WAIT, |_| ())
        .await
        .unwrap();
    assert!(done, "{report}");
    for stream in &streams {
        let sealed = client
            .seal(*stream, Epoch(0), Uuid::new_v4())
            .await
            .unwrap();
        client
            .append(*stream, sealed.fence, Lsn(1), Bytes::from_static(b"x"))
            .await
            .unwrap();
    }
    assert!(
        !client
            .keeper_status(drained, streams[0])
            .await
            .unwrap()
            .accepting
    );
    let (_, _, metrics) =
        super::ops::https_get(addrs[&drained], &cluster.credentials, "/metrics").await;
    assert!(metrics.contains("logkeeper_consensus_operator_mode{mode=\"draining\"} 1"));

    // The mark is durable: after a restart the keeper still leads nothing,
    // even once its streams elect again.
    cluster.running.remove(&drained).unwrap().stop().await;
    cluster.restart(drained).await;
    let report = operator.drain_status(drained).await.unwrap();
    assert_eq!(report["mode"], "draining");
    tokio::time::sleep(Duration::from_secs(2)).await;
    for stream in &streams {
        client.head(*stream).await.unwrap();
    }
    let report = operator.drain_status(drained).await.unwrap();
    assert_eq!(report["led"], 0, "{report}");
    assert_eq!(report["drained"], true);

    let report = operator.set_mode(drained, "/undrain").await.unwrap();
    assert_eq!(report["mode"], "serving");
    timeout(WAIT, async {
        while !client
            .keeper_status(drained, streams[0])
            .await
            .is_ok_and(|status| status.accepting)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("an undrained keeper accepts streams again");
    cluster.stop_all().await;
}

/// A draining voter starts no election of its own, but it campaigns as a
/// last resort when it is the only voter that can win: here the leader
/// died after committing an entry that only the draining voter shares, so
/// the third voter's log is behind and the draining voter refuses it.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_draining_voter_campaigns_when_no_other_voter_can_win() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(232);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal.prefer_leader(stream, c).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, c).await);
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap()
        .fence;
    cluster.running[&a]
        .engine
        .set_mode(super::super::drain::Mode::Draining, "test")
        .await
        .unwrap();
    // `b` misses everything `c` sends from now on.
    let leader = c.as_u128();
    *cluster.running[&b].engine.reject_append.write() = Some(Box::new(move |group, sender, _| {
        group == stream && sender == leader
    }));
    assert_eq!(
        journal
            .append(stream, fence, Lsn(1), Bytes::from_static(b"one"))
            .await,
        Ok(Lsn(1))
    );
    // `c` crashes rather than stopping, so it hands nothing off.
    let crashed = cluster.running.remove(&c).unwrap();
    crashed.engine.crash.store(true, Ordering::Release);
    crashed.stop().await;
    let head = timeout(WAIT, async {
        loop {
            match journal.head(stream).await {
                Ok(head) => break head,
                Err(_) => tokio::time::sleep(Duration::from_millis(100)).await,
            }
        }
    })
    .await
    .expect("the stream elected a leader with a draining voter");
    assert_eq!(head, Lsn(1));
    cluster.stop_all().await;
}
