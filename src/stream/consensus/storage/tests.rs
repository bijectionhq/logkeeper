//! The leader's in-flight appends against the WAL queues.

use std::{fs, path::Path, time::Duration};

use bytes::Bytes;
use journal_contract::{Epoch, Lsn};
use openraft::{
    EntryPayload, Membership,
    storage::{RaftLogStorage as _, RaftSnapshotBuilder as _, RaftStateMachine as _},
};
use tokio::sync::oneshot;
use uuid::Uuid;

use super::*;
use crate::stream::consensus::Voters;
use crate::stream::consensus::{Fence, placement::Placement, state::Command};

const KEEPER: u128 = 1;

fn genesis(stream: u128) -> Genesis {
    Genesis {
        stream: StreamId(stream),
        voters: Voters::from([1, 2, 3].map(Uuid::from_u128)),
        quota_bytes: 64 * 1024 * 1024,
        immutable: false,
        authenticated: false,
    }
}

fn placement() -> Placement {
    let ids = [1, 2, 3].map(Uuid::from_u128);
    let keepers = ids
        .into_iter()
        .enumerate()
        .map(|(i, id)| {
            (
                id,
                std::net::SocketAddr::from(([127, 0, 0, 1], 6000 + i as u16)).into(),
            )
        })
        .collect();
    let domains = ids
        .into_iter()
        .zip(["a", "b", "c"].map(String::from))
        .collect();
    Placement::new(&keepers, domains, Default::default()).unwrap()
}

fn entry(index: u64) -> Entry {
    Entry {
        log_id: LogId::new(
            openraft::vote::leader_id_std::CommittedLeaderId::new(2),
            index,
        ),
        payload: EntryPayload::Normal(Command::Append {
            fence: Fence {
                epoch: Epoch(1),
                writer: Uuid::from_u128(4),
            },
            owner: "urn:logkeeper:client:writer".into(),
            at: Lsn(index),
            payload: Bytes::from(vec![index as u8; 64]),
        }),
    }
}

fn open(dir: &Path) -> Disk {
    let data = dir.join("data");
    let registry = dir.join("registry");
    if !registry.exists() {
        fs::create_dir(&registry).unwrap();
        Enrollment::test(data.clone(), registry.clone(), Uuid::from_u128(KEEPER))
            .initialize()
            .unwrap();
    }
    Disk::open(Enrollment::test(data, registry, Uuid::from_u128(KEEPER))).unwrap()
}

/// A leader's store of `stream`, registered with this keeper's vote.
async fn leader(disk: &Disk, stream: u128) -> LogStore {
    let genesis = genesis(stream);
    disk.protocol(Record::Register(genesis.clone()))
        .await
        .unwrap();
    disk.protocol(Record::Vote(genesis.stream, Vote::new_committed(2, KEEPER)))
        .await
        .unwrap();
    let state = StateMachine::open(disk, genesis.clone(), placement())
        .await
        .unwrap();
    LogStore {
        disk: disk.clone(),
        stream: genesis.stream,
        generation: state.generation(),
        state,
        keeper: KEEPER,
        follower: Arc::default(),
        asynchronous: true,
        inflight: disk.inflight(genesis.stream),
    }
}

fn durable(disk: &Disk, stream: u128) -> Vec<u64> {
    disk.log(StreamId(stream), |log| {
        log.entries.keys().copied().collect()
    })
}

/// Holds the WAL thread inside a round of a local write of `stream`, so
/// writes queued meanwhile wait behind it.
async fn hold(disk: &Disk, stream: u128) -> std::sync::mpsc::Sender<bool> {
    let (entered, inside) = tokio::sync::oneshot::channel();
    let (resume, held) = std::sync::mpsc::channel();
    disk.fail_replication_at(
        StreamId(stream),
        ReplicaFault::Hold {
            entered,
            resume: held,
        },
    );
    let writer = disk.clone();
    tokio::spawn(async move {
        writer
            .write(Record::Vote(
                StreamId(stream),
                Vote::new_committed(2, KEEPER),
            ))
            .await
    });
    inside.await.unwrap();
    resume
}

async fn append(store: &mut LogStore, entries: Vec<Entry>) -> oneshot::Receiver<io::Result<()>> {
    use openraft::type_config::TypeConfigExt as _;
    let (flushed, reported) = RaftTypes::oneshot();
    store
        .append(entries, IOFlushed::signal(flushed))
        .await
        .unwrap();
    let (forward, durable) = oneshot::channel();
    tokio::spawn(async move {
        let _ = forward.send(
            reported
                .await
                .unwrap_or_else(|_| Err(io::Error::other("dropped"))),
        );
    });
    durable
}

#[tokio::test]
async fn a_leader_append_is_readable_before_it_is_durable() {
    let dir = tempfile::tempdir().unwrap();
    let disk = open(dir.path());
    let mut store = leader(&disk, 1).await;
    let _other = leader(&disk, 2).await;
    let resume = hold(&disk, 2).await;
    let mut flushed = append(&mut store, (0..3).map(entry).collect()).await;
    // Returned with the write still queued behind the held round.
    assert!(flushed.try_recv().is_err());
    assert!(durable(&disk, 1).is_empty());
    let read = store.try_get_log_entries(0..3).await.unwrap();
    assert_eq!(read, (0..3).map(entry).collect::<Vec<_>>());
    assert_eq!(
        store.get_log_state().await.unwrap().last_log_id,
        Some(entry(2).log_id)
    );
    resume.send(true).unwrap();
    flushed.await.unwrap().unwrap();
    assert_eq!(durable(&disk, 1), [0, 1, 2]);
    assert_eq!(store.try_get_log_entries(0..3).await.unwrap(), read);
    assert!(store.inflight.idle());
    disk.shutdown().await.unwrap();
}

#[tokio::test]
async fn a_conflicting_truncation_waits_for_an_append_in_flight() {
    let dir = tempfile::tempdir().unwrap();
    let disk = open(dir.path());
    let mut store = leader(&disk, 1).await;
    let _other = leader(&disk, 2).await;
    append(&mut store, (0..3).map(entry).collect())
        .await
        .await
        .unwrap()
        .unwrap();
    let resume = hold(&disk, 2).await;
    let flushed = append(&mut store, (3..6).map(entry).collect()).await;
    // The leader steps down; its successor's log conflicts after index 1.
    let mut truncating = store.clone();
    let truncation =
        tokio::spawn(async move { truncating.truncate_after(Some(entry(1).log_id)).await });
    tokio::time::sleep(Duration::from_millis(200)).await;
    assert!(
        !truncation.is_finished(),
        "the truncation waits for the append in flight"
    );
    // Released, the WAL serves its control queue before the application
    // queue. A truncation queued now would land first and leave the append
    // past a gap.
    resume.send(true).unwrap();
    flushed.await.unwrap().unwrap();
    truncation.await.unwrap().unwrap();
    assert!(disk.healthy(), "no write landed past a gap");
    assert_eq!(durable(&disk, 1), [0, 1]);
    assert_eq!(
        store.try_get_log_entries(0..6).await.unwrap(),
        (0..2).map(entry).collect::<Vec<_>>()
    );
    disk.shutdown().await.unwrap();
    // The log survives a restart as the truncation left it.
    let reopened = open(dir.path());
    assert_eq!(durable(&reopened, 1), [0, 1]);
    reopened.shutdown().await.unwrap();
}

/// A replica parked while compaction relocates its snapshot's extent: the
/// park mark must name the source segment that the selected snapshot still
/// reads, even when the pin sees the slice already at its copy. Found by
/// RelocationParkRace in verification/tla/Relocation.tla.
#[tokio::test]
async fn a_park_mark_keeps_the_selected_snapshot_during_relocation() {
    let dir = tempfile::tempdir().unwrap();
    let disk = open(dir.path());
    disk.set_write_version(crate::stream::consensus::CLUSTER_VERSION_V2);
    let mut store = leader(&disk, 1).await;
    let scope = store.stream;
    let mut log = (0..4).map(entry).collect::<Vec<_>>();
    let nodes = (1..=3u128)
        .map(|id| (id, openraft::BasicNode::new(format!("k{id}:7000"))))
        .collect::<std::collections::BTreeMap<_, _>>();
    log[0].payload = EntryPayload::Membership(
        Membership::new(vec![nodes.keys().copied().collect()], nodes).unwrap(),
    );
    log[1].payload = EntryPayload::Normal(Command::Create);
    log[2].payload = EntryPayload::Normal(Command::Seal {
        expected: Epoch(0),
        writer: Uuid::from_u128(4),
        owner: "urn:logkeeper:client:writer".into(),
    });
    let EntryPayload::Normal(Command::Append { at, .. }) = &mut log[3].payload else {
        unreachable!();
    };
    *at = Lsn(1);
    let through = log[3].log_id;
    append(&mut store, log.clone())
        .await
        .await
        .unwrap()
        .unwrap();
    store
        .state
        .apply(futures::stream::iter(
            log.into_iter().map(|entry| Ok((entry, None))),
        ))
        .await
        .unwrap();
    drop(
        store
            .state
            .get_snapshot_builder()
            .await
            .build_snapshot()
            .await
            .unwrap(),
    );
    store.purge(through).await.unwrap();
    let (source, _) = store.state.payload_path().unwrap();
    let segment = source
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .parse()
        .unwrap();

    // Roll the active WAL away from the source and publish a checkpoint
    // whose replay base is through that roll. The chosen snapshot still
    // names the original extent.
    let filler = genesis(2);
    disk.protocol(Record::Register(filler.clone()))
        .await
        .unwrap();
    disk.protocol(Record::Vote(filler.stream, Vote::new_committed(2, KEEPER)))
        .await
        .unwrap();
    for index in 0..8 {
        let mut frame = entry(index);
        let EntryPayload::Normal(Command::Append { payload, .. }) = &mut frame.payload else {
            unreachable!();
        };
        *payload = Bytes::from(vec![0; 128 * 1024]);
        disk.write(Record::Append(filler.stream, vec![frame]))
            .await
            .unwrap();
    }
    disk.checkpoint_now().await.unwrap();

    let (entered, swapped) = oneshot::channel();
    let (resume, held) = std::sync::mpsc::channel();
    disk.fail_replication_at(
        scope,
        ReplicaFault::AfterRelocationSwap {
            entered,
            resume: held,
        },
    );
    let writer = disk.clone();
    let moved = tokio::spawn(async move { writer.relocate_segment(segment, u64::MAX).await });
    tokio::time::timeout(Duration::from_secs(10), swapped)
        .await
        .unwrap()
        .unwrap();
    assert_ne!(store.state.payload_path().unwrap().0, source);

    store.state.shutdown().await;
    let pin = store.state.pin();
    pin.persist(&disk, scope).unwrap();
    resume.send(()).unwrap();
    assert!(moved.await.unwrap().unwrap() > 0);
    assert!(disk.objects.moved_segments(scope).contains(&segment));
    disk.checkpoint_now().await.unwrap();
    drop(pin);
    drop(store);
    disk.shutdown().await.unwrap();
    drop(disk);

    let reopened = open(dir.path());
    let _pin = snapshot::Pin::restore(&reopened, scope).unwrap().unwrap();
    reopened.enable_reaping();
    for _ in 0..8 {
        reopened.reap_objects().await.unwrap();
    }
    let state = StateMachine::open(&reopened, genesis(1), placement()).await;
    reopened.shutdown().await.unwrap();
    assert!(
        state.is_ok(),
        "the parked snapshot must reopen after reaping: {:?}",
        state.err()
    );
}

#[tokio::test]
async fn a_crash_before_the_leader_sync_loses_only_the_unflushed_append() {
    let dir = tempfile::tempdir().unwrap();
    let disk = open(dir.path());
    let mut store = leader(&disk, 1).await;
    append(&mut store, (0..2).map(entry).collect())
        .await
        .await
        .unwrap()
        .unwrap();
    // The leader's own write of 2..4 stalls in its round, and the keeper
    // dies before the round's boundary is published.
    let (entered, inside) = oneshot::channel();
    let (resume, held) = std::sync::mpsc::channel();
    disk.fail_replication_at(
        StreamId(1),
        ReplicaFault::Hold {
            entered,
            resume: held,
        },
    );
    let flushed = append(&mut store, (2..4).map(entry).collect()).await;
    inside.await.unwrap();
    // Replication reads the entries while the leader has not synced them.
    assert_eq!(
        store.try_get_log_entries(2..4).await.unwrap(),
        (2..4).map(entry).collect::<Vec<_>>()
    );
    let applying = store.inflight.clone();
    let apply = tokio::spawn(async move { applying.durable_through(3).await });
    resume.send(false).unwrap();
    // The leader never reports the entries durable, so OpenRaft never
    // counts it toward their commit, and applying them fails.
    assert!(flushed.await.unwrap().is_err());
    assert!(apply.await.unwrap().is_err());
    assert!(!disk.healthy());
    let _ = disk.shutdown().await;
    let reopened = open(dir.path());
    assert_eq!(durable(&reopened, 1), [0, 1]);
    reopened.shutdown().await.unwrap();
}
