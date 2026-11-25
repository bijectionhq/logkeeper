use bytes::Bytes;
use journal_contract::{Epoch, Lsn};
use openraft::EntryPayload;
use std::{
    fs::{File, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
};
use uuid::Uuid;

use super::*;
use crate::stream::consensus::{Fence, MAX_RECORD, state::Command};

fn genesis() -> Genesis {
    Genesis {
        stream: StreamId(1),
        voters: [1, 2, 3].map(Uuid::from_u128),
        quota_bytes: 64 * 1024 * 1024,
    }
}

fn entry(index: u64, payload: Bytes) -> Entry {
    Entry {
        log_id: LogId::new(openraft::CommittedLeaderId::new(2, 1), index),
        payload: EntryPayload::Normal(Command::Append {
            fence: Fence {
                epoch: Epoch(1),
                writer: Uuid::from_u128(4),
            },
            owner: "urn:logkeeper:client:writer".into(),
            at: Lsn(index + 1),
            payload,
        }),
    }
}

fn install(dir: &Path, keeper: Uuid) -> impl Fn() -> Enrollment + '_ {
    let path = dir.join("data");
    let ledger = dir.join("registry");
    fs::create_dir(&ledger).unwrap();
    let enrollment = move || Enrollment::test(path.clone(), ledger.clone(), keeper);
    enrollment().initialize().unwrap();
    enrollment
}

fn legacy(enrollment: Enrollment, records: &[Record]) -> PathBuf {
    let (media, _lock, selected) = enrollment.open().unwrap();
    let path = media.wal(selected.generation);
    let mut file = OpenOptions::new().append(true).open(&path).unwrap();
    let bytes = records
        .iter()
        .map(|record| write_record(&mut file, record).unwrap())
        .sum();
    sync_file(&file).unwrap();
    media
        .publish(
            selected.generation,
            bytes,
            super::super::media::sha256(File::open(&path).unwrap()).unwrap(),
        )
        .unwrap();
    path
}

#[tokio::test]
async fn legacy_framed_wal_migrates_a_large_batch_and_discards_unpublished_tail() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install(dir.path(), genesis.voters[0]);
    let payload = Bytes::from(vec![77; MAX_RECORD]);
    let mut records = vec![
        Record::Register(genesis),
        Record::Vote(stream, Vote::new_committed(2, 1)),
    ];
    records.extend((0..9).map(|index| Record::Append(stream, vec![entry(index, payload.clone())])));
    let old = legacy(enrollment(), &records);
    let mut tail = OpenOptions::new().append(true).open(&old).unwrap();
    tail.write_all(&100_u32.to_be_bytes()).unwrap();
    tail.write_all(&[0; 12]).unwrap();
    sync_file(&tail).unwrap();
    let restarted = Disk::open(enrollment()).unwrap();
    assert!(!old.exists());
    restarted.log(stream, |log| {
        assert_eq!(log.entries.len(), 9);
        assert_eq!(log.vote, Some(Vote::new_committed(2, 1)));
        for found in log.entries.values() {
            assert!(
                matches!(&found.payload, EntryPayload::Normal(Command::Append {
                payload: restored, ..
            }) if *restored == payload)
            );
        }
    });
    restarted.shutdown().await.unwrap();
    let (media, lock, selected) = enrollment().open().unwrap();
    drop(lock);
    OpenOptions::new()
        .write(true)
        .open(media.wal(selected.generation))
        .unwrap()
        .set_len(0)
        .unwrap();
    assert!(Disk::open(enrollment()).is_err());
}

#[tokio::test]
async fn a_detached_log_segment_is_retained_until_its_exact_last_pin() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open(enrollment()).unwrap();
    disk.protocol(Record::Register(genesis)).await.unwrap();
    disk.protocol(Record::Vote(stream, Vote::new_committed(2, 1)))
        .await
        .unwrap();
    disk.write(Record::Append(
        stream,
        vec![entry(0, Bytes::from_static(b"original"))],
    ))
    .await
    .unwrap();
    let pin = disk.log(stream, |log| log.segments[&0].clone());
    let path = pin.path().to_owned();
    disk.enable_reaping();
    disk.protocol(Record::Truncate(stream, 0)).await.unwrap();
    disk.write(Record::Append(
        stream,
        vec![entry(0, Bytes::from_static(b"replacement"))],
    ))
    .await
    .unwrap();
    disk.reap_objects().await.unwrap();
    assert!(path.exists());
    assert!(pin.read().is_ok());
    drop(pin);
    disk.reap_objects().await.unwrap();
    assert!(!path.exists());
    disk.shutdown().await.unwrap();
    let restarted = Disk::open(enrollment()).unwrap();
    restarted.log(stream, |log| {
        assert!(
            matches!(&log.entries[&0].payload, EntryPayload::Normal(Command::Append {
            payload, ..
        }) if *payload == Bytes::from_static(b"replacement"))
        );
        assert_eq!(log.vote, Some(Vote::new_committed(2, 1)));
    });
    restarted.shutdown().await.unwrap();
}

#[tokio::test]
async fn staged_install_requires_the_exact_cut_and_generation_and_keeps_the_vote() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let stage = Stage {
        stream,
        source: 12,
        old: genesis.voters,
        target: [2, 3, 4].map(Uuid::from_u128),
    };
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open(enrollment()).unwrap();
    let vote = Vote::new_committed(3, 1);
    disk.protocol(Record::Register(genesis)).await.unwrap();
    disk.protocol(Record::Vote(stream, vote)).await.unwrap();
    disk.maintenance(Record::Ownership(stream, Change::Stage(stage.clone())))
        .await
        .unwrap();
    let generation = disk.current_generation(stream).unwrap();
    let item = entry(0, Bytes::from_static(b"staged bytes"));
    let exact = item.log_id;
    let other = LogId::new(openraft::CommittedLeaderId::new(3, 1), exact.index);
    disk.write(Record::Owned(
        generation,
        Box::new(Record::Append(stream, vec![item])),
    ))
    .await
    .unwrap();
    let install_cut = |through| {
        Record::Ownership(
            stream,
            Change::Install {
                stage: stage.clone(),
                generation,
                through,
            },
        )
    };
    assert_eq!(
        disk.maintenance(install_cut(other))
            .await
            .unwrap_err()
            .kind(),
        io::ErrorKind::WouldBlock
    );
    assert!(!disk.installed(stream));
    disk.maintenance(install_cut(exact)).await.unwrap();
    assert!(disk.installed(stream));
    let next = Stage {
        source: 13,
        ..stage.clone()
    };
    disk.maintenance(Record::Ownership(stream, Change::Stage(next)))
        .await
        .unwrap();
    assert_eq!(
        disk.maintenance(install_cut(exact))
            .await
            .unwrap_err()
            .kind(),
        io::ErrorKind::WouldBlock
    );
    let late = Record::Owned(
        generation,
        Box::new(Record::Snapshot(
            stream,
            Selected {
                log_id: exact,
                digest: [1; 32],
            },
        )),
    );
    assert_eq!(
        disk.covered(late).await.unwrap_err().kind(),
        io::ErrorKind::WouldBlock
    );
    disk.shutdown().await.unwrap();
    let reopened = Disk::open(enrollment()).unwrap();
    let book = reopened.ownership(stream).unwrap();
    assert_eq!(book.high_water(), 14);
    assert!(book.generation().unwrap() > generation);
    assert!(!book.installed());
    reopened.log(stream, |log| {
        assert_eq!(log.vote, Some(vote));
        assert!(log.snapshot.is_none() && log.entries.is_empty());
    });
    reopened.shutdown().await.unwrap();
}

#[test]
fn selected_log_without_its_vote_fails_closed() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install(dir.path(), genesis.voters[0]);
    legacy(
        enrollment(),
        &[
            Record::Register(genesis),
            Record::Append(stream, vec![entry(0, Bytes::from_static(b"missing vote"))]),
        ],
    );
    assert!(Disk::open(enrollment()).is_err());
}

#[tokio::test]
async fn the_protocol_queue_remains_open_when_application_and_maintenance_queues_are_reserved() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open(enrollment()).unwrap();
    let occupied = disk.work.reserve_many(MAX_ROUND_RECORDS).await.unwrap();
    let scratch = disk
        .maintenance
        .reserve_many(MAINTENANCE_QUEUE)
        .await
        .unwrap();
    assert_eq!(disk.work.capacity(), 0);
    let vote = Vote::new(2, 1);
    tokio::time::timeout(std::time::Duration::from_secs(2), async {
        disk.protocol(Record::Register(genesis)).await.unwrap();
        disk.protocol(Record::Vote(stream, vote)).await.unwrap();
    })
    .await
    .unwrap();
    drop(occupied);
    drop(scratch);
    assert_eq!(disk.work.capacity(), MAX_ROUND_RECORDS);
    disk.shutdown().await.unwrap();
    let reopened = Disk::open(enrollment()).unwrap();
    assert_eq!(reopened.log(stream, |log| log.vote), Some(vote));
    reopened.shutdown().await.unwrap();
}

#[test]
fn a_restart_uses_the_complete_wal_index_on_either_side_of_publication() {
    for cut in [1, 2, 3, 4] {
        let dir = tempfile::tempdir().unwrap();
        let genesis = genesis();
        let stream = genesis.stream;
        let enrollment = install(dir.path(), genesis.voters[0]);
        let objects;
        let space;
        {
            let (media, _lock, boundary) = enrollment().open().unwrap();
            objects = Objects::open(media.data()).unwrap();
            space = Space::new(media.data().to_owned()).unwrap();
            let (mut indexed, mut state) =
                Indexed::open(&media, boundary, &objects, &space).unwrap();
            state
                .apply_indexed(Record::Register(genesis), &objects)
                .unwrap();
            let vote = Vote::new_committed(2, 1);
            state
                .apply_indexed(Record::Vote(stream, vote), &objects)
                .unwrap();
            state
                .apply_indexed(
                    Record::Append(stream, vec![entry(0, Bytes::from_static(b"old"))]),
                    &objects,
                )
                .unwrap();
            indexed
                .commit(&media, &objects, &state, &BTreeSet::from([stream]))
                .unwrap();
            let new = entry(1, Bytes::from_static(b"new"));
            let selected = Selected {
                log_id: new.log_id,
                digest: [7; 32],
            };
            state
                .apply_indexed(Record::Append(stream, vec![new]), &objects)
                .unwrap();
            state
                .apply_indexed(Record::Snapshot(stream, selected), &objects)
                .unwrap();
            indexed.interrupt(cut);
            assert!(
                indexed
                    .commit(&media, &objects, &state, &BTreeSet::from([stream]))
                    .is_err()
            );
        }
        let (media, _lock, boundary) = enrollment().open().unwrap();
        let (_, recovered) = Indexed::open(&media, boundary, &objects, &space).unwrap();
        assert_eq!(
            recovered.logs[&stream].entries.len(),
            if cut < 3 { 1 } else { 2 }
        );
        assert_eq!(recovered.logs[&stream].snapshot.is_some(), cut >= 3);
        assert!(recovered.logs[&stream].purged.is_none());
        assert_eq!(
            recovered.logs[&stream].vote,
            Some(Vote::new_committed(2, 1))
        );
        assert!(matches!(&recovered.logs[&stream].entries[&0].payload,
            EntryPayload::Normal(Command::Append { payload, .. }) if *payload == b"old"[..]));
    }
}

#[tokio::test]
async fn failed_follower_writes_keep_the_ticket_and_recover_the_selected_cut() {
    for (fault, survived) in [
        (ReplicaFault::PartialSegment, false),
        (ReplicaFault::FailedSync, false),
        (ReplicaFault::BeforeSelection, false),
        (ReplicaFault::AfterSelection, true),
    ] {
        let dir = tempfile::tempdir().unwrap();
        let genesis = genesis();
        let stream = genesis.stream;
        let enrollment = install(dir.path(), genesis.voters[0]);
        let disk = Disk::open(enrollment()).unwrap();
        let vote = Vote::new_committed(2, 1);
        disk.protocol(Record::Register(genesis)).await.unwrap();
        disk.protocol(Record::Vote(stream, vote)).await.unwrap();
        let entries = vec![entry(0, Bytes::from(vec![37; 32 * 1024]))];
        let record = Record::Owned(0, Box::new(Record::Append(stream, entries.clone())));
        assert!(
            disk.protocol(Record::Append(stream, entries.clone()))
                .await
                .is_err()
        );
        let ticket = disk
            .reserve_replication(stream, Uuid::new_v4(), &entries)
            .unwrap();
        let charge = disk.space.outstanding(stream);
        assert_eq!(charge.0, 1);
        assert!(charge.1 > 32 * 1024);
        let objects = disk.path.join("objects");
        let initial = fs::read_dir(&objects).unwrap().count();
        disk.fail_replication_at(stream, fault);
        assert!(disk.replicate(record, ticket).await.is_err());
        assert_eq!(disk.space.outstanding(stream), charge);
        assert!(fs::read_dir(&objects).unwrap().count() > initial);
        assert!(disk.shutdown().await.is_err());
        assert!(!disk.healthy());

        let reopened = Disk::open(enrollment()).unwrap();
        assert_eq!(reopened.space.outstanding(stream), (0, 0));
        reopened.log(stream, |log| {
            assert_eq!(log.vote, Some(vote));
            assert_eq!(log.entries.len(), usize::from(survived));
            if survived {
                assert_eq!(log.entries.get(&0), entries.first());
            }
        });
        let unreconciled = fs::read_dir(&objects).unwrap().count();
        reopened.enable_reaping();
        reopened.reap_objects().await.unwrap();
        assert!(fs::read_dir(&objects).unwrap().count() < unreconciled);
        reopened.shutdown().await.unwrap();
    }
}

#[test]
fn saturated_durable_lanes_rotate_without_overtaking_an_admitted_replica() {
    let [
        (peer_tx, peer),
        (covered_tx, reclaim),
        (replica_tx, follower),
        (app_tx, incoming),
        (bulk_tx, housekeeping),
    ] = std::array::from_fn(|_| mpsc::channel(8));
    let lanes = [peer_tx, covered_tx, replica_tx, app_tx, bulk_tx];
    let enqueue = |lane: usize, sequence: u128| {
        let (done, _) = oneshot::channel();
        lanes[lane]
            .try_send(Message::Write(Work {
                record: Record::Vote(StreamId(10 * sequence + lane as u128), Vote::default()),
                done,
                _space: None,
                follower: lane == 2,
            }))
            .ok()
            .unwrap();
    };
    for lane in 0..5 {
        enqueue(lane, 1);
        enqueue(lane, 2);
    }
    let mut queues = Queues {
        peer,
        reclaim,
        follower,
        incoming,
        housekeeping,
        next: 0,
    };
    for sequence in 1..=12 {
        for lane in 0..5 {
            let Some(Message::Write(work)) = queues.try_recv() else {
                panic!("persistent admitted lane is ready")
            };
            assert_eq!(work.record.stream(), StreamId(10 * sequence + lane as u128));
            enqueue(lane, sequence + 2);
        }
    }
}
