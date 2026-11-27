use bytes::Bytes;
use journal_contract::{Epoch, Lsn};
use openraft::EntryPayload;
use std::{
    fs::{self, File, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
};
use uuid::Uuid;

use super::*;
use crate::stream::consensus::{Fence, MAX_RECORD, state::Command, storage::objects::Reference};
use bincode::Options as _;

fn genesis() -> Genesis {
    Genesis {
        stream: StreamId(1),
        voters: [1, 2, 3].map(Uuid::from_u128),
        quota_bytes: 64 * 1024 * 1024,
    }
}

fn entry(index: u64, payload: Bytes) -> Entry {
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
            at: Lsn(index + 1),
            payload,
        }),
    }
}

fn payload_of(entry: &Entry) -> Bytes {
    match &entry.payload {
        EntryPayload::Normal(Command::Append { payload, .. }) => payload.clone(),
        _ => panic!("not an append"),
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

fn install_legacy(dir: &Path, keeper: Uuid) -> impl Fn() -> Enrollment + '_ {
    let path = dir.join("data");
    let ledger = dir.join("registry");
    fs::create_dir(&ledger).unwrap();
    let enrollment = move || Enrollment::test(path.clone(), ledger.clone(), keeper);
    enrollment().initialize_legacy().unwrap();
    enrollment
}

fn legacy(enrollment: Enrollment, records: &[Record]) -> PathBuf {
    let (media, _lock, Opened::Legacy(selected)) = enrollment.open().unwrap() else {
        panic!("legacy media")
    };
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

fn segment_files(dir: &Path) -> BTreeMap<u64, PathBuf> {
    fs::read_dir(dir.join("data").join(super::super::segment::DIRECTORY))
        .unwrap()
        .map(|item| item.unwrap().path())
        .filter_map(|path| {
            let id = super::super::segment::parse(path.file_name()?.to_str()?)?;
            Some((id, path))
        })
        .collect()
}

fn segment_bytes(dir: &Path) -> u64 {
    segment_files(dir)
        .values()
        .map(|path| fs::metadata(path).unwrap().len())
        .sum()
}

fn checkpoint_files(dir: &Path) -> Vec<PathBuf> {
    fs::read_dir(dir.join("data").join("raft-checkpoints"))
        .map(|items| items.map(|item| item.unwrap().path()).collect())
        .unwrap_or_default()
}

fn eager() -> Tuning {
    Tuning {
        segment_bytes: 1,
        checkpoint_bytes: 1,
        synchronous: true,
    }
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for item in fs::read_dir(from).unwrap() {
        let item = item.unwrap();
        let target = to.join(item.file_name());
        if item.file_type().unwrap().is_dir() {
            copy_tree(&item.path(), &target);
        } else {
            fs::copy(item.path(), target).unwrap();
        }
    }
}

async fn registered(disk: &Disk, genesis: Genesis) -> StreamId {
    let stream = genesis.stream;
    disk.protocol(Record::Register(genesis)).await.unwrap();
    disk.protocol(Record::Vote(stream, Vote::new_committed(2, 1)))
        .await
        .unwrap();
    stream
}

#[tokio::test]
async fn legacy_framed_wal_migrates_a_large_batch_and_discards_unpublished_tail() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install_legacy(dir.path(), genesis.voters[0]);
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
            assert_eq!(payload_of(found), payload);
        }
        assert!(log.segments.values().all(|object| object.key().is_none()));
    });
    restarted.shutdown().await.unwrap();
    let (_, newest) = segment_files(dir.path()).pop_last().unwrap();
    OpenOptions::new()
        .write(true)
        .open(newest)
        .unwrap()
        .set_len(0)
        .unwrap();
    assert!(Disk::open(enrollment()).is_err());
}

#[tokio::test]
async fn an_indexed_wal_written_by_the_old_code_path_migrates_once() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let keeper = genesis.voters[0];
    let enrollment = install_legacy(dir.path(), keeper);
    let entries = (0..4)
        .map(|index| entry(index, Bytes::from(format!("legacy {index}"))))
        .collect::<Vec<_>>();
    let selected = Selected {
        log_id: entries[1].log_id,
        digest: [9; 32],
    };
    {
        let (media, _lock, Opened::Legacy(boundary)) = enrollment().open().unwrap() else {
            panic!("legacy media")
        };
        let objects = Objects::open(media.data()).unwrap();
        let mut state = legacy::open(&media, boundary, &objects).unwrap();
        for record in [
            Record::Register(genesis.clone()),
            Record::Claim(genesis.clone()),
            Record::Vote(stream, Vote::new_committed(2, 1)),
            Record::Append(stream, entries.clone()),
            Record::Snapshot(stream, selected),
            Record::Purge(stream, entries[1].log_id),
        ] {
            state.apply(record).unwrap();
        }
        legacy::commit(&media, &objects, &mut state, boundary.generation).unwrap();
        // A migration that stopped before its registry commit left these.
        fs::write(enrollment().boundary_path(), [0; 1024]).unwrap();
        fs::write(
            objects
                .segment_directory()
                .join(super::super::segment::name(1)),
            b"partial",
        )
        .unwrap();
    }
    let registry = dir.path().join("registry");
    let check = |disk: &Disk, count| {
        disk.log(stream, |log| {
            assert_eq!(log.vote, Some(Vote::new_committed(2, 1)));
            assert_eq!(log.purged, Some(entries[1].log_id));
            assert_eq!(
                log.snapshot.map(|found| found.log_id),
                Some(selected.log_id)
            );
            assert_eq!(log.entries.len(), count);
            for index in 2..4 {
                assert_eq!(log.entries[&index], entries[index as usize]);
                assert!(log.segments[&index].key().is_some());
            }
        });
        assert_eq!(disk.catalog(stream).unwrap().genesis, genesis);
    };
    let disk = Disk::open(enrollment()).unwrap();
    check(&disk, 2);
    assert!(!registry.join(format!("{keeper}.wal")).exists());
    assert!(enrollment().boundary_path().exists());
    let wal_files = |data: &Path| {
        fs::read_dir(data)
            .unwrap()
            .filter(|item| {
                item.as_ref()
                    .unwrap()
                    .file_name()
                    .to_str()
                    .unwrap()
                    .ends_with(".wal")
            })
            .count()
    };
    let data = dir.path().join("data");
    assert_eq!(wal_files(&data), 0);
    disk.write(Record::Append(
        stream,
        vec![entry(4, Bytes::from_static(b"segmented"))],
    ))
    .await
    .unwrap();
    disk.shutdown().await.unwrap();

    // The registry committed the migration but the data volume still says
    // the old format.
    let keeper_file = data.join("KEEPER");
    let installed = fs::read_to_string(&keeper_file).unwrap();
    assert!(installed.contains("logkeeper-raft-3"));
    fs::write(
        &keeper_file,
        installed.replace("logkeeper-raft-3", "logkeeper-raft-2"),
    )
    .unwrap();
    fs::write(data.join(format!("raft-{}.wal", Uuid::new_v4())), b"stale").unwrap();
    let reopened = Disk::open(enrollment()).unwrap();
    check(&reopened, 3);
    reopened.log(stream, |log| {
        assert_eq!(payload_of(&log.entries[&4]), &b"segmented"[..]);
        assert!(log.segments[&4].key().is_none());
    });
    assert!(
        fs::read_to_string(&keeper_file)
            .unwrap()
            .contains("logkeeper-raft-3")
    );
    assert_eq!(wal_files(&data), 0);
    reopened.shutdown().await.unwrap();
}

#[tokio::test]
async fn a_detached_log_segment_is_retained_until_its_exact_last_pin() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open_tuned(enrollment(), eager()).unwrap();
    let stream = registered(&disk, genesis).await;
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
    assert_ne!(
        disk.log(stream, |log| log.segments[&0].path().to_owned()),
        path
    );
    disk.reap_objects().await.unwrap();
    assert!(path.exists());
    assert!(pin.read().is_ok());
    drop(pin);
    disk.reap_objects().await.unwrap();
    assert!(!path.exists());
    disk.shutdown().await.unwrap();
    let restarted = Disk::open(enrollment()).unwrap();
    restarted.log(stream, |log| {
        assert_eq!(payload_of(&log.entries[&0]), &b"replacement"[..]);
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
    let other = LogId::new(
        openraft::vote::leader_id_std::CommittedLeaderId::new(3),
        exact.index,
    );
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
    let enrollment = install_legacy(dir.path(), genesis.voters[0]);
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
fn a_restart_recovers_the_published_side_of_every_crash_point() {
    // 2: after the data sync, before the boundary. 3: after the boundary.
    // 5: failed data sync. 6: torn frame. A rolled round also leaves a
    // segment no boundary names.
    for roll in [false, true] {
        for cut in [2, 3, 5, 6] {
            let dir = tempfile::tempdir().unwrap();
            let genesis = genesis();
            let stream = genesis.stream;
            let enrollment = install(dir.path(), genesis.voters[0]);
            let tuning = Tuning {
                segment_bytes: if roll { 1 } else { u64::MAX },
                ..Tuning::default()
            };
            let objects;
            let space;
            let scopes = BTreeSet::from([stream]);
            {
                let (media, _lock, _) = enrollment().open().unwrap();
                objects = Objects::open(media.data()).unwrap();
                space = Space::new(media.data().to_owned()).unwrap();
                let (mut wal, mut state) = Segmented::open(&media, &objects, tuning).unwrap();
                for record in [
                    Record::Register(genesis),
                    Record::Vote(stream, Vote::new_committed(2, 1)),
                    Record::Append(stream, vec![entry(0, Bytes::from_static(b"old"))]),
                ] {
                    state.apply_indexed(record, &mut wal, &objects).unwrap();
                }
                wal.commit(&objects, &scopes).unwrap();
                let new = entry(1, Bytes::from_static(b"new"));
                let selected = Selected {
                    log_id: new.log_id,
                    digest: [7; 32],
                };
                state
                    .apply_indexed(Record::Append(stream, vec![new]), &mut wal, &objects)
                    .unwrap();
                state
                    .apply_indexed(Record::Snapshot(stream, selected), &mut wal, &objects)
                    .unwrap();
                wal.interrupt(cut);
                assert!(wal.commit(&objects, &scopes).is_err());
            }
            let (media, _lock, _) = enrollment().open().unwrap();
            let (wal, recovered) = Segmented::open(&media, &objects, tuning).unwrap();
            let survived = cut == 3;
            let log = &recovered.logs[&stream];
            assert_eq!(log.entries.len(), if survived { 2 } else { 1 });
            assert_eq!(log.snapshot.is_some(), survived);
            assert!(log.purged.is_none());
            assert_eq!(log.vote, Some(Vote::new_committed(2, 1)));
            assert_eq!(payload_of(&log.entries[&0]), &b"old"[..]);
            let position = wal.position();
            let (last, path) = segment_files(dir.path()).pop_last().unwrap();
            assert_eq!(last, position.segment);
            assert_eq!(fs::metadata(path).unwrap().len(), position.offset);
            drop(space);
        }
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
        let initial = segment_bytes(dir.path());
        disk.fail_replication_at(stream, fault);
        assert!(disk.replicate(record, ticket).await.is_err());
        assert_eq!(disk.space.outstanding(stream), charge);
        assert!(segment_bytes(dir.path()) > initial);
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
        // An unacknowledged tail is cut back to the trusted boundary.
        assert_eq!(segment_bytes(dir.path()) > initial, survived);
        reopened.shutdown().await.unwrap();
    }
}

#[tokio::test]
async fn a_torn_tail_past_the_boundary_is_truncated_on_open() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open(enrollment()).unwrap();
    let stream = registered(&disk, genesis).await;
    disk.write(Record::Append(
        stream,
        vec![entry(0, Bytes::from_static(b"kept"))],
    ))
    .await
    .unwrap();
    disk.shutdown().await.unwrap();
    let (_, active) = segment_files(dir.path()).pop_last().unwrap();
    let published = fs::metadata(&active).unwrap().len();
    let mut tail = OpenOptions::new().append(true).open(&active).unwrap();
    // A whole frame the boundary never named, then a torn one.
    let body = b"never acknowledged";
    tail.write_all(&(body.len() as u32).to_le_bytes()).unwrap();
    tail.write_all(&crc32fast::hash(body).to_le_bytes())
        .unwrap();
    tail.write_all(body).unwrap();
    tail.write_all(&64_u32.to_le_bytes()).unwrap();
    tail.write_all(&[1; 13]).unwrap();
    drop(tail);

    let reopened = Disk::open(enrollment()).unwrap();
    assert_eq!(fs::metadata(&active).unwrap().len(), published);
    reopened
        .write(Record::Append(
            stream,
            vec![entry(1, Bytes::from_static(b"after"))],
        ))
        .await
        .unwrap();
    reopened.shutdown().await.unwrap();
    let again = Disk::open(enrollment()).unwrap();
    again.log(stream, |log| {
        assert_eq!(payload_of(&log.entries[&0]), &b"kept"[..]);
        assert_eq!(payload_of(&log.entries[&1]), &b"after"[..]);
    });
    again.shutdown().await.unwrap();
}

#[tokio::test]
async fn a_data_volume_that_lost_acknowledged_writes_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open(enrollment()).unwrap();
    let stream = registered(&disk, genesis).await;
    disk.write(Record::Append(
        stream,
        vec![entry(0, Bytes::from_static(b"first"))],
    ))
    .await
    .unwrap();
    disk.shutdown().await.unwrap();
    let data = dir.path().join("data");
    let older = dir.path().join("older");
    copy_tree(&data, &older);
    let disk = Disk::open(enrollment()).unwrap();
    disk.write(Record::Append(
        stream,
        vec![entry(1, Bytes::from_static(b"second"))],
    ))
    .await
    .unwrap();
    disk.shutdown().await.unwrap();
    let intact = dir.path().join("intact");
    copy_tree(&data, &intact);
    let restore = |from: &Path| {
        fs::remove_dir_all(&data).unwrap();
        copy_tree(from, &data);
    };
    let (_, active) = segment_files(dir.path()).pop_last().unwrap();
    let len = fs::metadata(&active).unwrap().len();

    // The last acknowledged frame is missing.
    OpenOptions::new()
        .write(true)
        .open(&active)
        .unwrap()
        .set_len(len - 1)
        .unwrap();
    assert!(Disk::open(enrollment()).is_err());

    // A byte of an acknowledged frame changed.
    restore(&intact);
    let mut bytes = fs::read(&active).unwrap();
    bytes[len as usize - 3] ^= 1;
    fs::write(&active, bytes).unwrap();
    assert!(Disk::open(enrollment()).is_err());

    // The whole volume went back to an earlier consistent state.
    restore(&older);
    assert!(Disk::open(enrollment()).is_err());

    // The segment itself is gone.
    restore(&intact);
    fs::remove_file(&active).unwrap();
    assert!(Disk::open(enrollment()).is_err());

    restore(&intact);
    let reopened = Disk::open(enrollment()).unwrap();
    reopened.log(stream, |log| assert_eq!(log.entries.len(), 2));
    reopened.shutdown().await.unwrap();
}

#[tokio::test]
async fn purged_and_truncated_segments_are_deleted_and_stay_deleted() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open_tuned(enrollment(), eager()).unwrap();
    let stream = registered(&disk, genesis).await;
    let mut held = BTreeMap::new();
    for index in 0..6 {
        disk.write(Record::Append(
            stream,
            vec![entry(index, Bytes::from(vec![index as u8; 1024]))],
        ))
        .await
        .unwrap();
        let path = disk.log(stream, |log| log.segments[&index].path().to_owned());
        held.insert(index, path);
    }
    // Every round rolls, so each entry sits in a segment of its own.
    assert_eq!(held.values().collect::<BTreeSet<_>>().len(), held.len());
    let removed = fs::read(&held[&0]).unwrap();
    let cut = disk.log(stream, |log| log.entries[&3].log_id);
    disk.protocol(Record::Snapshot(
        stream,
        Selected {
            log_id: cut,
            digest: [3; 32],
        },
    ))
    .await
    .unwrap();
    disk.covered(Record::Purge(stream, cut)).await.unwrap();
    disk.protocol(Record::Truncate(stream, 5)).await.unwrap();
    disk.enable_reaping();
    disk.reap_objects().await.unwrap();
    for (index, path) in &held {
        assert_eq!(path.exists(), *index == 4, "entry {index}");
    }
    disk.shutdown().await.unwrap();

    // An unlink that did not survive a crash is repeated.
    fs::write(&held[&0], removed).unwrap();
    let reopened = Disk::open(enrollment()).unwrap();
    reopened.log(stream, |log| {
        assert_eq!(log.purged, Some(cut));
        assert_eq!(log.entries.keys().copied().collect::<Vec<_>>(), [4]);
        assert_eq!(payload_of(&log.entries[&4]), vec![4; 1024]);
    });
    reopened.enable_reaping();
    reopened.reap_objects().await.unwrap();
    assert!(!held[&0].exists());
    assert!(held[&4].exists());
    reopened.shutdown().await.unwrap();
}

#[test]
fn recovery_restores_the_checkpoint_and_replays_the_frames_after_it() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let stream = genesis.stream;
    let enrollment = install(dir.path(), genesis.voters[0]);
    let tuning = Tuning {
        checkpoint_bytes: u64::MAX,
        ..Tuning::default()
    };
    let scopes = BTreeSet::from([stream]);
    let objects;
    let space;
    let checkpoint;
    {
        let (media, _lock, _) = enrollment().open().unwrap();
        objects = Objects::open(media.data()).unwrap();
        space = Space::new(media.data().to_owned()).unwrap();
        let (mut wal, mut state) = Segmented::open(&media, &objects, tuning).unwrap();
        for record in [
            Record::Register(genesis.clone()),
            Record::Vote(stream, Vote::new_committed(2, 1)),
            Record::Append(stream, vec![entry(0, Bytes::from_static(b"before"))]),
        ] {
            state.apply_indexed(record, &mut wal, &objects).unwrap();
        }
        wal.commit(&objects, &scopes).unwrap();
        wal.checkpoint_now(&state, &objects, &space).unwrap();
        checkpoint = checkpoint_files(dir.path());
        assert_eq!(checkpoint.len(), 1);
        for record in [
            Record::Append(stream, vec![entry(1, Bytes::from_static(b"after"))]),
            Record::Vote(stream, Vote::new_committed(3, 1)),
            Record::Truncate(stream, 1),
            Record::Append(stream, vec![entry(1, Bytes::from_static(b"replaced"))]),
        ] {
            state.apply_indexed(record, &mut wal, &objects).unwrap();
            wal.commit(&objects, &scopes).unwrap();
        }
        // A checkpoint that crashed before its boundary published it.
        fs::write(
            checkpoint[0].with_file_name(format!("{}.ckpt", Uuid::new_v4())),
            b"LKRWAL04 torn",
        )
        .unwrap();
    }
    let (media, _lock, _) = enrollment().open().unwrap();
    let (wal, recovered) = Segmented::open(&media, &objects, tuning).unwrap();
    assert!(
        wal.replayed() > 0,
        "frames after the checkpoint were replayed"
    );
    assert_eq!(checkpoint_files(dir.path()), checkpoint);
    let log = &recovered.logs[&stream];
    assert_eq!(log.vote, Some(Vote::new_committed(3, 1)));
    assert_eq!(payload_of(&log.entries[&0]), &b"before"[..]);
    assert_eq!(payload_of(&log.entries[&1]), &b"replaced"[..]);
    assert_eq!(recovered.catalog.len(), 0);
    drop((wal, _lock));

    // The checkpoint the boundary names is part of the trusted state.
    fs::remove_file(&checkpoint[0]).unwrap();
    let (media, _lock, _) = enrollment().open().unwrap();
    assert!(Segmented::open(&media, &objects, tuning).is_err());
    drop(space);
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
                record: Record::Vote(StreamId(10 * sequence + lane as u128), Vote::new(0, 1)),
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

#[tokio::test]
async fn each_segment_counts_the_exact_bytes_its_live_slices_hold() {
    let dir = tempfile::tempdir().unwrap();
    let genesis = genesis();
    let enrollment = install(dir.path(), genesis.voters[0]);
    let disk = Disk::open_tuned(enrollment(), eager()).unwrap();
    let stream = registered(&disk, genesis).await;
    let mut slices = Vec::new();
    for index in 0..4 {
        let entry = entry(index, Bytes::from(vec![index as u8; 1000 + index as usize]));
        let len = crate::stream::consensus::options()
            .serialized_size(&entry)
            .unwrap();
        disk.write(Record::Append(stream, vec![entry]))
            .await
            .unwrap();
        let slice = disk.log(stream, |log| log.segments[&index].clone());
        let Reference::Segment(location) = slice.reference() else {
            panic!("segment slice");
        };
        assert_eq!(location.len, len);
        assert_eq!(disk.objects.live_bytes(location.segment), len);
        // A second holder of the same bytes shares the slice.
        let again = disk.objects.slice(location).unwrap();
        assert!(Arc::ptr_eq(&again, &slice));
        assert_eq!(disk.objects.live_bytes(location.segment), len);
        slices.push(location);
    }
    let usage = disk.segment_usage();
    assert!(usage.buckets.iter().sum::<u32>() >= 3, "{usage}");
    let cut = disk.log(stream, |log| log.entries[&1].log_id);
    disk.protocol(Record::Snapshot(
        stream,
        Selected {
            log_id: cut,
            digest: [1; 32],
        },
    ))
    .await
    .unwrap();
    disk.covered(Record::Purge(stream, cut)).await.unwrap();
    assert_eq!(disk.objects.live_bytes(slices[0].segment), 0);
    assert_eq!(disk.objects.live_bytes(slices[1].segment), 0);
    assert_eq!(disk.objects.live_bytes(slices[2].segment), slices[2].len);
    disk.shutdown().await.unwrap();
}
