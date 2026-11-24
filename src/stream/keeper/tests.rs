use std::{fs, fs::OpenOptions, io::Write, path::PathBuf};

use bytes::Buf;
use futures::poll;
use journal_contract::BoxFuture;
use tempfile::{TempDir, tempdir};
use tokio::sync::Notify;

use super::*;

const A: StreamId = StreamId(10);
const B: StreamId = StreamId(20);
const MEMBERS: [KeeperId; 3] = [KeeperId(1), KeeperId(2), KeeperId(3)];
static CLIENT: Identity = Identity::from_static("urn:logkeeper:client:writer-a");
static OTHER: Identity = Identity::from_static("urn:logkeeper:client:writer-b");

fn create(stream: StreamId) -> Request {
    Request::Create {
        stream,
        ensemble: MEMBERS,
    }
}
fn seal(stream: StreamId, epoch: u64) -> Request {
    seal_at(stream, epoch, MEMBERS)
}
fn seal_at(stream: StreamId, epoch: u64, ensemble: [KeeperId; 3]) -> Request {
    Request::Seal {
        stream,
        epoch: Epoch(epoch),
        ensemble,
    }
}
fn delete(stream: StreamId) -> Request {
    Request::Delete {
        stream,
        ensemble: MEMBERS,
    }
}
fn sync(
    stream: StreamId,
    epoch: u64,
    from: u64,
    records: &[&'static [u8]],
    head: u64,
    complete: bool,
) -> Request {
    let runs = if records.is_empty() {
        Vec::new()
    } else {
        vec![EpochRun {
            epoch: Epoch(epoch),
            first: Lsn(from),
            last: Lsn(from + records.len() as u64 - 1),
        }]
    };
    Request::Sync {
        stream,
        epoch: Epoch(epoch),
        floor: Lsn(1),
        from: Lsn(from),
        records: records
            .iter()
            .map(|record| Bytes::from_static(record))
            .collect(),
        runs,
        head: Lsn(head),
        complete,
    }
}
fn append(stream: StreamId, epoch: u64, at: u64, records: &[&'static [u8]], head: u64) -> Request {
    Request::Append {
        stream,
        epoch: Epoch(epoch),
        at: Lsn(at),
        head: Lsn(head),
        records: records
            .iter()
            .map(|record| Bytes::from_static(record))
            .collect(),
    }
}
fn trim(stream: StreamId, epoch: u64, through: u64) -> Request {
    Request::Trim {
        stream,
        epoch: Epoch(epoch),
        through: Lsn(through),
    }
}
fn check(stream: StreamId) -> Request {
    Request::Check {
        stream,
        epoch: Epoch(99),
    }
}
fn read(stream: StreamId, from: u64) -> Request {
    Request::Read {
        stream,
        from: Lsn(from),
        max: 100,
        wait_ms: 0,
    }
}
fn recover(stream: StreamId, epoch: u64, from: u64) -> Request {
    Request::Recover {
        stream,
        epoch: Epoch(epoch),
        from: Lsn(from),
        max: 100,
    }
}
fn page(floor: u64, head: u64, records: &[(u64, &'static [u8])]) -> Reply {
    Reply::Records {
        floor: Lsn(floor),
        head: Lsn(head),
        records: records
            .iter()
            .map(|(lsn, record)| (Lsn(*lsn), Bytes::from_static(record)))
            .collect(),
    }
}

fn work(identity: &Identity, request: Request) -> (Work, oneshot::Receiver<Response>) {
    let (done, result) = oneshot::channel();
    (
        Work {
            request,
            identity: identity.clone(),
            done,
            pending: None,
        },
        result,
    )
}

struct Harness {
    engine: Engine,
    dir: TempDir,
}

impl Harness {
    fn new(limits: Limits) -> Self {
        let dir = tempdir().unwrap();
        let engine = Engine::open(dir.path(), MEMBERS[0], limits, Arc::new(Allow)).unwrap();
        Self { engine, dir }
    }

    fn batch(&mut self, requests: impl IntoIterator<Item = Request>) -> Vec<Reply> {
        let (pending, results): (VecDeque<_>, Vec<_>) = requests
            .into_iter()
            .map(|request| work(&CLIENT, request))
            .unzip();
        self.engine.process(pending).unwrap();
        results
            .into_iter()
            .map(|mut result| result.try_recv().unwrap().0.unwrap())
            .collect()
    }

    fn send(&mut self, request: Request) -> Reply {
        self.batch([request]).pop().unwrap()
    }

    fn writer(&mut self, stream: StreamId) {
        self.batch([
            create(stream),
            seal(stream, 1),
            sync(stream, 1, 1, &[], 0, true),
        ]);
    }

    fn segment(&self) -> PathBuf {
        let entries: Vec<_> = fs::read_dir(self.dir.path().join("segments"))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(entries.len(), 1);
        entries[0].clone()
    }
}

#[test]
fn create_is_durable_and_idempotent() {
    let mut test = Harness::new(Limits::default());
    assert_eq!(test.send(check(A)), Reply::Refused(Refusal::NotFound));
    assert_eq!(test.send(create(A)), Reply::Created);
    let rounds = test.engine.wal.rounds.len();
    assert_eq!(test.send(create(A)), Reply::Created);
    assert_eq!(test.engine.wal.rounds.len(), rounds);
    let Reply::Checked(view) = test.send(check(A)) else {
        panic!("missing stream")
    };
    assert_eq!(
        (
            view.promised,
            view.synced,
            view.tail,
            view.head,
            view.floor,
            view.learner
        ),
        (None, None, Lsn(0), Lsn(0), Lsn(1), false)
    );
    assert_eq!(
        test.send(Request::Create {
            stream: B,
            ensemble: [MEMBERS[0]; 3]
        }),
        Reply::Refused(Refusal::Unauthorized)
    );
}

#[test]
fn seal_fences_lower_epochs_and_equal_epochs_from_other_identities() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"accepted"], 0));
    let accepted = test.send(seal(A, 2));
    let Reply::Sealed(view) = &accepted else {
        panic!("missing seal")
    };
    assert_eq!(
        view.runs,
        [EpochRun {
            epoch: Epoch(1),
            first: Lsn(1),
            last: Lsn(1)
        }]
    );
    assert_eq!(
        (view.tail, view.head, view.synced),
        (Lsn(1), Lsn(0), Some(Epoch(1)))
    );
    let synced_rounds = test.engine.wal.rounds.len();
    assert_eq!(test.send(seal(A, 2)), accepted);
    let fenced = Reply::Refused(Refusal::Fenced { promised: Epoch(2) });
    assert_eq!(test.send(seal(A, 1)), fenced);
    let (work, mut result) = work(&OTHER, seal(A, 2));
    test.engine.process(VecDeque::from([work])).unwrap();
    assert_eq!(result.try_recv().unwrap().0.unwrap(), fenced);
    assert_eq!(test.engine.wal.rounds.len(), synced_rounds);
}

#[test]
fn sync_preserves_head_and_completes_explicitly() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"committed", b"tail"], 1));
    test.send(seal(A, 2));
    assert_eq!(
        test.send(sync(A, 1, 2, &[], 1, true)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(2) })
    );
    assert_eq!(
        test.send(sync(A, 2, 1, &[b"wrong"], 1, true)),
        Reply::Refused(Refusal::Conflict { head: Lsn(1) })
    );
    assert_eq!(
        test.send(sync(A, 2, 1, &[], 0, true)),
        Reply::Refused(Refusal::AboveHead { head: Lsn(1) })
    );
    assert_eq!(
        test.send(sync(A, 2, 4, &[], 1, true)),
        Reply::Refused(Refusal::Gap { head: Lsn(1) })
    );
    assert_eq!(
        test.send(sync(A, 2, 2, &[b"replacement"], 1, false)),
        Reply::Synced { tail: Lsn(2) }
    );
    assert_eq!(
        test.send(append(A, 2, 3, &[b"early"], 1)),
        Reply::Refused(Refusal::NotSynced)
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[], 1, true)),
        Reply::Synced { tail: Lsn(2) }
    );
    assert_eq!(
        test.send(append(A, 2, 3, &[b"new"], 1)),
        Reply::Appended { tail: Lsn(3) }
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[], 1, true)),
        Reply::Synced { tail: Lsn(3) }
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[], 1, false)),
        Reply::Refused(Refusal::Conflict { head: Lsn(1) })
    );
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"replacement"), (3, b"new")])
    );
}

#[test]
fn append_requires_current_sync_next_position_or_an_identical_retry() {
    let mut test = Harness::new(Limits {
        stream_quota_bytes: 4,
        max_record_bytes: 3,
        ..Limits::default()
    });
    test.writer(A);
    assert_eq!(
        test.send(append(A, 0, 1, &[b"a"], 0)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) })
    );
    let (job, mut result) = work(&OTHER, append(A, 1, 1, &[b"a"], 0));
    test.engine.process(VecDeque::from([job])).unwrap();
    assert_eq!(
        result.try_recv().unwrap().0.unwrap(),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) })
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[b"a"], 0)),
        Reply::Refused(Refusal::Gap { head: Lsn(0) })
    );
    assert_eq!(
        test.send(append(A, 1, 1, &[b"long"], 0)),
        Reply::Refused(Refusal::TooLarge { max: 3 })
    );
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abc"], 2)),
        Reply::Refused(Refusal::AboveHead { head: Lsn(0) })
    );
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abc"], 0)),
        Reply::Appended { tail: Lsn(1) }
    );
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abc"], 1)),
        Reply::Appended { tail: Lsn(1) }
    );
    let rounds = test.engine.wal.rounds.len();
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abc"], 0)),
        Reply::Appended { tail: Lsn(1) }
    );
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abd"], 0)),
        Reply::Refused(Refusal::Conflict { head: Lsn(1) })
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[b"ab"], 1)),
        Reply::Refused(Refusal::Full { floor: Lsn(1) })
    );
    assert_eq!(test.engine.wal.rounds.len(), rounds);
}

#[test]
fn commit_only_append_preserves_a_later_accepted_record() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"first", b"later"], 0));
    assert_eq!(
        test.send(append(A, 1, 2, &[], 1)),
        Reply::Appended { tail: Lsn(2) },
        "head publication inside the accepted prefix"
    );
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"first")]));
    assert_eq!(
        test.send(recover(A, 1, 1)),
        page(1, 1, &[(1, b"first"), (2, b"later")])
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[], 3)),
        Reply::Refused(Refusal::AboveHead { head: Lsn(1) })
    );
}

#[test]
fn synced_floor_catch_up_preserves_the_retained_suffix() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"retired", b"committed", b"accepted"], 2));
    let floor = |epoch| Request::Sync {
        stream: A,
        epoch: Epoch(epoch),
        floor: Lsn(2),
        from: Lsn(2),
        records: vec![],
        runs: vec![],
        head: Lsn(1),
        complete: false,
    };
    assert_eq!(
        test.send(floor(0)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) }),
        "floor catch-up requires the current promise"
    );
    assert_eq!(
        test.send(floor(1)),
        Reply::Synced { tail: Lsn(3) },
        "floor catch-up preserves accepted tail"
    );
    assert_eq!(
        test.send(recover(A, 1, 2)),
        page(2, 2, &[(2, b"committed"), (3, b"accepted")])
    );
    let Harness { engine, dir } = test;
    drop(engine);
    let engine = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let mut test = Harness { engine, dir };
    assert_eq!(
        test.send(recover(A, 1, 2)),
        page(2, 2, &[(2, b"committed"), (3, b"accepted")]),
        "floor catch-up survives WAL replay"
    );
}

#[test]
fn trim_is_monotone_committed_and_frees_quota() {
    let mut test = Harness::new(Limits {
        stream_quota_bytes: 1,
        ..Limits::default()
    });
    test.writer(A);
    test.send(append(A, 1, 1, &[b"x"], 0));
    assert_eq!(
        test.send(trim(A, 2, 1)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) })
    );
    assert_eq!(
        test.send(trim(A, 1, 1)),
        Reply::Refused(Refusal::AboveHead { head: Lsn(0) })
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[], 1)),
        Reply::Appended { tail: Lsn(1) }
    );
    assert_eq!(test.send(trim(A, 1, 1)), Reply::Trimmed { floor: Lsn(2) });
    assert_eq!(test.send(trim(A, 1, 0)), Reply::Trimmed { floor: Lsn(2) });
    assert_eq!(
        test.send(append(A, 1, 1, &[b"x"], 1)),
        Reply::Refused(Refusal::BelowFloor { floor: Lsn(2) })
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[b"y"], 2)),
        Reply::Appended { tail: Lsn(2) }
    );
    assert_eq!(test.send(read(A, 2)), page(2, 2, &[(2, b"y")]));
}

#[test]
fn check_reports_the_durable_view_without_writing() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"committed", b"accepted"], 1));
    let rounds = test.engine.wal.rounds.len();
    let Reply::Checked(view) = test.send(check(A)) else {
        panic!("missing check")
    };
    assert_eq!(
        (view.promised, view.synced, view.tail, view.head),
        (
            Some((Epoch(1), CLIENT.clone())),
            Some(Epoch(1)),
            Lsn(2),
            Lsn(1)
        )
    );
    assert_eq!(test.engine.wal.rounds.len(), rounds);
}

#[test]
fn read_stops_at_head_and_recover_requires_the_writer() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"committed", b"accepted"], 1));
    let rounds = test.engine.wal.rounds.len();
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"committed")]));
    assert_eq!(
        test.send(recover(A, 1, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"accepted")])
    );
    assert_eq!(
        test.send(recover(A, 0, 1)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) })
    );
    test.send(trim(A, 1, 1));
    assert_eq!(
        test.send(read(A, 1)),
        Reply::Refused(Refusal::BelowFloor { floor: Lsn(2) })
    );
    assert_eq!(test.send(read(A, 2)), page(2, 1, &[]));
    assert_eq!(test.engine.wal.rounds.len(), rounds + 1);
}

#[test]
fn delete_rotates_and_removes_only_its_payloads() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"keep"], 1),
        append(B, 1, 1, &[b"remove"], 1),
    ]);
    test.engine.wal.rotate(&mut test.engine.streams).unwrap();
    let a = test
        .dir
        .path()
        .join("streams")
        .join(format!("{:032x}", A.0));
    let b = test
        .dir
        .path()
        .join("streams")
        .join(format!("{:032x}", B.0));
    let checkpoint = fs::read(a.join("state")).unwrap();
    let segment = test.segment();
    assert_eq!(test.send(delete(B)), Reply::Deleted);
    assert_ne!(test.segment(), segment, "delete must rotate");
    assert!(!segment.exists(), "old shared segment still exists");
    assert_eq!(
        fs::read(a.join("state")).unwrap(),
        checkpoint,
        "untouched stream was checkpointed"
    );
    assert_eq!(
        fs::read_dir(b).unwrap().count(),
        1,
        "deleted stream kept an extent"
    );
    assert_eq!(test.send(create(B)), Reply::Refused(Refusal::Deleted));
    assert_eq!(test.send(delete(B)), Reply::Deleted);
    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    assert_eq!(reopened.send(check(B)), Reply::Refused(Refusal::Deleted));
    assert_eq!(reopened.send(read(A, 1)), page(1, 1, &[(1, b"keep")]));
}

#[test]
fn create_after_delete_of_an_absent_stream_is_refused() {
    let mut test = Harness::new(Limits::default());
    assert_eq!(test.send(delete(A)), Reply::Deleted);
    assert_eq!(test.send(create(A)), Reply::Refused(Refusal::Deleted));
}

#[test]
fn group_commit_covers_multiple_streams_in_one_sync() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    let rounds = test.engine.wal.rounds.len();
    assert_eq!(
        test.batch([
            append(A, 1, 1, &[b"a"], 1),
            append(B, 1, 1, &[b"b"], 1),
            check(A)
        ]),
        [
            Reply::Appended { tail: Lsn(1) },
            Reply::Appended { tail: Lsn(1) },
            Reply::Checked(test.engine.streams[&A].view.clone())
        ]
    );
    assert_eq!(
        test.engine.wal.rounds.len() - rounds,
        1,
        "two streams must share one covering sync"
    );
}

#[test]
fn sync_failure_publishes_neither_the_ack_nor_a_read_of_staged_data() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    let (pending, results): (VecDeque<_>, Vec<_>) = [
        append(A, 1, 1, &[b"a"], 1),
        append(B, 1, 1, &[b"b"], 1),
        read(A, 1),
    ]
    .into_iter()
    .map(|request| work(&CLIENT, request))
    .unzip();
    test.engine.wal.fail_sync = true;
    assert!(test.engine.process(pending).is_err());
    for mut result in results {
        assert!(
            matches!(result.try_recv(), Err(oneshot::error::TryRecvError::Closed)),
            "reply escaped a failed sync"
        );
    }
}

#[test]
fn round_cap_is_enforced_even_for_a_record_larger_than_the_cap() {
    let cap = 128;
    let large = vec![2; 512];
    let mut test = Harness::new(Limits {
        round_bytes_per_stream: cap,
        ..Limits::default()
    });
    test.writer(A);
    test.writer(B);
    let baseline = test.engine.wal.rounds.len();
    let mut request = append(A, 1, 1, &[], 1);
    if let Request::Append { records, .. } = &mut request {
        records.push(Bytes::from(large));
    }
    assert_eq!(
        test.batch([request, append(B, 1, 1, &[b"small"], 1)]),
        [
            Reply::Appended { tail: Lsn(1) },
            Reply::Appended { tail: Lsn(1) }
        ]
    );
    let file = fs::read(test.segment()).unwrap();
    let mut rounds = file.as_slice();
    for (index, &round_bytes) in test.engine.wal.rounds.iter().enumerate() {
        let (mut round, rest) = rounds.split_at(round_bytes);
        rounds = rest;
        let mut used = HashMap::<StreamId, usize>::new();
        while round.has_remaining() {
            let len = round.get_u32() as usize;
            round.advance(4);
            let (mut body, rest) = round.split_at(len);
            round = rest;
            *used.entry(StreamId(body.get_u128())).or_default() += len + 8;
        }
        assert!(
            used.values().all(|&bytes| bytes <= cap),
            "a stream exceeded its byte cap"
        );
        if index == baseline {
            assert_eq!(
                used.len(),
                2,
                "small stream must advance alongside a fragmented request"
            );
        }
    }
    assert!(test.engine.wal.rounds.len() > baseline + 1);
}

#[test]
fn recovery_cuts_interleaved_torn_tail_and_keeps_the_other_stream() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([append(A, 1, 1, &[b"a1"], 1), append(B, 1, 1, &[b"b1"], 1)]);
    let segment = test.segment();
    let a = wal::entry(&append(A, 1, 2, &[b"a2"], 2), None).unwrap();
    let b = wal::entry(&append(B, 1, 2, &[b"b2"], 2), None).unwrap();
    let mut tail = BytesMut::new();
    wal::fragment(&mut tail, A, true, false, &a[..30]);
    wal::fragment(&mut tail, B, true, true, &b);
    let last = tail.len();
    wal::fragment(&mut tail, A, false, true, &a[30..]);
    // Damage the checksum so this specifically exercises the CRC guard.
    tail[last + 4] ^= 1;
    OpenOptions::new()
        .append(true)
        .open(&segment)
        .unwrap()
        .write_all(&tail)
        .unwrap();

    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    assert_eq!(
        reopened.send(read(A, 1)),
        page(1, 1, &[(1, b"a1")]),
        "torn record was replayed"
    );
    assert_eq!(
        reopened.send(read(B, 1)),
        page(1, 2, &[(1, b"b1"), (2, b"b2")]),
        "other stream lost a whole record"
    );
    assert!(!segment.exists());
}

#[test]
fn recovery_refuses_damage_before_the_last_segment() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    let segment = test.segment();
    OpenOptions::new()
        .append(true)
        .open(&segment)
        .unwrap()
        .write_all(b"short")
        .unwrap();
    fs::File::create(segment.with_file_name("00000000000000000001.seg")).unwrap();
    let Harness { engine, dir } = test;
    drop(engine);
    let error = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow))
        .err()
        .expect("middle segment damage was accepted");
    assert_eq!(error.to_string(), "damaged frame before keeper WAL tail");
}

#[test]
fn existing_keeper_directory_rejects_identity_change_and_missing_wal() {
    let test = Harness::new(Limits::default());
    let segment = test.segment();
    let Harness { engine, dir } = test;
    drop(engine);
    assert!(Engine::open(dir.path(), MEMBERS[1], Limits::default(), Arc::new(Allow)).is_err());
    fs::remove_file(segment).unwrap();
    assert!(Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).is_err());
}

#[tokio::test(start_paused = true)]
async fn read_waits_for_commit_and_times_out_at_the_end() {
    const WAIT_MS: u32 = 100;
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"x"], 0));
    let (work, mut incoming) = mpsc::channel(1);
    let keeper = Keeper { work };
    let process_read = |test: &mut Harness, incoming: &mut mpsc::Receiver<Work>, wait_ms, check| {
        let work = incoming.try_recv().expect(check);
        assert!(matches!(work.request, Request::Read { wait_ms: actual, .. } if actual == wait_ms));
        test.engine.process(VecDeque::from([work])).unwrap();
    };
    let read = |from| Request::Read {
        stream: A,
        from: Lsn(from),
        max: 1,
        wait_ms: WAIT_MS,
    };
    let mut waiting = std::pin::pin!(keeper.call(&CLIENT, read(1)));
    assert!(poll!(waiting.as_mut()).is_pending());
    process_read(&mut test, &mut incoming, WAIT_MS, "keeper queued the read");
    assert!(
        poll!(waiting.as_mut()).is_pending(),
        "read completed before commit"
    );
    assert_eq!(
        test.send(append(A, 1, 2, &[], 1)),
        Reply::Appended { tail: Lsn(1) }
    );
    assert!(poll!(waiting.as_mut()).is_pending());
    process_read(&mut test, &mut incoming, WAIT_MS, "read did not recheck after commit");
    assert_eq!(waiting.await.unwrap(), page(1, 1, &[(1, b"x")]));

    let mut expiring = std::pin::pin!(keeper.call(&CLIENT, read(2)));
    assert!(poll!(expiring.as_mut()).is_pending());
    process_read(&mut test, &mut incoming, WAIT_MS, "keeper queued the read");
    assert!(poll!(expiring.as_mut()).is_pending());
    tokio::time::advance(Duration::from_millis(u64::from(WAIT_MS - 1))).await;
    assert!(poll!(expiring.as_mut()).is_pending());
    assert!(incoming.is_empty(), "read resampled before deadline");
    tokio::time::advance(Duration::from_millis(1)).await;
    assert!(poll!(expiring.as_mut()).is_pending());
    process_read(&mut test, &mut incoming, 0, "read did not recheck at the deadline");
    assert_eq!(expiring.await.unwrap(), page(1, 1, &[]));
}

#[test]
fn nomination_policy_can_refuse_a_seal() {
    let mut test = Harness::new(Limits::default());
    test.engine.policy = Arc::new(|_: &Identity, stream, epoch| stream == A && epoch == Epoch(2));
    test.send(create(A));
    assert_eq!(test.send(seal(A, 1)), Reply::Refused(Refusal::Unauthorized));
    assert!(matches!(test.send(seal(A, 2)), Reply::Sealed(_)));
}

struct Local(HashMap<KeeperId, Keeper>);
impl Transport for Local {
    fn identity(&self) -> &Identity {
        &CLIENT
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        Box::pin(async move {
            self.0
                .get(&keeper)
                .ok_or(TransportError::Unreachable)?
                .call(&CLIENT, request)
                .await
        })
    }
}

#[tokio::test]
async fn sweeper_uses_two_survivors_and_activates_the_trimmed_learner() {
    let replacement = KeeperId(4);
    let directories: Vec<_> = (0..3).map(|_| tempdir().unwrap()).collect();
    let mut transport = Local(
        [MEMBERS[0], MEMBERS[1], replacement]
            .into_iter()
            .zip(&directories)
            .map(|(id, dir)| (id, Keeper::open(dir.path(), id, Limits::default()).unwrap()))
            .collect(),
    );
    let [first, second, _] = MEMBERS;
    for id in [first, second] {
        for request in [
            create(A),
            seal(A, 1),
            sync(A, 1, 1, &[], 0, true),
            append(A, 1, 1, &[b"trim", b"chosen"], 1),
            trim(A, 1, 1),
        ] {
            transport.call(id, request).await.unwrap();
        }
    }
    transport
        .call(first, append(A, 1, 3, &[b"stale", b"tail"], 1))
        .await
        .unwrap();
    transport.call(second, seal(A, 2)).await.unwrap();
    assert_eq!(
        transport
            .call(second, sync(A, 2, 3, &[], 1, true))
            .await
            .unwrap(),
        Reply::Synced { tail: Lsn(2) }
    );

    assert_eq!(
        transport.call(replacement, create(A)).await.unwrap(),
        Reply::Created
    );
    let Reply::Checked(view) = transport.call(replacement, check(A)).await.unwrap() else {
        panic!("bad check")
    };
    assert!(view.learner);
    let plan = Sweep {
        stream: A,
        ensemble: MEMBERS,
        survivors: [first, second],
        learner: replacement,
        epoch: Epoch(3),
    };
    let missing = transport.0.remove(&second).unwrap();
    let outcome = sweep_idle(&transport, [plan]).await.pop().unwrap().1;
    assert!(matches!(outcome, Err(SweepError::Transport { keeper, .. }) if keeper == second));
    let Reply::Checked(view) = transport.call(replacement, check(A)).await.unwrap() else {
        panic!("bad check")
    };
    assert!(view.learner, "one survivor activated the learner");

    transport.0.insert(second, missing);
    sweep_idle(&transport, [plan])
        .await
        .pop()
        .unwrap()
        .1
        .unwrap();
    for id in [first, second, replacement] {
        let Reply::Checked(view) = transport.call(id, check(A)).await.unwrap() else {
            panic!("missing swept stream")
        };
        assert_eq!(
            (view.learner, view.synced, view.tail, view.floor, view.head),
            (false, Some(Epoch(3)), Lsn(2), Lsn(2), Lsn(2))
        );
        assert_eq!(
            transport.call(id, read(A, 2)).await.unwrap(),
            page(2, 2, &[(2, b"chosen")])
        );
    }
    sweep_idle(&transport, [plan])
        .await
        .pop()
        .unwrap()
        .1
        .unwrap();
}

#[tokio::test]
async fn sweeper_restores_an_absent_survivor_from_one_durable_copy() {
    let learner = KeeperId(4);
    let [source, absent, lost] = MEMBERS;
    let next = [source, absent, learner];
    let directories: Vec<_> = (0..4).map(|_| tempdir().unwrap()).collect();
    let mut transport = Local(
        MEMBERS
            .into_iter()
            .chain([learner])
            .zip(&directories)
            .map(|(id, dir)| (id, Keeper::open(dir.path(), id, Limits::default()).unwrap()))
            .collect(),
    );
    for keeper in [source, lost] {
        for request in [create(A), seal(A, 1), sync(A, 1, 1, &[], 0, true)] {
            transport.call(keeper, request).await.unwrap();
        }
        assert_eq!(
            transport
                .call(keeper, append(A, 1, 1, &[b"chosen"], 1))
                .await
                .unwrap(),
            Reply::Appended { tail: Lsn(1) }
        );
    }
    drop(transport.0.remove(&lost).unwrap());
    assert_eq!(
        transport.call(absent, check(A)).await.unwrap(),
        Reply::Refused(Refusal::NotFound)
    );
    let plan = Sweep {
        stream: A,
        ensemble: MEMBERS,
        survivors: [source, absent],
        learner,
        epoch: Epoch(2),
    };
    let keeper = transport.0.remove(&source).unwrap();
    let unreachable = Sweep { survivors: [absent, source], ..plan };
    let [(_, outcome)] = sweep_idle(&transport, [unreachable]).await.try_into().unwrap();
    assert!(matches!(outcome, Err(SweepError::Transport { keeper, .. }) if keeper == source),
        "an absent survivor must not mask an unreachable source: {outcome:?}");
    transport.0.insert(source, keeper);
    let [(_, outcome)] = sweep_idle(&transport, [plan]).await.try_into().unwrap();
    assert!(
        outcome.is_ok(),
        "replacement must restore the absent survivor: {outcome:?}"
    );
    for keeper in next {
        assert_eq!(
            transport.call(keeper, read(A, 1)).await.unwrap(),
            page(1, 1, &[(1, b"chosen")])
        );
    }
    let unknown = Sweep { stream: B, ..plan };
    let [(_, outcome)] = sweep_idle(&transport, [unknown]).await.try_into().unwrap();
    assert!(
        matches!(
            outcome,
            Err(SweepError::Reply {
                reply: Reply::Refused(Refusal::NotFound),
                ..
            })
        ),
        "replacement requires an existing survivor"
    );
    for keeper in next {
        assert_eq!(
            transport.call(keeper, check(B)).await.unwrap(),
            Reply::Refused(Refusal::NotFound)
        );
    }
}

#[test]
fn recovery_resumes_rotation_after_only_one_stream_checkpointed() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"a1"], 1),
        append(B, 1, 1, &[b"b1"], 1),
        trim(A, 1, 1),
        append(A, 1, 2, &[b"a2"], 2),
    ]);
    let segment = test.segment();
    test.engine
        .wal
        .checkpoint_stream(A, test.engine.streams.get_mut(&A).unwrap())
        .unwrap();
    let a = test
        .dir
        .path()
        .join("streams")
        .join(format!("{:032x}", A.0));
    let path = a.join("state");
    let checkpoint = fs::read(&path).unwrap();
    let file = OpenOptions::new().write(true).open(&path).unwrap();
    file.set_modified(std::time::UNIX_EPOCH + Duration::from_secs(100))
        .unwrap();
    let modified = file.metadata().unwrap().modified().unwrap();
    drop(file);
    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    assert_eq!(
        reopened.send(read(A, 2)),
        page(2, 2, &[(2, b"a2")]),
        "checkpointed stream was replayed twice"
    );
    assert_eq!(
        reopened.send(read(B, 1)),
        page(1, 1, &[(1, b"b1")]),
        "uncheckpointed stream was skipped"
    );
    assert_eq!(fs::read(&path).unwrap(), checkpoint);
    assert_eq!(
        fs::metadata(path).unwrap().modified().unwrap(),
        modified,
        "checkpointed stream was rewritten"
    );
    assert!(!segment.exists());
}

#[test]
fn corrupt_extent_cannot_supply_a_read() {
    use std::io::{Seek, SeekFrom};
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"valid"], 1));
    test.engine.wal.rotate(&mut test.engine.streams).unwrap();
    let dir = test
        .dir
        .path()
        .join("streams")
        .join(format!("{:032x}", A.0));
    let path = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| path.extension().is_some_and(|ext| ext == "extent"))
        .unwrap();
    let mut file = OpenOptions::new().write(true).open(path).unwrap();
    file.seek(SeekFrom::End(-1)).unwrap();
    file.write_all(b"!").unwrap();
    let (work, mut result) = work(&CLIENT, read(A, 1));
    let error = test.engine.process(VecDeque::from([work])).unwrap_err();
    assert_eq!(error.to_string(), "stream extent checksum mismatch");
    assert!(matches!(
        result.try_recv(),
        Err(oneshot::error::TryRecvError::Closed)
    ));
}

struct SplitReplacement<'a> {
    transport: &'a Local,
    first_installed: Notify,
}
impl Transport for SplitReplacement<'_> {
    fn identity(&self) -> &Identity {
        &CLIENT
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        Box::pin(async move {
            let replacing = matches!(request, Request::Replace { .. });
            if keeper == MEMBERS[1] && replacing {
                self.first_installed.notified().await;
                return Err(TransportError::Unreachable);
            }
            let result = self.transport.call(keeper, request).await;
            if keeper == MEMBERS[0] && replacing {
                assert_eq!(result, Ok(Reply::Replaced));
                self.first_installed.notify_one();
            }
            result
        })
    }
}

#[tokio::test]
async fn replacement_fences_stale_routes_and_resumes_a_split_install() {
    let learner = KeeperId(4);
    let next = [MEMBERS[0], MEMBERS[1], learner];
    let directories: Vec<_> = (0..4).map(|_| tempdir().unwrap()).collect();
    let transport = Local(
        MEMBERS
            .into_iter()
            .chain([learner])
            .zip(&directories)
            .map(|(id, dir)| (id, Keeper::open(dir.path(), id, Limits::default()).unwrap()))
            .collect(),
    );
    for id in MEMBERS {
        for request in [create(A), seal(A, 1), sync(A, 1, 1, &[], 0, true)] {
            transport.call(id, request).await.unwrap();
        }
    }
    let plan = Sweep {
        stream: A,
        ensemble: MEMBERS,
        survivors: [MEMBERS[0], MEMBERS[1]],
        learner,
        epoch: Epoch(2),
    };
    let split = SplitReplacement {
        transport: &transport,
        first_installed: Notify::new(),
    };
    let [(stream, outcome)] = sweep_idle(&split, [plan]).await.try_into().unwrap();
    assert_eq!(stream, A);
    assert!(matches!(outcome, Err(SweepError::Transport {
        keeper,
        error: TransportError::Unreachable,
    }) if keeper == MEMBERS[1]));
    let Reply::Checked(second) = transport.call(MEMBERS[1], check(A)).await.unwrap() else {
        panic!("missing second survivor")
    };
    assert_eq!(second.ensemble, MEMBERS, "the second survivor already moved");
    let Reply::Checked(view) = transport.call(learner, check(A)).await.unwrap() else {
        panic!("missing learner")
    };
    assert_eq!(view.synced, Some(Epoch(2)));
    assert!(view.learner, "sync alone activated a replacement");
    assert_eq!(
        transport
            .call(learner, append(A, 2, 1, &[b"too early"], 0))
            .await
            .unwrap(),
        Reply::Refused(Refusal::NotSynced)
    );
    assert_eq!(
        transport.call(MEMBERS[0], seal(A, 2)).await.unwrap(),
        Reply::Refused(Refusal::WrongEnsemble { ensemble: next }),
        "stale route gained a promise after one survivor moved"
    );

    sweep_idle(&transport, [plan])
        .await
        .pop()
        .unwrap()
        .1
        .unwrap();
    for id in next {
        let Reply::Checked(view) = transport.call(id, check(A)).await.unwrap() else {
            panic!("missing replacement member")
        };
        assert!(!view.learner);
        assert_eq!(view.ensemble, next);
        assert_eq!(
            transport.call(id, seal(A, 4)).await.unwrap(),
            Reply::Refused(Refusal::WrongEnsemble { ensemble: next }),
            "stale route gained a promise"
        );
        assert!(matches!(
            transport.call(id, seal_at(A, 3, next)).await.unwrap(),
            Reply::Sealed(_)
        ));
    }
    assert!(matches!(
        transport.call(MEMBERS[2], seal(A, 4)).await.unwrap(),
        Reply::Sealed(_)
    ));
    for id in [MEMBERS[0], MEMBERS[1]] {
        assert_eq!(
            transport.call(id, delete(A)).await.unwrap(),
            Reply::Refused(Refusal::WrongEnsemble { ensemble: next }),
            "stale route gained a tombstone"
        );
    }
}

#[test]
fn replacement_ensemble_survives_wal_recovery() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    let new = [MEMBERS[0], MEMBERS[1], KeeperId(4)];
    assert_eq!(
        test.send(Request::Replace {
            stream: A,
            epoch: Epoch(1),
            from: MEMBERS,
            to: new,
        }),
        Reply::Replaced
    );
    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    let Reply::Checked(view) = reopened.send(check(A)) else {
        panic!("the replaced stream did not replay");
    };
    assert_eq!(view.ensemble, new, "replay must preserve the new ensemble");
    assert_eq!(
        view.promised,
        Some((Epoch(1), CLIENT.clone())),
        "replay must preserve the authenticated certificate identity"
    );
    assert_eq!(
        reopened.send(seal(A, 2)),
        Reply::Refused(Refusal::WrongEnsemble { ensemble: new })
    );
    assert!(matches!(
        reopened.send(seal_at(A, 2, new)),
        Reply::Sealed(_)
    ));
    assert_eq!(
        reopened.send(Request::Delete {
            stream: A,
            ensemble: new
        }),
        Reply::Deleted
    );
    assert_eq!(
        reopened.send(delete(A)),
        Reply::Refused(Refusal::WrongEnsemble { ensemble: new })
    );
}
