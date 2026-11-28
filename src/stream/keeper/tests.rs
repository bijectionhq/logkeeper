use std::{fs, fs::OpenOptions, io::Write, path::PathBuf};

use bytes::Buf;
use futures::poll;
use journal_contract::BoxFuture;
use tempfile::{TempDir, tempdir};
use tokio::sync::Notify;

use super::*;

#[cfg(feature = "stream")]
mod timed_original;

const A: StreamId = StreamId(10);
const B: StreamId = StreamId(20);
const MEMBERS: [KeeperId; 3] = [KeeperId(1), KeeperId(2), KeeperId(3)];
static CLIENT: Identity = Identity::from_static("urn:logkeeper:client:writer-a");
static OTHER: Identity = Identity::from_static("urn:logkeeper:client:writer-b");

#[test]
fn wal_request_is_encoded_after_the_identity_in_the_final_owner() {
    let request = Request::Append {
        stream: A,
        epoch: Epoch(2),
        at: Lsn(3),
        records: vec![Bytes::from_static(b"first"), Bytes::from_static(b"second")],
        head: Lsn(4),
    };
    let request_bytes = codec::encode_request(&request).unwrap();
    for identity in [None, Some(&CLIENT)] {
        let identity_bytes = identity.map_or("", Identity::as_str).as_bytes();
        let entry = wal::entry(&request, identity).unwrap();
        let mut expected = (identity_bytes.len() as u32).to_be_bytes().to_vec();
        expected.extend_from_slice(identity_bytes);
        expected.extend_from_slice(&request_bytes);
        assert_eq!(entry.as_ref(), expected.as_slice());
        assert_eq!(
            codec::decode_request(entry.slice(4 + identity_bytes.len()..)).unwrap(),
            request,
        );
    }
    let oversized = Identity::from("a".repeat(wal::MAX_IDENTITY_BYTES + 1).as_str());
    assert_eq!(
        wal::entry(&request, Some(&oversized))
            .unwrap_err()
            .to_string(),
        "oversized WAL identity",
    );
}

#[test]
fn wal_round_keeps_exact_frame_bytes_across_short_vectored_writes() {
    #[derive(Default)]
    struct ShortWrites(Vec<u8>);

    impl Write for ShortWrites {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let count = bytes.len().min(7);
            self.0.extend_from_slice(&bytes[..count]);
            Ok(count)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    let mut expected = Vec::new();
    let mut round = wal::Round::default();
    let entry = Bytes::from_static(b"a request fragment with binary bytes\0\xff");
    for index in 0..40 {
        let stream = if index % 2 == 0 { A } else { B };
        let first = index < 2;
        let last = index >= 38;
        wal::fragment(&mut expected, stream, first, last, &entry);
        round.push(stream, first, last, entry.clone());
    }
    let mut output = ShortWrites::default();
    round.write_to(&mut output).unwrap();
    assert_eq!(round.len(), expected.len());
    assert_eq!(output.0, expected);
}

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
        proposal: 1,
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
        let mut deletes = false;
        let (pending, results): (VecDeque<_>, Vec<_>) = requests
            .into_iter()
            .map(|request| {
                deletes |= matches!(request, Request::Delete { .. });
                work(&CLIENT, request)
            })
            .unzip();
        self.engine.process(pending).unwrap();
        if deletes {
            self.engine.drain_checkpoints().unwrap();
        }
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
        self.engine.wal.segment()
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
fn a_checkpoint_retains_the_seal_proposal() {
    let mut test = Harness::new(Limits::default());
    assert_eq!(test.send(create(A)), Reply::Created);
    let seal = |proposal| Request::Seal {
        stream: A,
        ensemble: MEMBERS,
        epoch: Epoch(1),
        proposal,
    };
    let promised = test.send(seal(1));
    assert!(
        matches!(&promised, Reply::Sealed(view) if view.promised == Some((Epoch(1), CLIENT.clone(), 1)))
    );
    let Harness { mut engine, dir } = test;
    engine.wal.rotate(&engine.streams).unwrap();
    engine.drain_checkpoints().unwrap();
    drop(engine);

    let engine = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let mut reopened = Harness { engine, dir };
    assert_eq!(
        reopened.send(seal(2)),
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) }),
        "reopened keeper accepted a different proposal"
    );
    assert_eq!(reopened.send(seal(1)), promised);
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
fn incomplete_sync_is_invisible_until_complete() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"committed", b"divergent"], 1));
    test.send(seal(A, 2));
    let voted = test.send(check(A));
    assert_eq!(
        test.send(sync(A, 2, 2, &[b"staged"], 1, false)),
        Reply::Synced { tail: Lsn(2) }
    );
    assert_eq!(
        test.send(check(A)),
        voted,
        "an incomplete Sync keeps the voted view"
    );
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"divergent")])
    );

    let reopen = |test: Harness, rotate: bool| {
        let Harness { mut engine, dir } = test;
        if rotate {
            engine.wal.rotate(&engine.streams).unwrap();
        }
        drop(engine);
        let engine =
            Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
        Harness { engine, dir }
    };
    let mut test = reopen(test, false);
    assert_eq!(
        test.send(check(A)),
        voted,
        "WAL replay restores the staged Sync"
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[b"more"], 1, false)),
        Reply::Synced { tail: Lsn(2) }
    );
    let mut test = reopen(test, true);
    assert_eq!(
        test.send(check(A)),
        voted,
        "a checkpoint keeps the staged Sync"
    );
    assert_eq!(
        test.send(sync(A, 2, 4, &[], 1, true)),
        Reply::Synced { tail: Lsn(3) }
    );
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"staged"), (3, b"more")])
    );
    let mut test = reopen(test, true);
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"staged"), (3, b"more")])
    );

    test.send(seal(A, 3));
    let voted = test.send(check(A));
    test.send(sync(A, 3, 2, &[b"abandoned"], 1, false));
    test.send(seal(A, 4));
    assert_eq!(
        test.send(sync(A, 4, 4, &[], 1, true)),
        Reply::Synced { tail: Lsn(3) },
        "a new promise discards the staged Sync"
    );
    assert_eq!(
        test.send(recover(A, 4, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"staged"), (3, b"more")])
    );
    let Reply::Checked(view) = voted else {
        panic!("missing stream")
    };
    assert_eq!(view.tail, Lsn(3));
}

#[test]
fn background_checkpoint_follows_staged_records_into_the_completed_history() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"committed", b"divergent"], 1));
    test.send(seal(A, 2));
    test.send(sync(A, 2, 2, &[b"staged"], 1, false));
    let (gate, wait) = std::sync::mpsc::channel();
    test.engine.wal.rotation_gate = Some(wait);
    test.engine
        .wal
        .start_rotation(&test.engine.streams, false)
        .unwrap();
    // The Sync completes while the checkpoint of its staged record is being written.
    assert_eq!(
        test.send(sync(A, 2, 3, &[], 1, true)),
        Reply::Synced { tail: Lsn(2) }
    );
    drop(gate);
    test.engine.wal.finish_rotation().unwrap();
    let pending = test.engine.streams[&A]
        .records
        .iter()
        .map(|record| matches!(*record.payload.read(), state::Payload::Pending(_)))
        .collect::<Vec<_>>();
    assert_eq!(pending, [false, false], "the staged copy now backs LSN 2");
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let Harness { engine, dir } = test;
    drop(engine);
    let engine = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let mut test = Harness { engine, dir };
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"committed"), (2, b"staged")])
    );
}

#[test]
fn staged_floor_skips_the_retained_history_on_completion() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"old"], 1));
    test.send(seal(A, 2));
    let voted = test.send(check(A));
    let skip = |from: u64, records: Vec<Bytes>, runs, complete| Request::Sync {
        stream: A,
        epoch: Epoch(2),
        floor: Lsn(5),
        from: Lsn(from),
        records,
        runs,
        head: Lsn(4),
        complete,
    };
    let run = EpochRun {
        epoch: Epoch(1),
        first: Lsn(5),
        last: Lsn(5),
    };
    assert_eq!(
        test.send(skip(5, vec![Bytes::from_static(b"kept")], vec![run], false)),
        Reply::Synced { tail: Lsn(1) }
    );
    assert_eq!(test.send(check(A)), voted);
    assert_eq!(
        test.send(sync(A, 2, 6, &[], 4, true)),
        Reply::Synced { tail: Lsn(5) },
        "a later chunk keeps the staged floor"
    );
    assert_eq!(test.send(recover(A, 2, 5)), page(5, 4, &[(5, b"kept")]));
}

#[test]
fn sync_charges_only_the_retained_and_staged_prefixes_it_keeps() {
    let mut test = Harness::new(Limits {
        stream_quota_bytes: 4,
        ..Limits::default()
    });
    test.writer(A);
    test.send(append(A, 1, 1, &[b"a", b"bb"], 1));
    test.send(seal(A, 2));
    assert_eq!(
        test.send(sync(A, 2, 2, &[b"c", b"dd"], 1, false)),
        Reply::Synced { tail: Lsn(2) },
        "Sync replaces the uncommitted retained suffix"
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[b"eee"], 1, false)),
        Reply::Refused(Refusal::Full { floor: Lsn(1) }),
        "quota includes the staged prefix"
    );
    assert_eq!(
        test.send(sync(A, 2, 3, &[b"ff"], 1, true)),
        Reply::Synced { tail: Lsn(3) },
        "quota excludes the replaced staged suffix"
    );
    assert_eq!(
        test.send(recover(A, 2, 1)),
        page(1, 1, &[(1, b"a"), (2, b"c"), (3, b"ff")])
    );
}

#[test]
fn complete_sync_can_skip_past_an_empty_keeper() {
    let mut test = Harness::new(Limits::default());
    assert_eq!(test.send(create(A)), Reply::Created);
    assert!(matches!(test.send(seal(A, 1)), Reply::Sealed(_)));
    let request = Request::Sync {
        stream: A,
        epoch: Epoch(1),
        floor: Lsn(2),
        from: Lsn(2),
        records: vec![],
        runs: vec![],
        head: Lsn(1),
        complete: true,
    };
    assert_eq!(
        test.send(request),
        Reply::Synced { tail: Lsn(1) },
        "the skipped prefix is absent from the request and local history"
    );
    let Reply::Checked(view) = test.send(check(A)) else {
        panic!("missing stream");
    };
    assert_eq!((view.floor, view.head, view.tail), (Lsn(2), Lsn(1), Lsn(1)));
    assert!(view.runs.is_empty());
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
        Reply::Refused(Refusal::Fenced { promised: Epoch(1) }),
        "keeper admitted an append from a different identity"
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
    assert_eq!(
        test.send(append(A, 1, 1, &[b"abc"], 1)),
        Reply::Appended { tail: Lsn(1) },
        "a retained identical retry charged quota"
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
            Some((Epoch(1), CLIENT.clone(), 1)),
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
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let segment = test.segment();
    let pack = pack_files(test.dir.path()).pop().unwrap();
    let before = fs::read(&pack).unwrap();
    assert!(before.windows(6).any(|bytes| bytes == b"remove"));
    assert_eq!(test.send(delete(B)), Reply::Deleted);
    assert_ne!(test.segment(), segment, "delete must rotate");
    assert!(!segment.exists(), "old shared segment still exists");
    assert!(!pack.exists(), "deleted stream kept a shared pack");
    let packs = pack_files(test.dir.path());
    assert_eq!(packs.len(), 1);
    assert_eq!(fs::read(&packs[0]).unwrap(), b"keep");
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
    let mut tail = Vec::new();
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
    reopened.engine.drain_checkpoints().unwrap();
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
    let process_read = |test: &mut Harness,
                        incoming: &mut mpsc::Receiver<Vec<Work>>,
                        wait_ms,
                        check| {
        let mut envelope = incoming.try_recv().expect(check);
        assert_eq!(envelope.len(), 1, "a read is resubmitted alone");
        let work = envelope.pop().unwrap();
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
    process_read(
        &mut test,
        &mut incoming,
        WAIT_MS,
        "read did not recheck after commit",
    );
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
    process_read(
        &mut test,
        &mut incoming,
        0,
        "read did not recheck at the deadline",
    );
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
    let plan = Sweep::new(A, MEMBERS, [first, second], replacement, Epoch(3));
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
    let restarted = Sweep::new(A, MEMBERS, [first, second], replacement, Epoch(3));
    let [(_, outcome)] = sweep_idle(&transport, [restarted])
        .await
        .try_into()
        .unwrap();
    assert!(
        matches!(
            outcome,
            Err(SweepError::Reply {
                reply: Reply::Refused(Refusal::Fenced { promised: Epoch(3) }),
                ..
            })
        ),
        "another sweep plan re-elected the same epoch"
    );
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
    let plan = Sweep::new(A, MEMBERS, [source, absent], learner, Epoch(2));
    let keeper = transport.0.remove(&source).unwrap();
    let unreachable = Sweep::new(A, MEMBERS, [absent, source], learner, Epoch(2));
    let [(_, outcome)] = sweep_idle(&transport, [unreachable])
        .await
        .try_into()
        .unwrap();
    assert!(
        matches!(outcome, Err(SweepError::Transport { keeper, .. }) if keeper == source),
        "an absent survivor must not mask an unreachable source: {outcome:?}"
    );
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
    let unknown = Sweep::new(B, MEMBERS, [source, absent], learner, Epoch(2));
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

#[tokio::test]
async fn sweeper_transfers_multiple_pages_across_successive_replacements() {
    use crate::stream::writer::Writer;
    use journal_contract::Journal;

    let [source, lagging, lost] = MEMBERS;
    let learner = KeeperId(4);
    let successor = KeeperId(5);
    let directories: Vec<_> = (0..5).map(|_| tempdir().unwrap()).collect();
    let mut transport = Local(
        MEMBERS
            .into_iter()
            .chain([learner, successor])
            .zip(&directories)
            .map(|(id, dir)| (id, Keeper::open(dir.path(), id, Limits::default()).unwrap()))
            .collect(),
    );
    let records = vec![b"before".as_slice(); 8193];
    let end = Lsn(records.len() as u64);
    for keeper in MEMBERS {
        for request in [create(A), seal(A, 1), sync(A, 1, 1, &[], 0, true)] {
            transport.call(keeper, request).await.unwrap();
        }
    }
    for keeper in [source, lost] {
        assert_eq!(
            transport
                .call(keeper, append(A, 1, 1, &records, end.0))
                .await
                .unwrap(),
            Reply::Appended { tail: end }
        );
    }
    transport.0.remove(&lost).unwrap();
    let transport = Arc::new(transport);
    let stale = Writer::new(transport.clone(), MEMBERS).unwrap();
    let first = Sweep::new(A, MEMBERS, [source, lagging], learner, Epoch(2));
    let [(_, outcome)] = sweep_idle(&*transport, [first]).await.try_into().unwrap();
    assert!(
        outcome.is_ok(),
        "sweep rejected its incomplete Sync reply: {outcome:?}"
    );
    let middle = [source, lagging, learner];
    let writer = Writer::new(transport.clone(), middle).unwrap();
    assert_eq!(writer.head(A).await, Ok(end));
    // A writer bound to the old ensemble follows the move on `Unavailable`: a voting
    // member reports the new ensemble, so the stale roster still reads the fresh head.
    assert_eq!(
        stale.head(A).await,
        Ok(end),
        "stale roster did not follow the replacement"
    );

    let epoch = Epoch(3);
    let last = Lsn(end.0 + 1);
    assert_eq!(writer.seal(A, epoch).await, Ok(end));
    assert_eq!(
        writer
            .append(A, epoch, last, Bytes::from_static(b"after"))
            .await,
        Ok(last)
    );
    let mut transport = Local(transport.0.clone());
    transport.0.remove(&source).unwrap();
    let transport = Arc::new(transport);
    let second = Sweep::new(A, middle, [lagging, learner], successor, Epoch(4));
    let [(_, outcome)] = sweep_idle(&*transport, [second]).await.try_into().unwrap();
    assert!(
        outcome.is_ok(),
        "second replacement lost the recovered prefix: {outcome:?}"
    );
    let observer = Writer::new(transport.clone(), [successor, lagging, learner]).unwrap();
    assert_eq!(observer.head(A).await, Ok(last));
    assert_eq!(
        transport.call(successor, read(A, end.0)).await.unwrap(),
        page(1, last.0, &[(end.0, b"before"), (last.0, b"after")])
    );
}

#[test]
fn checkpoint_boundary_controls_wal_replay() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"a1"], 1),
        append(B, 1, 1, &[b"b1"], 1),
        trim(A, 1, 1),
    ]);
    let old = test.segment();
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    // Crash after publishing the index and before unlinking the covered segment.
    fs::write(&old, b"damaged redundant data").unwrap();
    test.send(append(A, 1, 2, &[b"a2"], 2));

    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow))
            .expect("covered WAL was applied again"),
        dir,
    };
    let view = reopened.send(check(A));
    assert!(
        matches!(view, Reply::Checked(view) if view.floor == Lsn(2) && view.tail == Lsn(2)),
        "replay lost the indexed floor or the WAL suffix"
    );
    assert_eq!(reopened.send(read(A, 2)), page(2, 2, &[(2, b"a2")]));
    assert_eq!(reopened.send(read(B, 1)), page(1, 1, &[(1, b"b1")]));
    reopened.engine.drain_checkpoints().unwrap();
    assert!(!old.exists());
}

#[test]
fn wal_and_checkpoint_headers_match_the_existing_format() {
    let mut encoded = Vec::new();
    let stream = u128::from_be_bytes(core::array::from_fn(|index| index as u8));
    assert!(wal_bytes::encode_fragment(
        &mut encoded,
        stream,
        3,
        &[0, 255]
    ));
    let frame = b"\x00\x00\x00\x13\x2f\xb7\xbc\xe9\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x03\x00\xff";
    assert_eq!(encoded.as_slice(), frame, "WAL frame bytes changed");
    let (body, rest) = wal_bytes::decode_frame(frame, 64).unwrap();
    assert!(rest.is_empty());
    assert_eq!(
        wal_bytes::decode_fragment(body),
        Some((stream, 3, &[0, 255][..]))
    );
    for cut in 0..frame.len() {
        assert!(
            wal_bytes::decode_frame(&frame[..cut], 64).is_none(),
            "accepted a torn frame at {cut}"
        );
    }
    let mut corrupt = *frame;
    corrupt[4] ^= 1;
    assert!(
        wal_bytes::decode_frame(&corrupt, 64).is_none(),
        "accepted a corrupted frame CRC"
    );

    let next = 0x0102_0304_0506_0708;
    let expected = b"LKPACK01\x01\x02\x03\x04\x05\x06\x07\x08\x00\x00\x00\x02\xe6\x8c\xf8\xc5";
    assert_eq!(
        &checkpoint_bytes::encode_index_header(next, 2),
        expected,
        "index header bytes changed"
    );
    assert_eq!(
        checkpoint_bytes::decode_index_header(expected),
        Some((next, 2))
    );
    for cut in 0..expected.len() {
        assert!(
            checkpoint_bytes::decode_index_header(&expected[..cut]).is_none(),
            "accepted a torn index header at {cut}"
        );
    }
    let mut corrupt = *expected;
    corrupt[20] ^= 1;
    assert!(
        checkpoint_bytes::decode_index_header(&corrupt).is_none(),
        "accepted a corrupted index CRC"
    );
}

#[test]
fn checkpoint_index_requires_every_byte() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"retained"], 1));
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let path = test.dir.path().join("INDEX");
    let bytes = fs::read(&path).unwrap();
    let opens = || checkpoint::Checkpoint::load(test.dir.path()).is_ok_and(|index| index.is_some());

    assert!(opens(), "valid index must open");
    for cut in 0..bytes.len() {
        fs::write(&path, &bytes[..cut]).unwrap();
        assert!(!opens(), "index opened after truncation at byte {cut}");
    }

    let mut trailing = bytes;
    trailing.push(0);
    fs::write(&path, trailing).unwrap();
    assert!(!opens(), "index opened with trailing bytes");
}

#[test]
fn checkpoint_pack_writes_and_reopens_exact_extents() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"first", b"", b"third-longer"], 3),
        append(B, 1, 1, &[b"old"], 1),
    ]);
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    // Deleting B makes the next checkpoint repack A's already packed records.
    test.send(delete(B));
    let mut paths = pack_files(test.dir.path());
    assert_eq!(paths.len(), 1);
    assert_eq!(
        fs::read(paths.pop().unwrap()).unwrap(),
        b"firstthird-longer",
        "pack write changed the payload bytes"
    );

    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    assert_eq!(
        reopened.send(read(A, 1)),
        page(1, 3, &[(1, b"first"), (2, b""), (3, b"third-longer")]),
        "packed payloads changed on reopen",
    );
}

#[test]
fn corrupt_extent_cannot_supply_a_read() {
    use std::io::{Seek, SeekFrom};
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"valid"], 1));
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let path = pack_files(test.dir.path()).pop().unwrap();
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
    let plan = Sweep::new(A, MEMBERS, [MEMBERS[0], MEMBERS[1]], learner, Epoch(2));
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
    assert_eq!(
        second.ensemble, MEMBERS,
        "the second survivor already moved"
    );
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
        Some((Epoch(1), CLIENT.clone(), 1)),
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

/// Feed envelopes through the WAL thread's admission and count the synced rounds.
fn rounds_for_envelopes(batched: bool) -> usize {
    const STREAMS: u128 = 10;
    let limits = Limits {
        round_requests: 4,
        ..Limits::default()
    };
    let mut test = Harness::new(limits);
    let streams: Vec<_> = (1..=STREAMS).map(|id| StreamId(100 + id)).collect();
    for &stream in &streams {
        test.writer(stream);
    }
    let before = test.engine.wal.rounds.len();
    let (works, mut results): (Vec<_>, Vec<_>) = streams
        .iter()
        .map(|&stream| work(&CLIENT, append(stream, 1, 1, &[b"x"], 0)))
        .unzip();
    let (send, mut incoming) = mpsc::channel(STREAMS as usize);
    if batched {
        send.try_send(works).unwrap();
    } else {
        for work in works {
            send.try_send(vec![work]).unwrap();
        }
    }
    while let Ok(first) = incoming.try_recv() {
        let pending = admit(first, &mut incoming, limits.round_requests);
        test.engine.process(pending).unwrap();
    }
    for result in &mut results {
        assert_eq!(
            result.try_recv().unwrap().0,
            Ok(Reply::Appended { tail: Lsn(1) })
        );
    }
    test.engine.wal.rounds.len() - before
}

#[test]
fn a_batch_envelope_is_decided_and_synced_in_one_round() {
    assert_eq!(rounds_for_envelopes(true), 1);
    // Negative control: the same requests as separate envelopes need one sync per
    // `round_requests` requests.
    assert_eq!(rounds_for_envelopes(false), 3);
}

#[tokio::test]
async fn keeper_answers_a_batch_in_request_order_with_per_request_refusals() {
    let dir = tempdir().unwrap();
    let keeper = Keeper::open(dir.path(), MEMBERS[0], Limits::default()).unwrap();
    let reply = keeper
        .call(
            &CLIENT,
            Request::Batch(vec![
                create(A),
                seal(A, 1),
                append(A, 1, 1, &[b"early"], 0),
                sync(A, 1, 1, &[], 0, true),
                append(A, 1, 1, &[b"x", b"y"], 0),
                check(B),
            ]),
        )
        .await
        .unwrap();
    let Reply::Batch(replies) = reply else {
        panic!("batch answered with {reply:?}");
    };
    assert_eq!(replies.len(), 6);
    assert_eq!(replies[0], Reply::Created);
    assert!(matches!(replies[1], Reply::Sealed(_)));
    assert_eq!(replies[2], Reply::Refused(Refusal::NotSynced));
    assert_eq!(replies[3], Reply::Synced { tail: Lsn(0) });
    assert_eq!(replies[4], Reply::Appended { tail: Lsn(2) });
    assert_eq!(replies[5], Reply::Refused(Refusal::NotFound));
    for malformed in [
        Request::Batch(Vec::new()),
        Request::Batch(vec![Request::Batch(vec![check(A)])]),
    ] {
        assert_eq!(
            keeper.call(&CLIENT, malformed).await,
            Ok(Reply::Refused(Refusal::Unauthorized))
        );
    }
}

fn segment_count(dir: &Path) -> usize {
    fs::read_dir(dir.join("segments")).unwrap().count()
}

#[test]
fn background_rotation_keeps_deciding_rounds_until_its_checkpoints_are_durable() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"a1", b"a2"], 2),
        append(B, 1, 1, &[b"b1", b"b2"], 2),
    ]);
    let index = test.dir.path().join("INDEX");
    let (gate, wait) = std::sync::mpsc::channel();
    test.engine.wal.rotation_gate = Some(wait);
    test.engine
        .wal
        .start_rotation(&test.engine.streams, false)
        .unwrap();

    // The checkpoint worker is held, yet rounds are decided and synced in the new segment.
    let rounds = test.engine.wal.rounds.len();
    assert_eq!(
        test.batch([append(A, 1, 3, &[b"a3"], 3), trim(B, 1, 1)]),
        [
            Reply::Appended { tail: Lsn(3) },
            Reply::Trimmed { floor: Lsn(2) }
        ]
    );
    assert_eq!(test.engine.wal.rounds.len(), rounds + 1);
    assert!(!index.exists());
    assert_eq!(
        segment_count(test.dir.path()),
        2,
        "old segment retired early"
    );

    drop(gate);
    test.engine.wal.finish_rotation().unwrap();
    assert!(index.exists());
    assert_eq!(segment_count(test.dir.path()), 1);
    let kinds = |stream: StreamId, engine: &Engine| {
        engine.streams[&stream]
            .records
            .iter()
            .map(|record| matches!(*record.payload.read(), state::Payload::Pending(_)))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        kinds(A, &test.engine),
        [false, false, true],
        "a1 and a2 moved to the extent"
    );
    assert_eq!(
        kinds(B, &test.engine),
        [false],
        "b1 was trimmed before installation"
    );
    assert_eq!(
        test.send(read(A, 1)),
        page(1, 3, &[(1, b"a1"), (2, b"a2"), (3, b"a3")])
    );

    let Harness { engine, dir } = test;
    drop(engine);
    let mut reopened = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap(),
        dir,
    };
    assert_eq!(
        reopened.send(read(A, 1)),
        page(1, 3, &[(1, b"a1"), (2, b"a2"), (3, b"a3")])
    );
    assert_eq!(reopened.send(read(B, 2)), page(2, 2, &[(2, b"b2")]));
}

fn pack_files(dir: &Path) -> Vec<PathBuf> {
    fs::read_dir(dir)
        .unwrap()
        .map(|file| file.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "pack"))
        .collect()
}

#[test]
fn rotation_sync_count_is_independent_of_dirty_streams() {
    let rotate = |count| {
        let mut test = Harness::new(Limits::default());
        for id in 1..=count {
            test.writer(StreamId(id));
            test.send(append(StreamId(id), 1, 1, &[b"record"], 1));
        }
        let before = durability::syncs();
        test.engine.wal.rotate(&test.engine.streams).unwrap();
        assert_eq!(pack_files(test.dir.path()).len(), 1);
        durability::syncs() - before + test.engine.wal.rotation_syncs()
    };
    let one = rotate(1);
    let many = rotate(10_000);
    assert_eq!(
        one, many,
        "rotation sync count depends on dirty stream count"
    );
    assert_eq!(many, 7);
}

#[test]
fn delete_joins_its_compaction_without_blocking_other_rounds() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.send(append(B, 1, 1, &[b"secret"], 1));
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let old_pack = pack_files(test.dir.path()).pop().unwrap();
    let (gate, wait) = std::sync::mpsc::channel();
    test.engine.wal.rotation_gate = Some(wait);

    let (delete_work, mut deleted) = work(&CLIENT, delete(B));
    let Harness { mut engine, dir } = test;
    let (return_engine, returned) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        engine.process(VecDeque::from([delete_work])).unwrap();
        let _ = return_engine.send(engine);
    });
    let engine = returned.recv_timeout(Duration::from_secs(5));
    assert!(
        engine.is_ok(),
        "delete blocked the keeper round thread on compaction"
    );
    let mut test = Harness {
        engine: engine.unwrap(),
        dir,
    };
    let (retry_work, mut retried) = work(&CLIENT, delete(B));
    test.engine.process(VecDeque::from([retry_work])).unwrap();

    assert!(old_pack.exists());
    assert!(
        matches!(deleted.try_recv(), Err(oneshot::error::TryRecvError::Empty)),
        "delete replied before the tombstone and erasure checkpoint"
    );
    assert!(
        matches!(retried.try_recv(), Err(oneshot::error::TryRecvError::Empty)),
        "delete retry replied before erasure"
    );
    assert_eq!(test.send(read(B, 1)), Reply::Refused(Refusal::Deleted));
    assert_eq!(
        test.send(append(A, 1, 1, &[b"other stream"], 1)),
        Reply::Appended { tail: Lsn(1) }
    );

    drop(gate);
    test.engine.drain_checkpoints().unwrap();
    assert_eq!(deleted.try_recv().unwrap().0, Ok(Reply::Deleted));
    assert_eq!(retried.try_recv().unwrap().0, Ok(Reply::Deleted));
    assert!(!old_pack.exists());
}

#[test]
fn replay_and_new_rounds_do_not_wait_for_startup_compaction() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"one"], 1));
    let old = test.segment();
    let Harness { engine, dir } = test;
    drop(engine);
    let mut engine =
        Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let (gate, wait) = std::sync::mpsc::channel();
    engine.wal.rotation_gate = Some(wait);
    let mut test = Harness { engine, dir };
    assert!(old.exists(), "startup checkpoint ran synchronously");
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"one")]));
    assert_eq!(
        test.send(append(A, 1, 2, &[b"two"], 2)),
        Reply::Appended { tail: Lsn(2) }
    );
    assert!(old.exists(), "startup ran compaction on the round thread");
    drop(gate);
    test.engine.drain_checkpoints().unwrap();
    assert!(!old.exists());
    assert_eq!(
        test.send(read(A, 1)),
        page(1, 2, &[(1, b"one"), (2, b"two")])
    );
}

#[test]
fn segment_rollover_caps_files_and_keeps_interleaved_fragments() {
    let mut test = Harness::new(Limits {
        round_bytes_per_stream: 85,
        ..Limits::default()
    });
    test.engine.wal.segment_bytes = 256;
    test.writer(A);
    test.writer(B);
    let mut large = append(A, 1, 1, &[], 1);
    let data = Bytes::from(vec![7; 720]);
    let Request::Append { records, .. } = &mut large else {
        unreachable!()
    };
    records.push(data.clone());
    assert_eq!(
        test.batch([large, append(B, 1, 1, &[b"small"], 1)]),
        [
            Reply::Appended { tail: Lsn(1) },
            Reply::Appended { tail: Lsn(1) }
        ]
    );
    for path in fs::read_dir(test.dir.path().join("segments")).unwrap() {
        assert!(
            path.unwrap().metadata().unwrap().len() <= 256,
            "segment exceeded its byte cap"
        );
    }
    assert!(
        segment_count(test.dir.path()) > 2,
        "fixture must roll across multiple segments"
    );
    let Harness { engine, dir } = test;
    drop(engine);
    let mut test = Harness {
        engine: Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow))
            .expect("cross-segment fragment was lost"),
        dir,
    };
    assert_eq!(
        test.send(read(A, 1)),
        Reply::Records {
            floor: Lsn(1),
            head: Lsn(1),
            records: vec![(Lsn(1), data)]
        }
    );
    assert_eq!(test.send(read(B, 1)), page(1, 1, &[(1, b"small")]));
}

#[test]
fn startup_reuses_a_checkpoint_boundary_with_an_unpublished_pack() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"live"], 1));
    let next = test.segment().with_file_name("00000000000000000001.seg");
    let orphan = test.dir.path().join("00000000000000000001.pack");
    // Crash after syncing the new pack but before publishing INDEX.
    fs::File::create(&next).unwrap();
    fs::write(&orphan, b"unpublished").unwrap();
    let covered = fs::metadata(test.segment()).unwrap().len();
    let Harness { engine, dir } = test;
    drop(engine);
    let engine = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let mut test = Harness { engine, dir };
    assert_eq!(
        test.engine.wal.uncheckpointed, covered,
        "reopen lost the WAL suffix charge"
    );
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"live")]));
    test.engine
        .drain_checkpoints()
        .expect("orphan pack blocked recovery");
    assert_eq!(test.segment(), next);
    assert_eq!(fs::read(orphan).unwrap(), b"live");
    assert_eq!(test.engine.wal.uncheckpointed, 0);
}

#[test]
fn recovered_delete_retry_waits_for_obsolete_pack_cleanup() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"ciphertext"], 1));
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let orphan = pack_files(test.dir.path()).pop().unwrap();
    let data = fs::read(&orphan).unwrap();
    assert_eq!(test.send(delete(A)), Reply::Deleted);
    // Crash after publishing the tombstone index but before unlinking its old pack.
    fs::write(&orphan, data).unwrap();
    let Harness { engine, dir } = test;
    drop(engine);
    let mut engine =
        Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let (gate, wait) = std::sync::mpsc::channel();
    engine.wal.rotation_gate = Some(wait);
    let (retry, mut result) = work(&CLIENT, delete(A));
    engine.process(VecDeque::from([retry])).unwrap();
    assert!(
        matches!(result.try_recv(), Err(oneshot::error::TryRecvError::Empty)),
        "recovered delete replied before durable cleanup"
    );
    drop(gate);
    engine.drain_checkpoints().unwrap();
    assert_eq!(result.try_recv().unwrap().0, Ok(Reply::Deleted));
    assert!(!orphan.exists());
}

#[test]
fn wal_backlog_keeps_observations_running_without_growing_replay() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    let (gate, wait) = std::sync::mpsc::channel();
    test.engine.wal.rotation_gate = Some(wait);
    test.engine.wal.uncheckpointed = wal::MAX_WAL_SUFFIX_BYTES;
    let (job, mut result) = work(&CLIENT, append(A, 1, 1, &[b"later"], 1));
    test.engine.process(VecDeque::from([job])).unwrap();
    assert_eq!(
        result.try_recv().unwrap().0,
        Err(TransportError::TimedOut),
        "the keeper admitted a new mutation above the recovery bound"
    );
    assert_eq!(test.send(read(A, 1)), page(1, 0, &[]));
    drop(gate);
    test.engine.drain_checkpoints().unwrap();
    assert_eq!(
        test.send(append(A, 1, 1, &[b"later"], 1)),
        Reply::Appended { tail: Lsn(1) }
    );
}

#[test]
fn failed_index_publication_leaves_covered_wal_for_recovery() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.send(append(A, 1, 1, &[b"durable"], 1));
    let old = test.segment();
    let blocker = test.dir.path().join("INDEX.tmp");
    fs::create_dir(&blocker).unwrap();
    test.engine
        .wal
        .start_rotation(&test.engine.streams, false)
        .unwrap();
    assert!(test.engine.wal.finish_rotation().is_err());
    assert!(
        old.exists(),
        "covered WAL was retired before index publication"
    );
    assert!(!test.dir.path().join("INDEX").exists());
    assert_eq!(
        pack_files(test.dir.path()).len(),
        1,
        "the pack precedes index publication"
    );
    fs::remove_dir(blocker).unwrap();
    let Harness { engine, dir } = test;
    drop(engine);
    let engine = Engine::open(dir.path(), MEMBERS[0], Limits::default(), Arc::new(Allow)).unwrap();
    let mut test = Harness { engine, dir };
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"durable")]));
    test.engine.drain_checkpoints().unwrap();
    assert!(!old.exists());
}

#[test]
fn rotation_reclaims_mixed_packs_with_excess_discarded_bytes() {
    let mut test = Harness::new(Limits::default());
    test.writer(A);
    test.writer(B);
    test.batch([
        append(A, 1, 1, &[b"retained"], 1),
        append(B, 1, 1, &[b"trimmed"], 1),
    ]);
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    let mixed = pack_files(test.dir.path()).pop().unwrap();
    // A sparse tail supplies the same physical file-length input without writing
    // tens of megabytes of payloads in this regression.
    OpenOptions::new()
        .write(true)
        .open(&mixed)
        .unwrap()
        .set_len(2 * wal::SEGMENT_BYTES)
        .unwrap();
    test.send(trim(B, 1, 1));
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    assert!(
        mixed.exists(),
        "the first rotation still indexes the retained record"
    );
    test.engine.wal.rotate(&test.engine.streams).unwrap();
    assert!(
        !mixed.exists(),
        "excess discarded bytes still pin the mixed pack"
    );
    assert_eq!(test.send(read(A, 1)), page(1, 1, &[(1, b"retained")]));
}

struct Identified(Arc<HashMap<KeeperId, Keeper>>, Identity);
impl Transport for Identified {
    fn identity(&self) -> &Identity {
        &self.1
    }

    fn call(&self, keeper: KeeperId, request: Request) -> BoxFuture<'_, CallResult> {
        Box::pin(async move {
            self.0
                .get(&keeper)
                .ok_or(TransportError::Unreachable)?
                .call(&self.1, request)
                .await
        })
    }
}

#[tokio::test]
async fn writers_on_durable_keepers_conform_to_the_journal_contract() {
    use journal_contract::conformance;

    let directories: Vec<_> = (0..3).map(|_| tempdir().unwrap()).collect();
    let limits = Limits {
        max_record_bytes: conformance::LIMITS.max_record_bytes.try_into().unwrap(),
        stream_quota_bytes: conformance::LIMITS.stream_quota_bytes,
        ..Limits::default()
    };
    let keepers = Arc::new(
        MEMBERS
            .into_iter()
            .zip(&directories)
            .map(|(id, dir)| (id, Keeper::open(dir.path(), id, limits).unwrap()))
            .collect::<HashMap<_, _>>(),
    );
    conformance::run(|identity| {
        Arc::new(
            crate::stream::writer::Writer::new(
                Arc::new(Identified(keepers.clone(), identity)),
                MEMBERS,
            )
            .unwrap(),
        )
    })
    .await;
}
