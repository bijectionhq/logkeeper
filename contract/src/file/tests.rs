use super::*;
use crate::{
    JournalError::*,
    Page,
    test_support::{Scratch, block_on, panics_at},
};
use bytes::BytesMut;

const LIMITS: Limits = Limits {
    max_record_bytes: 4,
    stream_quota_bytes: 8,
};
const LIVE: StreamId = StreamId(1);
const DEAD: StreamId = StreamId(2);
const OWNER: Identity = Identity::from_static("urn:logkeeper:client:10");
const OTHER: Identity = Identity::from_static("urn:logkeeper:client:11");
const EPOCH: Epoch = Epoch(0);
const LIVE_RECOVERY: &str = "recovery preserves committed data and trim";
const SEAL_RECOVERY: &str = "recovery preserves sealed identity";
const DELETE_RECOVERY: &str = "recovery preserves tombstone";
const BEFORE_SYNC: &str = "durability precedes acknowledgement";

fn bytes(data: &'static [u8]) -> Bytes {
    Bytes::from_static(data)
}

#[test]
fn refuses_numeric_identity_frames() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    {
        let journal = FileJournal::open(&path, LIMITS).unwrap();
        block_on(journal.handle(OWNER).create(LIVE)).unwrap();
    }
    let mut body = BytesMut::new();
    body.put_u8(1);
    body.put_u128_le(LIVE.0);
    body.put_u64_le(EPOCH.0);
    body.put_u128_le(10);
    let mut frame = BytesMut::new();
    frame.put_u64_le(body.len() as u64);
    frame.put_u64_le(!(body.len() as u64));
    frame.put_u32_le(crc32(&[&body]));
    frame.put_slice(&body);
    OpenOptions::new()
        .append(true)
        .open(&path)
        .unwrap()
        .write_all(&frame)
        .unwrap();

    assert!(
        matches!(
            FileJournal::open(&path, LIMITS),
            Err(error) if error.kind() == io::ErrorKind::InvalidData
        ),
        "reference journal accepted an obsolete numeric identity frame"
    );
}

async fn populate(journal: &FileJournal) {
    let a = journal.handle(OWNER);
    a.create(LIVE).await.unwrap();
    a.seal(LIVE, EPOCH).await.unwrap();
    a.append(LIVE, EPOCH, Lsn(1), bytes(b"aaaa")).await.unwrap();
    a.append(LIVE, EPOCH, Lsn(2), bytes(b"bbbb")).await.unwrap();
    a.trim(LIVE, EPOCH, Lsn(1)).await.unwrap();
    a.append(LIVE, EPOCH, Lsn(3), bytes(b"cccc")).await.unwrap();
    a.create(DEAD).await.unwrap();
    a.delete(DEAD).await.unwrap();
}

async fn check_live(journal: &FileJournal) {
    let a = journal.handle(OWNER);
    assert_eq!(a.head(LIVE).await, Ok(Lsn(3)), "{LIVE_RECOVERY}");
    assert_eq!(
        a.read(LIVE, Lsn(1), 4, std::time::Duration::ZERO).await,
        Err(Trimmed { floor: Lsn(2) }),
        "{LIVE_RECOVERY}"
    );
    assert_eq!(
        a.read(LIVE, Lsn(2), usize::MAX, std::time::Duration::ZERO)
            .await,
        Ok(Page {
            floor: Lsn(2),
            head: Lsn(3),
            records: vec![(Lsn(2), bytes(b"bbbb")), (Lsn(3), bytes(b"cccc"))],
            recoveries: Vec::new(),
        }),
        "{LIVE_RECOVERY}"
    );
    assert_eq!(
        a.append(LIVE, EPOCH, Lsn(3), bytes(b"cccc")).await,
        Ok(Lsn(3)),
        "{LIVE_RECOVERY}"
    );
    assert_eq!(
        a.append(LIVE, EPOCH, Lsn(4), bytes(b"d")).await,
        Err(Full { floor: Lsn(2) }),
        "{LIVE_RECOVERY}"
    );
}

async fn check_seal(journal: &FileJournal) {
    let b = journal.handle(OTHER);
    assert_eq!(
        b.seal(LIVE, EPOCH).await,
        Err(Fenced { current: EPOCH }),
        "{SEAL_RECOVERY}"
    );
}

async fn check_delete(journal: &FileJournal) {
    let b = journal.handle(OTHER);
    assert_eq!(b.create(DEAD).await, Err(Deleted), "{DELETE_RECOVERY}");
}

#[test]
fn replays_every_mutation() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    block_on(populate(&FileJournal::open(&path, LIMITS).unwrap()));
    let reopened = FileJournal::open(&path, LIMITS).unwrap();
    block_on(async {
        check_live(&reopened).await;
        check_seal(&reopened).await;
        check_delete(&reopened).await;
    });
}

#[test]
fn rejects_lost_committed_frame() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    let journal = FileJournal::open(&path, LIMITS).unwrap();
    block_on(populate(&journal));
    drop(journal);
    let lost =
        (FRAME_HEADER_LEN + STREAM_MUTATION_LEN) * 2 + FRAME_HEADER_LEN + APPEND_MUTATION_LEN + 4;
    let file = OpenOptions::new().write(true).open(&path).unwrap();
    // Keep the prefix through trim and remove the subsequent durable append.
    file.set_len(file.metadata().unwrap().len() - lost).unwrap();
    panics_at(LIVE_RECOVERY, || {
        block_on(check_live(&FileJournal::open(&path, LIMITS).unwrap()));
    });
}

#[test]
fn rejects_lost_seal_identity() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    {
        let journal = FileJournal::open(&path, LIMITS).unwrap();
        let a = journal.handle(OWNER);
        block_on(a.create(LIVE)).unwrap();
    }
    panics_at(SEAL_RECOVERY, || {
        block_on(check_seal(&FileJournal::open(&path, LIMITS).unwrap()));
    });
}

#[test]
fn rejects_lost_tombstone() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    block_on(populate(&FileJournal::open(&path, LIMITS).unwrap()));
    let file = OpenOptions::new().write(true).open(&path).unwrap();
    file.set_len(file.metadata().unwrap().len() - FRAME_HEADER_LEN - STREAM_MUTATION_LEN)
        .unwrap();
    panics_at(DELETE_RECOVERY, || {
        block_on(check_delete(&FileJournal::open(&path, LIMITS).unwrap()));
    });
}

#[test]
fn cuts_each_partial_append_frame_and_can_append_again() {
    let scratch = Scratch::new();
    let path = scratch.path().join("source");
    let prefix_len;
    {
        let journal = FileJournal::open(&path, LIMITS).unwrap();
        let a = journal.handle(OWNER);
        block_on(async {
            a.create(LIVE).await.unwrap();
            a.seal(LIVE, EPOCH).await.unwrap();
            a.append(LIVE, EPOCH, Lsn(1), bytes(b"a")).await.unwrap();
        });
        prefix_len = std::fs::metadata(&path).unwrap().len() as usize;
        block_on(a.append(LIVE, EPOCH, Lsn(2), bytes(b"tail"))).unwrap();
    }

    let contents = std::fs::read(&path).unwrap();
    let path = scratch.path().join("partial");
    for cut in prefix_len..contents.len() {
        std::fs::write(&path, &contents[..cut]).unwrap();
        {
            let journal = FileJournal::open(&path, LIMITS).unwrap();
            assert_eq!(
                std::fs::metadata(&path).unwrap().len() as usize,
                prefix_len,
                "cut at {cut}"
            );
            let a = journal.handle(OWNER);
            assert_eq!(block_on(a.head(LIVE)), Ok(Lsn(1)), "cut at {cut}");
            block_on(a.append(LIVE, EPOCH, Lsn(2), bytes(b"new"))).unwrap();
        }
        let journal = FileJournal::open(&path, LIMITS).unwrap();
        let a = journal.handle(OWNER);
        assert_eq!(
            block_on(a.append(LIVE, EPOCH, Lsn(2), bytes(b"new"))),
            Ok(Lsn(2)),
            "cut at {cut}"
        );
    }
}

#[test]
fn rejects_complete_corruption_and_changed_limits() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    block_on(populate(&FileJournal::open(&path, LIMITS).unwrap()));
    let changed = Limits {
        stream_quota_bytes: 9,
        ..LIMITS
    };
    assert_eq!(
        FileJournal::open(&path, changed).err().unwrap().kind(),
        io::ErrorKind::InvalidData
    );
    let mut contents = std::fs::read(&path).unwrap();
    *contents.last_mut().unwrap() ^= 1;
    std::fs::write(&path, &contents).unwrap();
    assert_eq!(
        FileJournal::open(&path, LIMITS).err().unwrap().kind(),
        io::ErrorKind::InvalidData
    );
    assert_eq!(std::fs::read(&path).unwrap(), contents);
}

#[test]
fn keeps_exclusive_lock_until_last_handle_is_dropped() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    let journal = FileJournal::open(&path, LIMITS).unwrap();
    let handle = journal.handle(OWNER);
    drop(journal);
    assert_eq!(
        FileJournal::open(&path, LIMITS).err().unwrap().kind(),
        io::ErrorKind::WouldBlock
    );
    drop(handle);
    assert!(FileJournal::open(&path, LIMITS).is_ok());
}

fn sync_failure_fixture(path: &Path, sync: fn(&File) -> io::Result<()>) {
    let journal = FileJournal::open(path, LIMITS).unwrap();
    let a = journal.handle(OWNER);
    block_on(async {
        a.create(LIVE).await.unwrap();
        a.seal(LIVE, EPOCH).await.unwrap();
    });
    drop(a);
    drop(journal);

    let (mut storage, state) = Storage::open(path, LIMITS).unwrap();
    storage.sync = sync;
    let journal = FileJournal(Arc::new(Engine::new(state, Some(storage))));
    let a = journal.handle(OWNER);
    block_on(async {
        assert_eq!(
            a.append(LIVE, EPOCH, Lsn(1), bytes(b"a")).await,
            Err(Unavailable),
            "{BEFORE_SYNC}"
        );
        assert_eq!(a.head(LIVE).await, Err(Unavailable), "{BEFORE_SYNC}");
        assert_eq!(
            a.append(LIVE, EPOCH, Lsn(1), bytes(b"a")).await,
            Err(Unavailable),
            "{BEFORE_SYNC}"
        );
    });
}

#[test]
fn fails_closed_after_sync_error() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    sync_failure_fixture(&path, |_| Err(io::Error::other("simulated sync failure")));
    let reopened = FileJournal::open(&path, LIMITS).unwrap();
    let a = reopened.handle(OWNER);
    // A complete write with a failed sync can take effect on recovery.
    assert_eq!(
        block_on(a.append(LIVE, EPOCH, Lsn(1), bytes(b"a"))),
        Ok(Lsn(1))
    );
}

#[test]
fn rejects_ack_without_sync() {
    let scratch = Scratch::new();
    let path = scratch.path().join("journal");
    panics_at(BEFORE_SYNC, || sync_failure_fixture(&path, |_| Ok(())));
}
