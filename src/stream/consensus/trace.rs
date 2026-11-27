//! Test-only observation of one fault-harness cluster, including its WAL threads.

use std::{
    collections::HashMap,
    io::{self, Write},
    path::{Path, PathBuf},
    sync::{Arc, LazyLock, Weak},
    time::Instant,
};

use journal_contract::StreamId;
use openraft::EntryPayload;
use parking_lot::Mutex;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{Entry, LogId, Vote, Voters, authority, state::Command, storage::Record};

#[derive(Clone)]
pub(super) struct Capture(Arc<Mutex<Vec<Value>>>);

type Registry = Mutex<HashMap<PathBuf, Weak<Mutex<Vec<Value>>>>>;
static CAPTURES: LazyLock<Registry> = LazyLock::new(Registry::default);

impl Capture {
    pub fn new() -> Self {
        Self(Arc::default())
    }

    pub fn register(&self, root: &Path) -> Registration {
        let root = root.canonicalize().expect("trace cluster directory");
        let previous = CAPTURES
            .lock()
            .insert(root.clone(), Arc::downgrade(&self.0));
        assert!(previous.is_none(), "trace cluster already registered");
        Registration(root)
    }

    pub fn write(&self, out: &mut impl Write) -> io::Result<()> {
        for event in self.0.lock().iter() {
            serde_json::to_writer(&mut *out, event)?;
            writeln!(out)?;
        }
        Ok(())
    }
}

pub(super) struct Registration(PathBuf);

impl Drop for Registration {
    fn drop(&mut self) {
        CAPTURES.lock().remove(&self.0);
    }
}

#[derive(Clone)]
pub(super) struct Node {
    capture: Capture,
    id: Uuid,
}

impl Node {
    pub fn open(data: &Path, id: Uuid, incarnation: Uuid) -> Option<Self> {
        let capture = Capture(CAPTURES.lock().get(data.parent()?)?.upgrade()?);
        let node = Self { capture, id };
        node.event("Media", StreamId(0), json!({"incarnation": incarnation}));
        Some(node)
    }

    pub fn event(&self, kind: &str, stream: StreamId, data: Value) {
        self.batch([event(kind, stream, data)]);
    }

    pub fn batch(&self, events: impl IntoIterator<Item = Value>) {
        let mut trace = self.capture.0.lock();
        for mut event in events {
            event["node"] = json!(self.id);
            trace.push(event);
        }
    }
}

pub(super) fn event(kind: &str, stream: StreamId, data: Value) -> Value {
    json!({"kind": kind, "stream": format!("{:032x}", stream.0), "data": data})
}

/// Keep full terms without overflowing TLC's signed 32-bit integers.
/// Each big-endian digit fits in an ordinary TLC integer.
fn term(n: u64) -> [u16; 4] {
    [48, 32, 16, 0].map(|shift| (n >> shift) as u16)
}

pub(super) fn cut(id: Option<LogId>) -> Value {
    id.map_or_else(
        || json!({"index": 0, "term": term(0)}),
        |id| json!({"index": id.index + 1, "term": term(id.leader_id.term)}),
    )
}

pub(super) fn vote(vote: Vote) -> Value {
    json!({
        "term": term(vote.leader_id().term),
        "votedFor": Uuid::from_u128(vote.leader_id().voted_for),
        "committed": vote.is_committed(),
    })
}

pub(super) fn entry(
    id: LogId,
    payload: &EntryPayload<Command, openraft::Membership<super::NodeId, openraft::BasicNode>>,
) -> Value {
    let bytes = match payload {
        EntryPayload::Normal(command) => bincode::serialize(&(1u32, command.body())),
        other => bincode::serialize(other),
    }
    .expect("encode trace entry");
    json!({"cut": cut(Some(id)), "digest": format!("{:x}", Sha256::digest(bytes))})
}

pub(super) fn wal(record: &Record) -> Option<Value> {
    let entries = |entries: &[Entry]| {
        entries
            .iter()
            .map(|e| entry(e.log_id, &e.payload))
            .collect::<Vec<_>>()
    };
    Some(match record {
        Record::Owned(_, record) => return wal(record),
        Record::Register(genesis) => event("Register", genesis.stream, json!({})),
        Record::Vote(stream, saved) => event("Vote", *stream, vote(*saved)),
        Record::Append(stream, batch) if !batch.is_empty() => {
            event("Append", *stream, json!({"entries": entries(batch)}))
        }
        Record::Recover(stream, saved, batch) => event(
            "Recover",
            *stream,
            json!({
                "vote": vote(*saved), "entries": entries(batch),
                "exact": batch.iter().any(|entry| matches!(&entry.payload,
                    EntryPayload::Normal(Command::RecoverRecorded { exact: true, .. }))),
            }),
        ),
        Record::Truncate(stream, from) => event("Truncate", *stream, json!({"from": from + 1})),
        Record::Snapshot(stream, selected) => {
            event("Snapshot", *stream, cut(Some(selected.log_id)))
        }
        Record::Purge(stream, id) => event("Purge", *stream, cut(Some(*id))),
        Record::Committed(stream, id) => event("DurableCommit", *stream, cut(Some(*id))),
        _ => return None,
    })
}

pub(super) fn voters(voters: Voters) -> Vec<Uuid> {
    voters.into_iter().collect()
}

pub(super) fn catalog(change: &authority::Change, at: u64) -> Value {
    use authority::Change;
    let nil = Uuid::nil();
    match change {
        Change::Enroll {
            keeper,
            incarnation,
        } => event(
            "Enroll",
            StreamId(0),
            json!({"at": at, "keeper": keeper, "incarnation": incarnation}),
        ),
        Change::Fence { keeper } => {
            event("Fence", StreamId(0), json!({"at": at, "keeper": keeper}))
        }
        Change::Lease {
            keeper,
            lease_ms,
            margin_ms,
        } => event(
            "LeasePolicy",
            StreamId(0),
            json!({"at": at, "keeper": keeper, "duration": lease_ms, "margin": margin_ms}),
        ),
        Change::Recover {
            stage,
            dead,
            record,
        }
        | Change::RecoverFrom {
            stage,
            dead,
            record,
            ..
        } => {
            let writer = match change {
                Change::RecoverFrom { writer, .. } => *writer,
                _ => nil,
            };
            event(
                "RecoveryTransaction",
                stage.stream,
                json!({
                    "at": at, "old": voters(stage.old), "target": voters(stage.target),
                    "sourceRevision": stage.source, "epoch": record.epoch,
                    "loss": record.loss_point.0, "dead": dead, "writer": writer,
                }),
            )
        }
    }
}

pub(super) fn measured_ms(start: Instant) -> u128 {
    start.elapsed().as_millis()
}
