//! The keeper's authenticated-history ledger for writer-driven streams.
//!
//! Each stream has an append-only file of the leaves of its committed records,
//! from LSN 1, kept beside the WAL in `DATA/authenticated/`. It is derived data:
//! a leaf is appended only for a record at or below the keeper's head, which is
//! committed and immutable, so every keeper holding a record derives the same
//! leaf. The ledger never changes the keeper's stream state or WAL, and the
//! keeper signs a head only after recomputing its root from its own leaves.
//!
//! The leaves of retained records can be recomputed after a crash, so ordinary
//! ingestion does not sync. A trim is decided only after the leaves it discards
//! are durable. A keeper that never held a prefix (a replacement, or a lagging
//! keeper that synced past a trimmed prefix) has a gap below its floor. It can
//! sign again once a client seeds the missing leaves together with a head that
//! two other keepers signed and that the keeper's own records extend.
//! Design: `verification/writer-driven-authenticated.md`.

use std::{
    collections::HashMap,
    fs::{self, File, OpenOptions},
    io::{self, BufReader, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::Bytes;
use sha2::{Digest, Sha256};

use super::{
    durability::{sync_data, sync_directory},
    state::{ExtentReader, Stream},
};
use crate::stream::{
    authenticated::{
        Frontier, Hash, Head, KeeperKeys, Leaf, SignedHead, Signer, Timing, Tree,
        protocol::{self, AuthReply, AuthRequest, LEAF_PAGE},
    },
    wire::*,
};

/// The operator-installed signing key of this keeper and the fleet's key set.
pub struct Authentication {
    pub signer: Signer,
    pub keys: Arc<KeeperKeys>,
}

const DIRECTORY: &str = "authenticated";
const LEAF_BYTES: usize = 129;
const RECORD_BYTES: usize = 4 + LEAF_BYTES;

pub(super) struct Ledger {
    directory: PathBuf,
    signer: Signer,
    keys: Arc<KeeperKeys>,
    chains: HashMap<StreamId, Chain>,
    seeds: HashMap<StreamId, Seeding>,
}

/// The leaves `1..=ingested` of one stream. The file is opened per use, so a
/// keeper with many streams holds no descriptor per stream.
struct Chain {
    path: PathBuf,
    ingested: u64,
    frontier: Frontier,
    dirty: bool,
}

/// Seeded leaves `first..next` staged in memory order on disk, not yet verified.
struct Seeding {
    path: PathBuf,
    file: File,
    next: u64,
    frontier: Frontier,
}

impl Ledger {
    pub(super) fn open(data: &Path, authentication: Authentication) -> io::Result<Self> {
        if authentication.signer.journal() != authentication.keys.journal
            || !authentication.keys.valid()
        {
            return Err(invalid(
                "the history signer and key set name different journals",
            ));
        }
        let directory = data.join(DIRECTORY);
        if !directory.is_dir() {
            fs::create_dir_all(&directory)?;
            sync_directory(data)?;
        }
        // Unverified seeds do not survive a restart. The client starts them again.
        for entry in fs::read_dir(&directory)? {
            let path = entry?.path();
            if path
                .extension()
                .is_some_and(|extension| extension == "seed")
            {
                fs::remove_file(path)?;
            }
        }
        Ok(Self {
            directory,
            signer: authentication.signer,
            keys: authentication.keys,
            chains: HashMap::new(),
            seeds: HashMap::new(),
        })
    }

    /// Append the leaves of newly committed records, up to `through` and the
    /// keeper's head. Stops at a gap below the floor.
    pub(super) fn ingest(
        &mut self,
        id: StreamId,
        state: &Stream,
        reader: &mut ExtentReader,
        through: u64,
    ) -> io::Result<()> {
        if state.deleted {
            return Ok(());
        }
        let chain = chain(&mut self.chains, &self.directory, id, state)?;
        let limit = through.min(state.view.head.0);
        let mut bytes = Vec::new();
        while chain.ingested < limit {
            let at = chain.ingested + 1;
            if at < state.view.floor.0 {
                break;
            }
            let leaf = leaf_of(state, id, Lsn(at), reader)?;
            bytes.extend_from_slice(&encode_leaf(&leaf));
            chain.frontier.push(leaf.hash());
            chain.ingested = at;
        }
        if !bytes.is_empty() {
            if let Err(error) = append(&chain.path, &bytes) {
                // The file may hold a torn suffix. Reload it before the next use.
                self.chains.remove(&id);
                return Err(error);
            }
            chain.dirty = true;
        }
        Ok(())
    }

    /// Make every leaf a trim through `through` discards durable before the trim
    /// is decided. A keeper with a gap trims without them; it already needs a seed.
    pub(super) fn prepare_trim(
        &mut self,
        id: StreamId,
        state: &Stream,
        through: Lsn,
        reader: &mut ExtentReader,
    ) -> io::Result<()> {
        self.ingest(id, state, reader, through.0)?;
        let chain = chain(&mut self.chains, &self.directory, id, state)?;
        if chain.dirty {
            sync_data(&File::open(&chain.path)?)?;
            chain.dirty = false;
        }
        Ok(())
    }

    /// Forget a deleted stream's ledger.
    pub(super) fn remove(&mut self, id: StreamId) {
        self.chains.remove(&id);
        self.seeds.remove(&id);
        for extension in ["leaves", "seed"] {
            let _ = fs::remove_file(self.directory.join(file_name(id, extension)));
        }
    }

    pub(super) fn answer(
        &mut self,
        id: StreamId,
        state: Option<&Stream>,
        body: &[u8],
        reader: &mut ExtentReader,
    ) -> io::Result<Reply> {
        let Ok(request) = protocol::decode::<AuthRequest>(body) else {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        };
        let Some(state) = state else {
            return Ok(Reply::Refused(Refusal::NotFound));
        };
        if state.deleted {
            return Ok(Reply::Refused(Refusal::Deleted));
        }
        self.ingest(id, state, reader, u64::MAX)?;
        let view = &state.view;
        let floor = view.floor;
        let head = view.head;
        let ingested = chain(&mut self.chains, &self.directory, id, state)?.ingested;
        let missing = AuthReply::Missing { ingested, floor };
        let reply = match request {
            AuthRequest::Status => AuthReply::Status {
                ingested,
                floor,
                complete: ingested + 1 >= floor.0,
            },
            AuthRequest::Sign { size } => {
                if view.learner || !view.ensemble.contains(&self.signer.keeper()) {
                    return Ok(Reply::Refused(Refusal::NotSynced));
                }
                if size > head.0 {
                    return Ok(Reply::Refused(Refusal::AboveHead { head }));
                }
                match self.root(id, state, size)? {
                    None => missing,
                    Some(root) => {
                        let head = Head {
                            journal: self.signer.journal(),
                            stream: id,
                            size,
                            root,
                            ensemble: view.ensemble,
                        };
                        AuthReply::Signed {
                            head,
                            signature: self.signer.sign(&head),
                        }
                    }
                }
            }
            AuthRequest::Leaves { from, through } => {
                if from.0 == 0 || from > head {
                    return Ok(Reply::Refused(Refusal::AboveHead { head }));
                }
                if from.0 > ingested {
                    missing
                } else {
                    let end = through
                        .min(head.0)
                        .min(ingested)
                        .min(from.0 + LEAF_PAGE as u64 - 1);
                    let path = &chain(&mut self.chains, &self.directory, id, state)?.path;
                    AuthReply::Leaves(read_leaves(path, id, from.0, end)?)
                }
            }
            AuthRequest::Path { at, size } => {
                if at.0 == 0 || at.0 > size || size > head.0 {
                    return Ok(Reply::Refused(Refusal::AboveHead { head }));
                }
                match self.tree(id, state, size)? {
                    None => missing,
                    Some(tree) => match (tree.leaf(at), tree.inclusion(at, size)) {
                        (Some(leaf), Ok(path)) => AuthReply::Path { leaf: *leaf, path },
                        _ => return Ok(Reply::Refused(Refusal::AboveHead { head })),
                    },
                }
            }
            AuthRequest::Consistency { earlier, later } => {
                if earlier > later || later > head.0 {
                    return Ok(Reply::Refused(Refusal::AboveHead { head }));
                }
                match self.tree(id, state, later)? {
                    None => missing,
                    Some(tree) => match tree.consistency(earlier, later) {
                        Ok(path) => AuthReply::Consistency(path),
                        Err(_) => return Ok(Reply::Refused(Refusal::AboveHead { head })),
                    },
                }
            }
            AuthRequest::Seed { from, leaves, head } => {
                match self.seed(id, state, reader, from, leaves, head)? {
                    Ok(reply) => reply,
                    Err(refusal) => return Ok(Reply::Refused(refusal)),
                }
            }
        };
        Ok(Reply::Authenticated(protocol::encode(&reply)?))
    }

    /// The root of the committed prefix through `size`, or `None` across a gap.
    fn root(&mut self, id: StreamId, state: &Stream, size: u64) -> io::Result<Option<Hash>> {
        let chain = chain(&mut self.chains, &self.directory, id, state)?;
        if size == chain.ingested {
            return Ok(Some(chain.frontier.root()));
        }
        if size > chain.ingested {
            return Ok(None);
        }
        let mut frontier = Frontier::default();
        for leaf in read_leaves(&chain.path, id, 1, size)? {
            frontier.push(leaf.hash());
        }
        Ok(Some(frontier.root()))
    }

    fn tree(&mut self, id: StreamId, state: &Stream, size: u64) -> io::Result<Option<Tree>> {
        let chain = chain(&mut self.chains, &self.directory, id, state)?;
        if size > chain.ingested {
            return Ok(None);
        }
        let mut tree = Tree::default();
        tree.extend(read_leaves(&chain.path, id, 1, size)?)
            .map_err(|_| invalid("damaged authenticated ledger"))?;
        Ok(Some(tree))
    }

    fn seed(
        &mut self,
        id: StreamId,
        state: &Stream,
        reader: &mut ExtentReader,
        from: Lsn,
        leaves: Vec<Leaf>,
        signed: Option<SignedHead>,
    ) -> io::Result<Result<AuthReply, Refusal>> {
        let floor = state.view.floor.0;
        let local_head = state.view.head.0;
        let chain = chain(&mut self.chains, &self.directory, id, state)?;
        let ingested = chain.ingested;
        if ingested + 1 >= floor {
            if let Some(seeding) = self.seeds.remove(&id) {
                let _ = fs::remove_file(seeding.path);
            }
            return Ok(Ok(AuthReply::Seeded { ingested }));
        }
        if from.0 == ingested + 1 {
            let path = self.directory.join(file_name(id, "seed"));
            let file = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(&path)?;
            self.seeds.insert(
                id,
                Seeding {
                    path,
                    file,
                    next: ingested + 1,
                    frontier: chain.frontier.clone(),
                },
            );
        }
        let Some(seeding) = self.seeds.get_mut(&id) else {
            return Ok(Err(Refusal::Gap {
                head: Lsn(ingested),
            }));
        };
        if from.0 != seeding.next {
            return Ok(Err(Refusal::Gap {
                head: Lsn(seeding.next - 1),
            }));
        }
        let mut bytes = Vec::with_capacity(leaves.len() * RECORD_BYTES);
        let mut frontier = seeding.frontier.clone();
        let mut next = seeding.next;
        for leaf in &leaves {
            if leaf.stream != id || leaf.at.0 != next || next >= floor || !leaf.valid() {
                self.abandon(id);
                return Ok(Err(Refusal::Conflict {
                    head: Lsn(ingested),
                }));
            }
            bytes.extend_from_slice(&encode_leaf(leaf));
            frontier.push(leaf.hash());
            next += 1;
        }
        seeding.file.write_all(&bytes)?;
        seeding.frontier = frontier;
        seeding.next = next;
        let Some(signed) = signed else {
            return Ok(Ok(AuthReply::Seeded { ingested }));
        };

        // Install only leaves that two keepers' signed root and this keeper's
        // own retained records confirm.
        let size = signed.head.size;
        if seeding.next != floor
            || signed.head.stream != id
            || signed.head.journal != self.signer.journal()
            || size + 1 < floor
            || size > local_head
            || signed.verify(&self.keys).is_err()
        {
            self.abandon(id);
            return Ok(Err(Refusal::Conflict {
                head: Lsn(ingested),
            }));
        }
        let mut extended = seeding.frontier.clone();
        for at in floor..=size {
            extended.push(leaf_of(state, id, Lsn(at), reader)?.hash());
        }
        if extended.root() != signed.head.root {
            self.abandon(id);
            return Ok(Err(Refusal::Conflict {
                head: Lsn(ingested),
            }));
        }
        let seeding = self.seeds.remove(&id).expect("staged seed");
        sync_data(&seeding.file)?;
        let mut staged = Vec::new();
        File::open(&seeding.path)?.read_to_end(&mut staged)?;
        let chain = chain_mut(&mut self.chains, id)?;
        if let Err(error) =
            append(&chain.path, &staged).and_then(|()| sync_data(&File::open(&chain.path)?))
        {
            self.chains.remove(&id);
            return Err(error);
        }
        chain.frontier = seeding.frontier;
        chain.ingested = floor - 1;
        chain.dirty = false;
        let _ = fs::remove_file(&seeding.path);
        self.ingest(id, state, reader, u64::MAX)?;
        let ingested = chain_mut(&mut self.chains, id)?.ingested;
        Ok(Ok(AuthReply::Seeded { ingested }))
    }

    fn abandon(&mut self, id: StreamId) {
        if let Some(seeding) = self.seeds.remove(&id) {
            let _ = fs::remove_file(seeding.path);
        }
    }
}

fn file_name(id: StreamId, extension: &str) -> String {
    format!("{:032x}.{extension}", id.0)
}

fn chain_mut(chains: &mut HashMap<StreamId, Chain>, id: StreamId) -> io::Result<&mut Chain> {
    chains
        .get_mut(&id)
        .ok_or_else(|| invalid("authenticated ledger is not loaded"))
}

/// Load a stream's chain on first use. A torn or damaged suffix is cut, and
/// leaves above the keeper's head are dropped; both are recomputed from
/// retained records or, below the floor, seeded again.
fn chain<'a>(
    chains: &'a mut HashMap<StreamId, Chain>,
    directory: &Path,
    id: StreamId,
    state: &Stream,
) -> io::Result<&'a mut Chain> {
    if !chains.contains_key(&id) {
        let path = directory.join(file_name(id, "leaves"));
        let created = !path.exists();
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)?;
        if created {
            sync_directory(directory)?;
        }
        let mut frontier = Frontier::default();
        let mut ingested = 0;
        let length = file.metadata()?.len();
        {
            let mut reader = BufReader::new(&mut file);
            let mut record = [0; RECORD_BYTES];
            while (ingested + 1) * (RECORD_BYTES as u64) <= length && ingested < state.view.head.0 {
                reader.read_exact(&mut record)?;
                let Some(leaf) = decode_leaf(id, &record).filter(|leaf| leaf.at.0 == ingested + 1)
                else {
                    break;
                };
                frontier.push(leaf.hash());
                ingested += 1;
            }
        }
        let kept = ingested * RECORD_BYTES as u64;
        if kept != length {
            file.set_len(kept)?;
        }
        chains.insert(
            id,
            Chain {
                path,
                ingested,
                frontier,
                dirty: kept != length,
            },
        );
    }
    chain_mut(chains, id)
}

fn append(path: &Path, bytes: &[u8]) -> io::Result<()> {
    OpenOptions::new().append(true).open(path)?.write_all(bytes)
}

fn read_leaves(path: &Path, id: StreamId, from: u64, through: u64) -> io::Result<Vec<Leaf>> {
    if from == 0 || from > through {
        return Ok(Vec::new());
    }
    let mut file = File::open(path)?;
    file.seek(SeekFrom::Start((from - 1) * RECORD_BYTES as u64))?;
    let mut reader = BufReader::new(file);
    let mut record = [0; RECORD_BYTES];
    let mut leaves = Vec::with_capacity((through - from + 1).min(LEAF_PAGE as u64) as usize);
    for at in from..=through {
        reader.read_exact(&mut record)?;
        let leaf = decode_leaf(id, &record)
            .filter(|leaf| leaf.at.0 == at)
            .ok_or_else(|| invalid("damaged authenticated ledger"))?;
        leaves.push(leaf);
    }
    Ok(leaves)
}

/// The leaf of the retained committed record at `at`.
fn leaf_of(state: &Stream, id: StreamId, at: Lsn, reader: &mut ExtentReader) -> io::Result<Leaf> {
    let record = state
        .record(at)
        .ok_or_else(|| invalid("missing retained record for its leaf"))?;
    if record.timed {
        let (evidence, _) = record.original(reader, id, at)?;
        let original = evidence.origin.original;
        return Ok(Leaf {
            stream: id,
            at,
            writer_epoch: record.epoch,
            payload_sha256: original.payload_sha256,
            timing: Some(Timing {
                exclusive_cutoff_micros: original.exclusive_journal_cutoff_micros,
                receiver_certificate_sha256: original.original_receiver_certificate_sha256,
                quorum_sync_upper_micros: evidence.quorum_upper_micros(),
                evidence_sha256: evidence.digest(),
            }),
        });
    }
    let payload: Bytes = record.read(reader)?;
    Ok(Leaf {
        stream: id,
        at,
        writer_epoch: record.epoch,
        payload_sha256: Sha256::digest(&payload).into(),
        timing: None,
    })
}

fn encode_leaf(leaf: &Leaf) -> [u8; RECORD_BYTES] {
    let mut record = [0; RECORD_BYTES];
    let body = &mut record[4..];
    body[..8].copy_from_slice(&leaf.at.0.to_be_bytes());
    body[8..16].copy_from_slice(&leaf.writer_epoch.0.to_be_bytes());
    body[16..48].copy_from_slice(&leaf.payload_sha256);
    if let Some(timing) = leaf.timing {
        body[48] = 1;
        body[49..57].copy_from_slice(&timing.exclusive_cutoff_micros.to_be_bytes());
        body[57..89].copy_from_slice(&timing.receiver_certificate_sha256);
        body[89..97].copy_from_slice(&timing.quorum_sync_upper_micros.to_be_bytes());
        body[97..129].copy_from_slice(&timing.evidence_sha256);
    }
    let crc = crc32fast::hash(&record[4..]);
    record[..4].copy_from_slice(&crc.to_be_bytes());
    record
}

fn decode_leaf(stream: StreamId, record: &[u8; RECORD_BYTES]) -> Option<Leaf> {
    let body = &record[4..];
    if crc32fast::hash(body).to_be_bytes() != record[..4] {
        return None;
    }
    let field = |range: std::ops::Range<usize>| -> [u8; 8] { body[range].try_into().unwrap() };
    let hash = |range: std::ops::Range<usize>| -> Hash { body[range].try_into().unwrap() };
    let timing = match body[48] {
        0 if body[49..].iter().all(|byte| *byte == 0) => None,
        1 => Some(Timing {
            exclusive_cutoff_micros: i64::from_be_bytes(field(49..57)),
            receiver_certificate_sha256: hash(57..89),
            quorum_sync_upper_micros: i64::from_be_bytes(field(89..97)),
            evidence_sha256: hash(97..129),
        }),
        _ => return None,
    };
    let leaf = Leaf {
        stream,
        at: Lsn(u64::from_be_bytes(field(0..8))),
        writer_epoch: Epoch(u64::from_be_bytes(field(8..16))),
        payload_sha256: hash(16..48),
        timing,
    };
    leaf.valid().then_some(leaf)
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ledger_records_round_trip_and_reject_damage() {
        let stream = StreamId(9);
        let ordinary = Leaf {
            stream,
            at: Lsn(3),
            writer_epoch: Epoch(2),
            payload_sha256: [5; 32],
            timing: None,
        };
        let timed = Leaf {
            timing: Some(Timing {
                exclusive_cutoff_micros: 10,
                receiver_certificate_sha256: [6; 32],
                quorum_sync_upper_micros: 9,
                evidence_sha256: [7; 32],
            }),
            ..ordinary
        };
        for leaf in [ordinary, timed] {
            let mut record = encode_leaf(&leaf);
            assert_eq!(decode_leaf(stream, &record), Some(leaf));
            record[RECORD_BYTES - 1] ^= 1;
            assert_eq!(decode_leaf(stream, &record), None);
        }
        assert_eq!(RECORD_BYTES, 133);
    }
}
