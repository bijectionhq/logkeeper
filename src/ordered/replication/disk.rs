use super::{Accepted, Ballot, Error, Fingerprint, Group, Prefix, Promise, Replica, Vote};
use crate::server::durability::sync_directory;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use fs2::FileExt;
use parking_lot::Mutex;
use sha2::{Digest, Sha256};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::Arc;
use uuid::Uuid;

const MAGIC: &[u8; 8] = b"LKORV003";
const SLOTS: [&str; 2] = ["ordered.slot-a", "ordered.slot-b"];
const LOCK: &str = "ordered.lock";
const MAX_HEADER_BYTES: usize = 256;
const HEADER: usize = 8 + 32 + 16 + 8 + 8 + 32;

#[derive(Clone)]
pub struct DurableVoter {
    inner: Arc<Inner>,
}

struct Inner {
    group: Group,
    identity: Uuid,
    _lock: File,
    media: Mutex<Media>,
}

struct Media {
    slots: [File; 2],
    used: [usize; 2],
    selected: Option<Selected>,
}

struct Selected {
    index: usize,
    generation: u64,
    state: VoterState,
}

#[derive(Clone, Default)]
struct VoterState {
    promised: Option<Ballot>,
    accepted: Option<Accepted>,
}

impl DurableVoter {
    pub(super) fn group(&self) -> Fingerprint {
        self.inner.group.identity
    }

    pub(super) fn max_prefix_bytes(&self) -> usize {
        self.inner.group.max_prefix_bytes
    }

    /// Creates the initial empty decision record in a provisioned directory.
    pub fn initialize(group: Group, identity: Uuid, directory: &Path) -> Result<Self, Error> {
        Self::open(group, identity, directory, true)
    }

    /// Recovers the original journal record. Missing media gives no vote.
    pub fn recover(group: Group, identity: Uuid, directory: &Path) -> Result<Self, Error> {
        Self::open(group, identity, directory, false)
    }

    fn open(
        group: Group,
        identity: Uuid,
        directory: &Path,
        initialize: bool,
    ) -> Result<Self, Error> {
        if !group.voters.contains(&identity) {
            return Err(Error::Group);
        }
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join(LOCK))?;
        FileExt::try_lock_exclusive(&lock)?;
        let size = group
            .max_prefix_bytes
            .checked_add(MAX_HEADER_BYTES)
            .ok_or(Error::Capacity)?;
        let open = |name| -> Result<File, Error> {
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(initialize)
                .open(directory.join(name))?;
            if initialize {
                FileExt::allocate(&file, size as u64)?;
                file.sync_all()?;
            }
            if file.metadata()?.len() != size as u64 {
                return Err(Error::Group);
            }
            Ok(file)
        };
        let mut slots = [open(SLOTS[0])?, open(SLOTS[1])?];
        let mut used = [0; 2];
        let selected = if initialize {
            let selected = Selected {
                index: 0,
                generation: 1,
                state: VoterState::default(),
            };
            used[0] = persist(&mut slots[0], group.identity, identity, &selected, 0, size)?;
            sync_directory(directory)?;
            selected
        } else {
            let mut recovered: Option<Selected> = None;
            for (index, file) in slots.iter_mut().enumerate() {
                let (written, candidate) = recover_slot(file, index, &group, identity, size)?;
                used[index] = written;
                if let Some(candidate) = candidate {
                    if recovered
                        .as_ref()
                        .is_some_and(|chosen| chosen.generation == candidate.generation)
                    {
                        return Err(Error::Diverged);
                    }
                    if recovered
                        .as_ref()
                        .is_none_or(|chosen| chosen.generation < candidate.generation)
                    {
                        recovered = Some(candidate);
                    }
                }
            }
            recovered.ok_or(Error::Prefix)?
        };
        Ok(Self {
            inner: Arc::new(Inner {
                group,
                identity,
                _lock: lock,
                media: Mutex::new(Media {
                    slots,
                    used,
                    selected: Some(selected),
                }),
            }),
        })
    }
}

impl Replica for DurableVoter {
    fn identity(&self) -> Uuid {
        self.inner.identity
    }

    async fn prepare(&self, group: Fingerprint, ballot: Ballot) -> Result<Promise, Error> {
        let inner = Arc::clone(&self.inner);
        tokio::task::spawn_blocking(move || inner.prepare(group, ballot))
            .await
            .map_err(|_| Error::Stopped)?
    }

    async fn accept(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: &Prefix,
    ) -> Result<Vote, Error> {
        let inner = Arc::clone(&self.inner);
        let prefix = prefix.clone();
        tokio::task::spawn_blocking(move || inner.accept(group, ballot, prefix))
            .await
            .map_err(|_| Error::Stopped)?
    }
}

impl Inner {
    fn check(&self, group: Fingerprint, ballot: Ballot) -> Result<(), Error> {
        if group != self.group.identity || ballot.round == 0 || ballot.nonce.is_nil() {
            return Err(Error::Group);
        }
        Ok(())
    }

    fn prepare(&self, group: Fingerprint, ballot: Ballot) -> Result<Promise, Error> {
        self.check(group, ballot)?;
        let mut media = self.media.lock();
        let current = &media.selected.as_ref().ok_or(Error::Stopped)?.state;
        if let Some(promised) = current.promised.filter(|promised| *promised > ballot) {
            return Err(Error::Deposed(promised));
        }
        let accepted = current.accepted.clone();
        if current.promised != Some(ballot) {
            self.install(
                &mut media,
                VoterState {
                    promised: Some(ballot),
                    accepted: accepted.clone(),
                },
            )?;
        }
        Ok(Promise {
            voter: self.identity,
            ballot,
            accepted,
        })
    }

    fn accept(&self, group: Fingerprint, ballot: Ballot, prefix: Prefix) -> Result<Vote, Error> {
        self.check(group, ballot)?;
        if prefix.is_empty() {
            return Err(Error::Prefix);
        }
        self.group.replay(&prefix)?;
        let vote = Vote {
            voter: self.identity,
            ballot,
            digest: prefix.identity(group),
        };
        let mut media = self.media.lock();
        let current = &media.selected.as_ref().ok_or(Error::Stopped)?.state;
        match current.promised {
            Some(promised) if promised > ballot => return Err(Error::Deposed(promised)),
            Some(promised) if promised == ballot => {}
            _ => return Err(Error::Group),
        }
        if let Some(accepted) = current
            .accepted
            .as_ref()
            .filter(|accepted| accepted.ballot == ballot)
        {
            if accepted.prefix != prefix {
                return Err(Error::Diverged);
            }
            return Ok(vote);
        }
        self.install(
            &mut media,
            VoterState {
                promised: Some(ballot),
                accepted: Some(Accepted { ballot, prefix }),
            },
        )?;
        Ok(vote)
    }

    fn install(&self, media: &mut Media, next: VoterState) -> Result<(), Error> {
        let prior = media.selected.take().ok_or(Error::Stopped)?;
        let index = 1 - prior.index;
        let generation = prior.generation.checked_add(1).ok_or(Error::Capacity)?;
        let selected = Selected {
            index,
            generation,
            state: next,
        };
        let size = self
            .group
            .max_prefix_bytes
            .checked_add(MAX_HEADER_BYTES)
            .ok_or(Error::Capacity)?;
        let previous = media.used[index];
        media.used[index] = persist(
            &mut media.slots[index],
            self.group.identity,
            self.identity,
            &selected,
            previous,
            size,
        )?;
        media.selected = Some(selected);
        Ok(())
    }
}

fn persist(
    file: &mut File,
    group: Fingerprint,
    voter: Uuid,
    selected: &Selected,
    previous: usize,
    size: usize,
) -> Result<usize, Error> {
    let mut body = BytesMut::new();
    put_ballot(&mut body, selected.state.promised);
    match &selected.state.accepted {
        Some(accepted) => {
            put_ballot(&mut body, Some(accepted.ballot));
            accepted.prefix.encode_into(&mut body);
        }
        None => put_ballot(&mut body, None),
    }
    if body.len() > size - HEADER {
        return Err(Error::Capacity);
    }
    let mut header = BytesMut::with_capacity(HEADER);
    header.put_slice(MAGIC);
    header.put_slice(&group);
    header.put_slice(voter.as_bytes());
    header.put_u64(selected.generation);
    header.put_u64(body.len() as u64);
    let digest = slot_digest(&header, &body);
    header.put_slice(&digest);

    // Leave the current slot intact until both the inactive slot's body
    // and its generation header have reached durable media.
    file.seek(SeekFrom::Start(HEADER as u64))?;
    file.write_all(&body)?;
    let mut old = previous.saturating_sub(body.len());
    let zeros = [0; 8192];
    while old > 0 {
        let count = old.min(zeros.len());
        file.write_all(&zeros[..count])?;
        old -= count;
    }
    file.sync_all()?;
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&header)?;
    file.sync_all()?;
    Ok(body.len())
}

fn recover_slot(
    file: &mut File,
    index: usize,
    group: &Group,
    voter: Uuid,
    size: usize,
) -> Result<(usize, Option<Selected>), Error> {
    let mut header = [0; HEADER];
    file.read_exact(&mut header)?;
    let payload_limit = size - HEADER;
    if header == [0; HEADER] {
        return Ok((payload_limit, None));
    }
    let split = HEADER - 32;
    let mut descriptor = &header[..split];
    let magic = descriptor.get_u64();
    let addressed: Fingerprint = descriptor[..32].try_into().map_err(|_| Error::Prefix)?;
    descriptor.advance(32);
    let witness = Uuid::from_slice(&descriptor[..16]).map_err(|_| Error::Prefix)?;
    descriptor.advance(16);
    let generation = descriptor.get_u64();
    let length = usize::try_from(descriptor.get_u64()).ok();
    let Some(length) = length.filter(|length| (2..=payload_limit).contains(length)) else {
        return Ok((payload_limit, None));
    };
    let mut body = vec![0; length];
    file.read_exact(&mut body)?;
    if &slot_digest(&header[..split], &body)[..] != &header[split..] {
        return Ok((payload_limit, None));
    }
    if magic != u64::from_be_bytes(*MAGIC)
        || addressed != group.identity
        || witness != voter
        || generation == 0
    {
        return Err(Error::Group);
    }
    let state = load_state(group, Bytes::from(body))?;
    Ok((
        length,
        Some(Selected {
            index,
            generation,
            state,
        }),
    ))
}

fn slot_digest(header: &[u8], body: &[u8]) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(header);
    hash.update(body);
    hash.finalize().into()
}

fn load_state(group: &Group, mut input: Bytes) -> Result<VoterState, Error> {
    let promised = read_ballot(&mut input)?;
    let accepted = if let Some(ballot) = read_ballot(&mut input)? {
        if promised.is_none_or(|promised| ballot > promised) {
            return Err(Error::Prefix);
        }
        let prefix = Prefix::decode(input, group.max_prefix_bytes)?;
        group.replay(&prefix)?;
        Some(Accepted { ballot, prefix })
    } else {
        if !input.is_empty() {
            return Err(Error::Prefix);
        }
        None
    };
    Ok(VoterState { promised, accepted })
}

fn put_ballot(output: &mut BytesMut, ballot: Option<Ballot>) {
    output.put_u8(u8::from(ballot.is_some()));
    if let Some(ballot) = ballot {
        output.put_u64(ballot.round);
        output.put_slice(ballot.nonce.as_bytes());
    }
}

fn read_ballot(input: &mut Bytes) -> Result<Option<Ballot>, Error> {
    if input.is_empty() {
        return Err(Error::Prefix);
    }
    match input.get_u8() {
        0 => Ok(None),
        1 if input.len() >= 24 => {
            let round = input.get_u64();
            let nonce = Uuid::from_slice(&input.split_to(16)).map_err(|_| Error::Prefix)?;
            if round == 0 || nonce.is_nil() {
                return Err(Error::Prefix);
            }
            Ok(Some(Ballot { round, nonce }))
        }
        _ => Err(Error::Prefix),
    }
}
