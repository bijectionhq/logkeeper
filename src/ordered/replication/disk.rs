use super::{Accepted, Ballot, Error, Fingerprint, Group, Prefix, Promise, Replica, Vote};
use crate::server::durability::sync_directory;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use fs2::FileExt;
use parking_lot::Mutex;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use uuid::Uuid;

const MAGIC: &[u8; 8] = b"LKORV001";
const STATE: &str = "ordered.state";
const STAGING: &str = "ordered.next";
const LOCK: &str = "ordered.lock";
const MAX_HEADER_BYTES: usize = 256;

#[derive(Clone)]
pub struct DurableVoter {
    inner: Arc<Inner>,
}

struct Inner {
    group: Group,
    identity: Uuid,
    directory: PathBuf,
    _lock: File,
    state: Mutex<Option<VoterState>>,
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
        let state = if initialize {
            if directory.join(STATE).try_exists()? {
                return Err(Error::Group);
            }
            let state = VoterState::default();
            persist(directory, group.identity, identity, &state)?;
            state
        } else {
            recover(directory, &group, identity)?
        };
        Ok(Self {
            inner: Arc::new(Inner {
                group,
                identity,
                directory: directory.to_owned(),
                _lock: lock,
                state: Mutex::new(Some(state)),
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
        let mut state = self.state.lock();
        let current = state.as_ref().ok_or(Error::Stopped)?;
        if let Some(promised) = current.promised.filter(|promised| *promised > ballot) {
            return Err(Error::Deposed(promised));
        }
        let accepted = current.accepted.clone();
        if current.promised != Some(ballot) {
            self.install(
                &mut state,
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
        if prefix.frames.is_empty() {
            return Err(Error::Prefix);
        }
        self.group.replay(&prefix)?;
        let vote = Vote {
            voter: self.identity,
            ballot,
            digest: prefix.identity(group),
        };
        let mut state = self.state.lock();
        let current = state.as_ref().ok_or(Error::Stopped)?;
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
            &mut state,
            VoterState {
                promised: Some(ballot),
                accepted: Some(Accepted { ballot, prefix }),
            },
        )?;
        Ok(vote)
    }

    fn install(&self, current: &mut Option<VoterState>, next: VoterState) -> Result<(), Error> {
        // A failed sync can leave either file selected. Close this process's
        // admission and wait for exact recovery before making another promise.
        *current = None;
        persist(&self.directory, self.group.identity, self.identity, &next)?;
        *current = Some(next);
        Ok(())
    }
}

fn persist(
    directory: &Path,
    group: Fingerprint,
    voter: Uuid,
    state: &VoterState,
) -> Result<(), Error> {
    let mut body = BytesMut::new();
    body.put_slice(MAGIC);
    body.put_slice(&group);
    body.put_slice(voter.as_bytes());
    put_ballot(&mut body, state.promised);
    match &state.accepted {
        Some(accepted) => {
            put_ballot(&mut body, Some(accepted.ballot));
            accepted.prefix.encode_into(&mut body);
        }
        None => put_ballot(&mut body, None),
    }
    let digest = Sha256::digest(&body);
    body.put_slice(&digest);

    let staging = directory.join(STAGING);
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&staging)?;
    file.write_all(&body)?;
    file.sync_all()?;
    drop(file);
    fs::rename(&staging, directory.join(STATE))?;
    sync_directory(directory)?;
    Ok(())
}

fn recover(directory: &Path, group: &Group, voter: Uuid) -> Result<VoterState, Error> {
    let limit = group
        .max_prefix_bytes
        .checked_add(MAX_HEADER_BYTES)
        .ok_or(Error::Capacity)?;
    let mut bytes = Vec::new();
    File::open(directory.join(STATE))?
        .take(limit as u64)
        .read_to_end(&mut bytes)?;
    if bytes.len() >= limit || bytes.len() < MAGIC.len() + 32 + 16 + 2 + 32 {
        return Err(Error::Prefix);
    }
    let split = bytes.len() - 32;
    if &Sha256::digest(&bytes[..split])[..] != &bytes[split..] {
        return Err(Error::Prefix);
    }
    bytes.truncate(split);
    let mut input = Bytes::from(bytes);
    if &input.split_to(MAGIC.len())[..] != MAGIC
        || &input.split_to(32)[..] != group.identity.as_slice()
        || &input.split_to(16)[..] != voter.as_bytes()
    {
        return Err(Error::Group);
    }
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
