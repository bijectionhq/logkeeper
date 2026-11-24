use super::rules::{AcceptBallot, accept_ballot, depose_prepare};
use super::{
    Accepted, Ballot, Error, Fingerprint, Group, Prefix, Promise, RepairSeed, Replica, SlotImage,
    SlotPair, Vote,
};
use crate::ordered::admission::matches_fingerprint;
use crate::ordered::codec::frame::bounded_body_length;
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

mod mirror;
mod recover;
mod selection;

use recover::{HEADER, SlotHeader, recover_slot};
use selection::{MAGIC, read_back_matches, select_slot};

const SLOTS: [&str; 2] = ["ordered.slot-a", "ordered.slot-b"];
const LOCK: &str = "ordered.lock";
const RESERVATION: &str = "ordered.reserve";
const MAX_HEADER_BYTES: usize = 256;

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
    pub fn reserved_bytes(group: &Group) -> Result<u64, Error> {
        (slot_size(group)? as u64)
            .checked_mul(2)
            .ok_or(Error::Capacity)
    }

    pub(super) fn group(&self) -> Fingerprint {
        self.inner.group.identity
    }

    pub(super) fn max_prefix_bytes(&self) -> usize {
        self.inner.group.max_prefix_bytes
    }

    /// Creates the initial empty decision record in a provisioned directory.
    pub fn initialize(group: Group, identity: Uuid, directory: &Path) -> Result<Self, Error> {
        if group.predecessor.is_some() {
            return Err(Error::Group);
        }
        Self::open(
            group,
            identity,
            directory,
            Some(VoterState::default()),
            true,
        )
    }

    /// Reserves both successor slots without creating an eligible voter.
    pub fn reserve_repair(group: &Group, identity: Uuid, directory: &Path) -> Result<u64, Error> {
        if group.predecessor.is_none() || !group.voters.contains(&identity) {
            return Err(Error::Group);
        }
        let lock = lock(directory)?;
        let size = slot_size(group)?;
        if directory.join(RESERVATION).try_exists()? {
            let _slots = slots(directory, size, false)?;
            let (ticket, _) = read_reservation(directory, group, identity, size)?;
            ticket.sync_all()?;
            sync_directory(directory)?;
            return Self::reserved_bytes(group);
        }
        let _slots = slots(directory, size, true)?;
        let mut ticket = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(directory.join(RESERVATION))?;
        ticket.write_all(&reservation(group, identity, size))?;
        ticket.write_all(&[0])?;
        ticket.sync_all()?;
        sync_directory(directory)?;
        drop(lock);
        Self::reserved_bytes(group)
    }

    /// Starts paid successor media with the exact image sealed by its predecessor.
    pub fn initialize_repaired(
        group: Group,
        identity: Uuid,
        directory: &Path,
        seed: &RepairSeed,
    ) -> Result<Self, Error> {
        let prefix = group.install_seed(seed)?;
        let ballot = Ballot {
            round: 1,
            nonce: Uuid::from_u128(1),
        };
        let voter = Self::open(
            group,
            identity,
            directory,
            Some(VoterState {
                promised: Some(ballot),
                accepted: Some(Accepted { ballot, prefix }),
            }),
            false,
        )?;
        #[cfg(feature = "simulation")]
        if let Some(trace) = &voter.inner.group.trace {
            let media = voter.inner.media.lock();
            let selected = &media.selected.as_ref().expect("installed media").state;
            let accepted = selected.accepted.as_ref().expect("installed prefix");
            assert_eq!(selected.promised, Some(accepted.ballot));
            let state = voter.inner.group.replay(&accepted.prefix).expect("installed prefix replays");
            trace.install(voter.inner.group.identity, identity, accepted, &state);
        }
        Ok(voter)
    }

    /// Recovers the original journal record. Missing media gives no vote.
    pub fn recover(group: Group, identity: Uuid, directory: &Path) -> Result<Self, Error> {
        let voter = Self::open(group, identity, directory, None, false)?;
        #[cfg(feature = "simulation")]
        if let Some(trace) = &voter.inner.group.trace {
            let media = voter.inner.media.lock();
            let state = &media.selected.as_ref().expect("reopened media").state;
            trace.restart(
                voter.inner.group.identity,
                identity,
                state.promised,
                state.accepted.as_ref(),
            );
        }
        Ok(voter)
    }

    fn open(
        group: Group,
        identity: Uuid,
        directory: &Path,
        bootstrap: Option<VoterState>,
        create: bool,
    ) -> Result<Self, Error> {
        if !group.voters.contains(&identity) {
            return Err(Error::Group);
        }
        let lock = lock(directory)?;
        let size = slot_size(&group)?;
        let ticket = group
            .predecessor
            .map(|_| read_reservation(directory, &group, identity, size))
            .transpose()?;
        if bootstrap.is_none() && ticket.as_ref().is_some_and(|(_, installed)| !installed) {
            return Err(Error::Stopped);
        }
        let mut slots = slots(directory, size, create)?;
        let mut used = [0; 2];
        let recovered = if create {
            None
        } else {
            recover_media(&mut slots, &mut used, &group, identity, size)?
        };
        let installing = bootstrap.is_some();
        let mut selected = if let Some(known) = recovered {
            if let Some(expected) = &bootstrap
                && (known.state.promised != expected.promised
                    || known.state.accepted.as_ref().map(|vote| &vote.prefix)
                        != expected.accepted.as_ref().map(|vote| &vote.prefix))
            {
                return Err(Error::Group);
            }
            // A warm restart can read a header that the prior process did
            // not finish syncing. Make its slot durable before a later
            // install can overwrite the other slot.
            slots[known.index].sync_all()?;
            known
        } else if let Some(state) = bootstrap {
            if ticket.as_ref().is_some_and(|(_, installed)| *installed) {
                return Err(Error::Stopped);
            }
            let selected = Selected {
                index: 0,
                generation: 1,
                state,
            };
            used[0] = persist(
                &mut slots[0],
                group.identity,
                identity,
                &selected,
                used[0],
                size,
            )?
            .0;
            selected
        } else {
            return Err(Error::Prefix);
        };
        if installing {
            let index = 1 - selected.index;
            selected.index = index;
            selected.generation = selected.generation.checked_add(1).ok_or(Error::Capacity)?;
            used[index] = persist(
                &mut slots[index],
                group.identity,
                identity,
                &selected,
                used[index],
                size,
            )?
            .0;
        }
        sync_directory(directory)?;
        if let Some((mut ticket, installed)) = ticket {
            if !installed {
                ticket.seek(SeekFrom::Start(32))?;
                ticket.write_all(&[1])?;
            }
            ticket.sync_all()?;
        }
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

fn lock(directory: &Path) -> Result<File, Error> {
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(directory.join(LOCK))?;
    FileExt::try_lock_exclusive(&lock)?;
    Ok(lock)
}

fn slot_size(group: &Group) -> Result<usize, Error> {
    group
        .max_prefix_bytes
        .checked_add(MAX_HEADER_BYTES)
        .ok_or(Error::Capacity)
}

fn slots(directory: &Path, size: usize, create: bool) -> Result<[File; 2], Error> {
    let open = |name| -> Result<File, Error> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(create)
            .open(directory.join(name))?;
        if create {
            FileExt::allocate(&file, size as u64)?;
            file.sync_all()?;
        }
        if file.metadata()?.len() != size as u64 {
            return Err(Error::Group);
        }
        Ok(file)
    };
    Ok([open(SLOTS[0])?, open(SLOTS[1])?])
}

fn reservation(group: &Group, identity: Uuid, size: usize) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.repair-reservation.v1");
    hash.update(group.identity);
    hash.update(identity.as_bytes());
    hash.update((size as u64).to_be_bytes());
    hash.finalize().into()
}

fn read_reservation(
    directory: &Path,
    group: &Group,
    identity: Uuid,
    size: usize,
) -> Result<(File, bool), Error> {
    let mut ticket = OpenOptions::new()
        .read(true)
        .write(true)
        .open(directory.join(RESERVATION))?;
    let mut stored = [0; 33];
    ticket.read_exact(&mut stored)?;
    if ticket.metadata()?.len() != 33
        || stored[..32] != reservation(group, identity, size)
        || stored[32] > 1
    {
        return Err(Error::Group);
    }
    Ok((ticket, stored[32] == 1))
}

fn recover_media(
    slots: &mut [File; 2],
    used: &mut [usize; 2],
    group: &Group,
    identity: Uuid,
    size: usize,
) -> Result<Option<Selected>, Error> {
    let mut candidates = [None, None];
    for (index, file) in slots.iter_mut().enumerate() {
        let (written, candidate) = recover_slot(file, index, group, identity, size)?;
        used[index] = written;
        candidates[index] = candidate.map(|(selected, _)| selected);
    }
    let [first, second] = candidates
        .each_ref()
        .map(|slot| slot.as_ref().map(|v| v.generation));
    Ok(select_slot(first, second)?.and_then(|index| candidates[index].take()))
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
        read_back: bool,
    ) -> Result<Vote, Error> {
        let inner = Arc::clone(&self.inner);
        let prefix = prefix.clone();
        tokio::task::spawn_blocking(move || inner.accept(group, ballot, prefix, read_back))
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
        if let Some(promised) = current
            .promised
            .filter(|promised| depose_prepare(Some(promised.rank()), ballot.rank()))
        {
            return Err(Error::Deposed(promised));
        }
        let accepted = current.accepted.clone();
        self.mirror(
            &mut media,
            VoterState {
                promised: Some(ballot),
                accepted: accepted.clone(),
            },
        )?;
        #[cfg(feature = "simulation")]
        if let Some(trace) = &self.group.trace {
            let selected = &media.selected.as_ref().expect("promised media").state;
            assert_eq!(selected.promised, Some(ballot));
            assert_eq!(
                selected.accepted.as_ref().map(|vote| (vote.ballot, &vote.prefix)),
                accepted.as_ref().map(|vote| (vote.ballot, &vote.prefix)),
            );
            trace.promise(group, self.identity, ballot, accepted.as_ref());
        }
        Ok(Promise {
            voter: self.identity,
            ballot,
            accepted,
        })
    }

    fn accept(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: Prefix,
        read_back: bool,
    ) -> Result<Vote, Error> {
        self.check(group, ballot)?;
        if prefix.is_empty() {
            return Err(Error::Prefix);
        }
        self.group.replay(&prefix)?;
        let digest = prefix.identity(group);
        let mut media = self.media.lock();
        let current = &media.selected.as_ref().ok_or(Error::Stopped)?.state;
        match accept_ballot(current.promised.map(Ballot::rank), ballot.rank()) {
            AcceptBallot::Deposed => return Err(Error::Deposed(current.promised.unwrap())),
            AcceptBallot::Promised => {}
            AcceptBallot::Unprepared => return Err(Error::Group),
        }
        if current
            .accepted
            .as_ref()
            .is_some_and(|accepted| accepted.ballot == ballot && accepted.prefix != prefix)
        {
            return Err(Error::Diverged);
        }
        let slots = self.mirror(
            &mut media,
            VoterState {
                promised: Some(ballot),
                accepted: Some(Accepted { ballot, prefix }),
            },
        )?;
        #[cfg(feature = "simulation")]
        if let Some(trace) = &self.group.trace {
            let selected = &media.selected.as_ref().expect("accepted media").state;
            let accepted = selected.accepted.as_ref().expect("accepted prefix");
            assert_eq!(selected.promised, Some(accepted.ballot));
            let state = self.group.replay(&accepted.prefix).expect("accepted prefix replays");
            trace.accept(group, self.identity, accepted, &state);
        }
        if read_back {
            if let Err(error) = self.read_back(&mut media, ballot, digest, slots) {
                media.selected = None;
                return Err(error);
            }
        }
        Ok(Vote {
            voter: self.identity,
            ballot,
            digest,
            slots,
            read_back,
        })
    }

    fn read_back_slot(
        &self,
        media: &mut Media,
        index: usize,
        size: usize,
        ballot: Ballot,
        digest: Fingerprint,
        expected: SlotImage,
    ) -> Result<(), Error> {
        let file = &mut media.slots[index];
        file.seek(SeekFrom::Start(0))?;
        let (_, image) = recover_slot(file, index, &self.group, self.identity, size)?;
        let (image, observed) = image.ok_or(Error::Prefix)?;
        let accepted = image.state.accepted.ok_or(Error::Prefix)?;
        if !read_back_matches(
            image.generation,
            expected.generation,
            &observed,
            &expected.digest,
            image.state.promised == Some(ballot),
            accepted.ballot == ballot,
            &accepted.prefix.identity(self.group.identity),
            &digest,
        ) {
            return Err(Error::Prefix);
        }
        Ok(())
    }

    fn install(&self, media: &mut Media, next: VoterState) -> Result<(usize, SlotImage), Error> {
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
        let (used, digest) = persist(
            &mut media.slots[index],
            self.group.identity,
            self.identity,
            &selected,
            previous,
            size,
        )?;
        media.used[index] = used;
        media.selected = Some(selected);
        Ok((index, SlotImage { generation, digest }))
    }
}

fn persist(
    file: &mut File,
    group: Fingerprint,
    voter: Uuid,
    selected: &Selected,
    previous: usize,
    size: usize,
) -> Result<(usize, Fingerprint), Error> {
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

    // The header digest covers the whole body, so a crash between these
    // writes can only expose a complete image or leave the prior slot in use.
    file.seek(SeekFrom::Start(HEADER as u64))?;
    file.write_all(&body)?;
    let mut old = previous.saturating_sub(body.len());
    let zeros = [0; 8192];
    while old > 0 {
        let count = old.min(zeros.len());
        file.write_all(&zeros[..count])?;
        old -= count;
    }
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&header)?;
    file.sync_all()?;
    Ok((body.len(), digest))
}

fn read_slot_header(file: &mut File) -> Result<SlotHeader, Error> {
    let mut header = [0; HEADER];
    file.read_exact(&mut header)?;
    let split = HEADER - 32;
    let mut descriptor = &header[..split];
    let magic = descriptor[..8].try_into().map_err(|_| Error::Prefix)?;
    descriptor.advance(8);
    let addressed = descriptor[..32].try_into().map_err(|_| Error::Prefix)?;
    descriptor.advance(32);
    let witness = Uuid::from_slice(&descriptor[..16]).map_err(|_| Error::Prefix)?;
    descriptor.advance(16);
    let generation = descriptor.get_u64();
    let length = descriptor.get_u64();
    Ok(SlotHeader {
        raw: header,
        empty: header == [0; HEADER],
        magic,
        addressed,
        witness: witness.as_u128(),
        generation,
        length,
        digest: header[split..].try_into().map_err(|_| Error::Prefix)?,
    })
}

fn read_slot_body(
    file: &mut File,
    header: &SlotHeader,
    length: usize,
) -> Result<(Vec<u8>, Fingerprint), Error> {
    let mut body = vec![0; length];
    file.read_exact(&mut body)?;
    let digest = slot_digest(&header.raw[..HEADER - 32], &body);
    Ok((body, digest))
}

fn slot_digest(header: &[u8], body: &[u8]) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(header);
    hash.update(body);
    hash.finalize().into()
}

fn load_state(group: &Group, body: Vec<u8>) -> Result<VoterState, Error> {
    let mut input = Bytes::from(body);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered::{
        Checkpoint, Command, Custody, Cut, Limits, Outcome, Placement, Principal, Request,
        RequestId, Window,
    };

    #[tokio::test]
    async fn surviving_voters_recover_the_exact_receipt_after_slot_tears() {
        for failed_zone in 0..3 {
            for tear_at in [0, HEADER as u64] {
                assert_receipt_recovers(failed_zone, tear_at).await;
            }
        }
    }

    async fn assert_receipt_recovers(failed_zone: usize, tear_at: u64) {
        let voters = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
        let placement = Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        };
        let group = Group::new(
            placement,
            Limits {
                enrolled_workers: 2,
                replay_holds: 2,
                retry_positions: 16,
                retained_data_bytes: 4096,
                maintenance_bytes: 1024,
                serving_lease: 30_000,
                clock_drift: 1_000,
            },
            Checkpoint {
                cut: Cut {
                    next_lsn: 0,
                    history: [1; 32],
                },
                root: [0; 32],
                manifest: [0; 32],
                custody: Custody {
                    allocation: Uuid::new_v4(),
                    revision: 1,
                    provider: [0; 32],
                },
            },
            Window {
                allocation: Uuid::new_v4(),
                serial: 1,
                bytes: 1024,
            },
            voters,
            64 << 10,
        )
        .unwrap();
        let volumes = voters.map(|_| tempfile::tempdir().unwrap());
        let peers = voters
            .iter()
            .zip(&volumes)
            .map(|(id, volume)| {
                DurableVoter::initialize(group.clone(), *id, volume.path()).unwrap()
            })
            .collect::<Vec<_>>();
        let invocation = Request {
            placement,
            principal: Principal::Administrator,
            id: RequestId::fresh(0, 16).unwrap(),
            command: Command::Enroll {
                worker: Uuid::new_v4(),
                expected: None,
            },
        };
        let chosen = group
            .choose(&peers[..2], 1, invocation.clone())
            .await
            .unwrap();
        assert!(matches!(chosen.receipt().outcome, Ok(Outcome::Enrolled(_))));
        assert_eq!(chosen.voters().len(), 2);
        let surviving = peers
            .iter()
            .enumerate()
            .filter(|(at, _)| *at != failed_zone)
            .map(|(at, peer)| {
                let disk = peer.inner.media.lock();
                let committed = disk.selected.as_ref().unwrap().index;
                (at, 1 - committed)
            })
            .collect::<Vec<_>>();
        drop(peers);
        for &(at, inactive) in &surviving {
            // Reproduce a torn body or generation header on every voter
            // outside the failed zone before restarting any of them.
            let path = volumes[at].path().join(SLOTS[inactive]);
            let mut file = OpenOptions::new().write(true).open(path).unwrap();
            file.seek(SeekFrom::Start(tear_at)).unwrap();
            file.write_all(&[0xff; 61]).unwrap();
            file.sync_all().unwrap();
        }
        let reopened = surviving
            .iter()
            .map(|&(at, _)| {
                DurableVoter::recover(group.clone(), voters[at], volumes[at].path()).unwrap()
            })
            .collect::<Vec<_>>();
        let retried = group.choose(&reopened, 2, invocation).await.unwrap();
        assert_eq!(retried.receipt(), chosen.receipt());
        assert_eq!(
            retried.state().command_history(),
            chosen.state().command_history()
        );
    }

    #[tokio::test]
    async fn rotation_fences_both_slots_across_changed_majorities_and_repair() {
        use crate::ordered::{AppendClass, CheckpointPreparation};

        let voters = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
        let placement = Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        };
        let base = Checkpoint {
            cut: Cut {
                next_lsn: 0,
                history: [1; 32],
            },
            root: [0; 32],
            manifest: [0; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [0; 32],
            },
        };
        let limits = Limits {
            enrolled_workers: 1,
            replay_holds: 2,
            retry_positions: 16,
            retained_data_bytes: 4096,
            maintenance_bytes: 1024,
            serving_lease: 30_000,
            clock_drift: 1000,
        };
        let window = Window {
            allocation: Uuid::new_v4(),
            serial: 1,
            bytes: 1024,
        };
        let group = Group::new(placement, limits, base, window, voters, 64 << 10).unwrap();
        let volumes = voters.map(|_| tempfile::tempdir().unwrap());
        let peers = voters
            .iter()
            .zip(&volumes)
            .map(|(id, path)| DurableVoter::initialize(group.clone(), *id, path.path()).unwrap())
            .collect::<Vec<_>>();
        let first = [peers[0].clone(), peers[2].clone()];
        let second = [peers[0].clone(), peers[1].clone()];
        let third = [peers[1].clone(), peers[2].clone()];
        let request = |observed_position: u64, principal, command| Request {
            placement,
            principal,
            id: RequestId::fresh(observed_position, limits.retry_positions).unwrap(),
            command,
        };
        let enrollment = group
            .choose(
                &first,
                1,
                request(
                    0,
                    Principal::Administrator,
                    Command::Enroll {
                        worker: Uuid::new_v4(),
                        expected: None,
                    },
                ),
            )
            .await
            .unwrap();
        let Ok(Outcome::Enrolled(enrolled)) = enrollment.receipt().outcome else {
            panic!()
        };
        let worker = Principal::Worker(enrolled);
        let granted = group
            .choose(
                &first,
                2,
                request(
                    enrollment.state().position(),
                    worker,
                    Command::Grant {
                        expected: enrollment.state().writer_state(),
                        candidate: enrolled,
                    },
                ),
            )
            .await
            .unwrap();
        let Ok(Outcome::Granted { grant, .. }) = granted.receipt().outcome else {
            panic!()
        };
        let append = group
            .choose(
                &first,
                3,
                request(
                    granted.state().position(),
                    worker,
                    Command::Append {
                        class: AppendClass::Data,
                        grant,
                        expected_next: 0,
                        timestamp: 1,
                        payload: Bytes::from_static(b"old"),
                        references: None,
                    },
                ),
            )
            .await
            .unwrap();
        let checkpoint = Checkpoint {
            cut: append.state().head(),
            root: [2; 32],
            manifest: [3; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 2,
                provider: [4; 32],
            },
        };
        let prepare = group
            .choose(
                &second,
                4,
                request(
                    append.state().position(),
                    Principal::Custodian,
                    Command::PrepareCheckpoint {
                        preparation: CheckpointPreparation {
                            erasure: true,
                            checkpoint: checkpoint.cut,
                            root: checkpoint.root,
                            source: grant,
                            base,
                            custody: checkpoint.custody,
                            usable_bytes: 64,
                            descriptor: [5; 32],
                        },
                        references: None,
                    },
                ),
            )
            .await
            .unwrap();
        assert!(matches!(
            prepare.receipt().outcome,
            Ok(Outcome::CheckpointPrepared(_))
        ));
        let invocation = request(
            prepare.state().position(),
            Principal::Custodian,
            Command::PublishAndRotate { grant, checkpoint },
        );
        let rotation = group.choose(&third, 6, invocation.clone()).await.unwrap();
        let evidence = rotation.rotation_slots(&invocation).unwrap();
        let witness = evidence
            .voters
            .iter()
            .find(|entry| entry.voter == voters[2])
            .unwrap();
        let selected = peers[2].inner.media.lock().selected.as_ref().unwrap().index;
        assert_eq!(usize::from(witness.slots.selected), selected);
        drop(first);
        drop(second);
        drop(third);
        let [stale, other, torn]: [DurableVoter; 3] = peers.try_into().ok().unwrap();
        drop(torn);
        tear_slot(volumes[2].path(), selected);
        let reopened = DurableVoter::recover(group.clone(), voters[2], volumes[2].path()).unwrap();
        {
            let media = reopened.inner.media.lock();
            let recovered = media.selected.as_ref().unwrap();
            assert_eq!(recovered.index, 1 - selected);
            let accepted = recovered.state.accepted.as_ref().unwrap();
            let state = group.replay(&accepted.prefix).unwrap();
            assert_eq!(
                state.checkpoint(),
                checkpoint,
                "alternate slot crossed the rotation fence backward"
            );
            assert_eq!(state.authority.key_generation, 2);
            assert_eq!(accepted.prefix.identity(group.identity()), evidence.prefix);
            let image = witness.slots.images[recovered.index];
            assert_eq!(recovered.generation, image.generation);
            let mut file = File::open(volumes[2].path().join(SLOTS[recovered.index])).unwrap();
            file.seek(SeekFrom::Start((HEADER - 32) as u64)).unwrap();
            let mut digest = [0; 32];
            file.read_exact(&mut digest).unwrap();
            assert_eq!(digest, image.digest);
        }

        let changed = [stale, reopened];
        let recovered = group.recover(&changed, 7).await.unwrap();
        assert_eq!(recovered.checkpoint(), checkpoint);
        let successor_voters = [Uuid::new_v4(), Uuid::new_v4(), Uuid::new_v4()];
        let successor = Group::new(placement, limits, base, window, successor_voters, 64 << 10)
            .unwrap()
            .successor(group.identity())
            .unwrap();
        let seal = request(
            recovered.position(),
            Principal::Administrator,
            Command::SealCohort {
                expected: group.identity(),
                successor: successor.identity(),
            },
        );
        let sealed = group.choose(&changed, 8, seal).await.unwrap();
        assert_eq!(
            sealed.receipt().outcome,
            Ok(Outcome::CohortSealed(successor.identity()))
        );
        let [_, reopened] = changed;
        let selected = reopened.inner.media.lock().selected.as_ref().unwrap().index;
        drop(reopened);
        tear_slot(volumes[2].path(), selected);
        let reopened = DurableVoter::recover(group.clone(), voters[2], volumes[2].path()).unwrap();
        let seed = group
            .repair_seed(&[other, reopened], 9, &successor)
            .await
            .unwrap();

        let mut replacements = Vec::new();
        let mut replacement_media = Vec::new();
        for (offset, voter) in successor_voters[..2].iter().copied().enumerate() {
            let directory = tempfile::tempdir().unwrap();
            DurableVoter::reserve_repair(&successor, voter, directory.path()).unwrap();
            let disk = DurableVoter::initialize_repaired(
                successor.clone(),
                voter,
                directory.path(),
                &seed,
            )
            .unwrap();
            drop(disk);
            tear_slot(directory.path(), offset);
            replacements
                .push(DurableVoter::recover(successor.clone(), voter, directory.path()).unwrap());
            replacement_media.push(directory);
        }
        let retried = successor
            .choose(&replacements, 2, invocation.clone())
            .await
            .unwrap();
        assert_eq!(retried.receipt(), rotation.receipt());
        let repaired_evidence = retried.rotation_slots(&invocation).unwrap();
        assert_eq!(repaired_evidence.group, successor.identity());
        assert_eq!(repaired_evidence.checkpoint, checkpoint);
    }

    fn tear_slot(directory: &Path, index: usize) {
        let mut torn = OpenOptions::new()
            .write(true)
            .open(directory.join(SLOTS[index]))
            .unwrap();
        torn.write_all(&[0; HEADER]).unwrap();
        torn.sync_all().unwrap();
    }
}
