//! Fixed-group prefix agreement over the ordered reducer.
//!
//! Each ballot is used for one proposed extension. Recovery adopts the
//! greatest accepted ballot and its exact prefix.
//! Transport implementations supply authenticated replies from the named
//! durable journals in the installed cohort.

mod disk;
mod evidence;
mod rotation;
mod rules;
pub mod transport;

pub use disk::DurableVoter;
pub use evidence::{RotationSlots, SlotImage, SlotPair, Vote, VoterSlots};
use evidence::{record_vote, register_peer, strict_majority};

use super::{
    BarrierClaim, Checkpoint, Command, Fingerprint, Limits, Outcome, Placement, Receipt, Refusal,
    Request, State, Window,
};
use bytes::{Buf, BufMut, Bytes, BytesMut};
use futures::{StreamExt, stream::FuturesUnordered};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::future::Future;
use uuid::Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ballot {
    pub round: u64,
    pub nonce: Uuid,
}

impl Ballot {
    fn rank(self) -> rules::BallotRank {
        (self.round, self.nonce.as_u128())
    }
}

#[derive(Clone)]
pub struct Group {
    identity: Fingerprint,
    initial: State,
    voters: BTreeSet<Uuid>,
    max_prefix_bytes: usize,
    predecessor: Option<Fingerprint>,
}

pub struct RepairSeed {
    predecessor: Fingerprint,
    destination: Fingerprint,
    base: Bytes,
}

impl RepairSeed {
    pub(in crate::ordered) fn encode(&self) -> Bytes {
        let mut bytes = BytesMut::with_capacity(72 + self.base.len());
        bytes.put_slice(b"LKSEED01");
        bytes.put_slice(&self.predecessor);
        bytes.put_slice(&self.destination);
        bytes.put_slice(&self.base);
        bytes.freeze()
    }

    /// The installation boundary verifies the predecessor's signature before decoding.
    pub(in crate::ordered) fn decode(mut bytes: Bytes) -> Result<Self, Error> {
        if bytes.len() <= 72 || &bytes.split_to(8)[..] != b"LKSEED01" {
            return Err(Error::Prefix);
        }
        let predecessor = bytes
            .split_to(32)
            .as_ref()
            .try_into()
            .map_err(|_| Error::Prefix)?;
        let destination = bytes
            .split_to(32)
            .as_ref()
            .try_into()
            .map_err(|_| Error::Prefix)?;
        Ok(Self {
            predecessor,
            destination,
            base: bytes,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prefix {
    base: Option<Bytes>,
    frames: Vec<Bytes>,
    bytes: usize,
}

#[derive(Clone)]
pub struct Accepted {
    pub ballot: Ballot,
    pub prefix: Prefix,
}

#[derive(Clone)]
pub struct Promise {
    pub voter: Uuid,
    pub ballot: Ballot,
    pub accepted: Option<Accepted>,
}

pub struct Chosen {
    group: Fingerprint,
    cohort_size: usize,
    ballot: Ballot,
    prefix: Fingerprint,
    voters: Vec<Uuid>,
    images: Vec<VoterSlots>,
    receipt: Receipt,
    state: State,
}

impl Chosen {
    pub fn ballot(&self) -> Ballot {
        self.ballot
    }
    pub fn prefix(&self) -> Fingerprint {
        self.prefix
    }
    pub fn voters(&self) -> &[Uuid] {
        &self.voters
    }
    pub fn receipt(&self) -> Receipt {
        self.receipt
    }
    pub fn state(&self) -> &State {
        &self.state
    }

    /// Supplies the exact successful application to a scoped receipt issuer.
    pub fn barrier_claim(&self) -> Option<BarrierClaim> {
        let Outcome::Barrier { read } = self.receipt.outcome.ok()? else {
            return None;
        };
        self.state.held_replay(self.receipt.principal, read).ok()?;
        Some(BarrierClaim {
            placement: self.receipt.placement,
            read,
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("the installed journal group does not match")]
    Group,
    #[error("invalid ordered journal prefix")]
    Prefix,
    #[error("the bounded ordered journal prefix is full")]
    Capacity,
    #[error("the voter promised a newer ballot {0:?}")]
    Deposed(Ballot),
    #[error("an intersecting durable quorum did not answer")]
    Quorum,
    #[error("the recovered prefix contains incompatible votes in the same ballot")]
    Diverged,
    #[error("the ordered voter has stopped accepting work")]
    Stopped,
    #[error("the installed voter configuration was sealed for repair")]
    Sealed,
    #[error("the proposed journal time precedes the chosen journal time")]
    Time,
    #[error("ordered journal I/O failed: {0}")]
    Io(#[from] std::io::Error),
}

impl Group {
    #[cfg(feature = "ordered-daemon")]
    pub(in crate::ordered) fn bind_voters(mut self, commitment: Fingerprint) -> Self {
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-voter-policy.v1");
        hash.update(self.identity);
        hash.update(commitment);
        self.identity = hash.finalize().into();
        self.initial.voter_scope = self.identity;
        self
    }

    pub fn new(
        placement: Placement,
        limits: Limits,
        checkpoint: Checkpoint,
        window: Window,
        voters: impl IntoIterator<Item = Uuid>,
        max_prefix_bytes: usize,
    ) -> Result<Self, Refusal> {
        let mut roster = BTreeSet::new();
        for voter in voters {
            if voter.is_nil() || !roster.insert(voter) {
                return Err(Refusal::Invalid);
            }
        }
        if roster.len() < 3 || roster.len() % 2 == 0 || max_prefix_bytes == 0 {
            return Err(Refusal::Invalid);
        }
        let data_bytes =
            usize::try_from(limits.retained_data_bytes).map_err(|_| Refusal::Capacity)?;
        let minimum = limits
            .base_control_bytes()
            .and_then(|control| control.checked_add(data_bytes))
            .ok_or(Refusal::Capacity)?;
        if max_prefix_bytes < minimum {
            return Err(Refusal::Capacity);
        }
        let mut initial = State::new(placement, limits, checkpoint, window)?;
        initial.object_control_bytes =
            ((max_prefix_bytes - minimum) / 2).min(super::MAX_OBJECT_CONTROL_BYTES);
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-group.v5");
        hash.update(placement.deployment.as_bytes());
        hash.update(placement.incarnation.as_bytes());
        hash.update(placement.group.as_bytes());
        hash.update(placement.generation.to_be_bytes());
        hash.update(checkpoint.cut.history);
        hash.update(checkpoint.root);
        hash.update(checkpoint.manifest);
        hash.update(checkpoint.custody.allocation.as_bytes());
        hash.update(checkpoint.custody.revision.to_be_bytes());
        hash.update(checkpoint.custody.provider);
        hash.update(window.allocation.as_bytes());
        hash.update(window.serial.to_be_bytes());
        hash.update(window.bytes.to_be_bytes());
        for limit in [
            limits.enrolled_workers,
            limits.replay_holds,
            max_prefix_bytes,
            roster.len(),
        ] {
            hash.update(
                u64::try_from(limit)
                    .map_err(|_| Refusal::Invalid)?
                    .to_be_bytes(),
            );
        }
        hash.update(limits.retry_positions.to_be_bytes());
        hash.update(limits.retained_data_bytes.to_be_bytes());
        hash.update(limits.maintenance_bytes.to_be_bytes());
        hash.update(limits.serving_lease.to_be_bytes());
        hash.update(limits.clock_drift.to_be_bytes());
        for voter in &roster {
            hash.update(voter.as_bytes());
        }
        let identity = hash.finalize().into();
        initial.voter_scope = identity;
        Ok(Self {
            identity,
            initial,
            voters: roster,
            max_prefix_bytes,
            predecessor: None,
        })
    }

    /// Names a physical successor without changing the logical placement.
    pub fn successor(mut self, predecessor: Fingerprint) -> Result<Self, Refusal> {
        if predecessor == [0; 32] || self.predecessor.is_some() {
            return Err(Refusal::Invalid);
        }
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-successor.v1");
        hash.update(predecessor);
        hash.update(self.identity);
        self.identity = hash.finalize().into();
        self.initial.voter_scope = self.identity;
        self.predecessor = Some(predecessor);
        Ok(self)
    }

    /// Captures the exact source selected by the old quorum's seal. The
    /// successor retains the original placement, data, grants, and custody.
    pub async fn repair_seed<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
        destination: &Group,
    ) -> Result<RepairSeed, Error> {
        if destination.predecessor != Some(self.identity)
            || destination.placement() != self.placement()
        {
            return Err(Error::Group);
        }
        let state = self.recover(peers, round).await?;
        let selected_seal = state.successor;
        let mut state = rules::seal_image(selected_seal.as_ref(), &destination.identity, state)
            .ok_or(Error::Sealed)?;
        state.voter_scope = destination.identity;
        state.successor = None;
        let seed = RepairSeed {
            predecessor: self.identity,
            destination: destination.identity,
            base: state.encode_base(),
        };
        destination.install_seed(&seed)?;
        Ok(seed)
    }

    fn install_seed(&self, seed: &RepairSeed) -> Result<Prefix, Error> {
        let base = rules::install_image(
            self.predecessor.as_ref(),
            &self.identity,
            &seed.predecessor,
            &seed.destination,
            &seed.base,
        )
        .ok_or(Error::Group)?;
        let prefix = Prefix::from_base(base.clone(), self.max_prefix_bytes)?;
        if self.replay(&prefix)?.successor.is_some() {
            return Err(Error::Sealed);
        }
        Ok(prefix)
    }

    pub fn identity(&self) -> Fingerprint {
        self.identity
    }
    pub fn placement(&self) -> Placement {
        self.initial.placement()
    }
    pub fn predecessor(&self) -> Option<Fingerprint> {
        self.predecessor
    }
    pub fn maximum_prefix_bytes(&self) -> usize {
        self.max_prefix_bytes
    }
    pub fn quorum(&self) -> usize {
        strict_majority(self.voters.len())
    }

    fn replay(&self, prefix: &Prefix) -> Result<State, Error> {
        if prefix.bytes > self.max_prefix_bytes {
            return Err(Error::Capacity);
        }
        let mut state = match &prefix.base {
            Some(base) => {
                State::decode_base(&self.initial, base.clone()).map_err(|_| Error::Prefix)?
            }
            None if self.predecessor.is_none() => self.initial.clone(),
            None => return Err(Error::Prefix),
        };
        for frame in &prefix.frames {
            let (time, request) =
                super::codec::decode_decision(frame.clone()).map_err(|_| Error::Prefix)?;
            if request.placement != state.placement() {
                return Err(Error::Group);
            }
            let position = state.position().checked_add(1).ok_or(Error::Capacity)?;
            state
                .apply(position, time, request)
                .map_err(|_| Error::Prefix)?;
        }
        Ok(state)
    }
}

impl Prefix {
    fn empty() -> Self {
        Self {
            base: None,
            frames: Vec::new(),
            bytes: 1,
        }
    }

    fn from_base(base: Bytes, limit: usize) -> Result<Self, Error> {
        let bytes = base
            .len()
            .checked_add(9)
            .filter(|size| *size <= limit)
            .ok_or(Error::Capacity)?;
        Ok(Self {
            base: Some(base),
            frames: Vec::new(),
            bytes,
        })
    }

    fn is_empty(&self) -> bool {
        self.base.is_none() && self.frames.is_empty()
    }

    fn append(&mut self, frame: Bytes, limit: usize) -> Result<(), Error> {
        let bytes = frame
            .len()
            .checked_add(8)
            .and_then(|size| self.bytes.checked_add(size));
        self.bytes = bytes.filter(|size| *size <= limit).ok_or(Error::Capacity)?;
        self.frames.push(frame);
        Ok(())
    }

    fn encode_into(&self, output: &mut BytesMut) {
        output.put_u8(u8::from(self.base.is_some()));
        if let Some(base) = &self.base {
            output.put_u64(base.len() as u64);
            output.put_slice(base);
        }
        for frame in &self.frames {
            output.put_u64(frame.len() as u64);
            output.put_slice(frame);
        }
    }

    fn decode(mut input: Bytes, limit: usize) -> Result<Self, Error> {
        if input.len() > limit {
            return Err(Error::Capacity);
        }
        if input.is_empty() {
            return Err(Error::Prefix);
        }
        let mut prefix = match input.get_u8() {
            0 => Self::empty(),
            1 => Self::from_base(take_body(&mut input)?, limit)?,
            _ => return Err(Error::Prefix),
        };
        while !input.is_empty() {
            prefix.append(take_body(&mut input)?, limit)?;
        }
        if prefix.is_empty() {
            return Err(Error::Prefix);
        }
        Ok(prefix)
    }

    fn identity(&self, group: Fingerprint) -> Fingerprint {
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-prefix.v2");
        hash.update(group);
        hash.update([u8::from(self.base.is_some())]);
        if let Some(base) = &self.base {
            hash.update((base.len() as u64).to_be_bytes());
            hash.update(base);
        }
        for frame in &self.frames {
            hash.update((frame.len() as u64).to_be_bytes());
            hash.update(frame);
        }
        hash.finalize().into()
    }
}

fn take_body(input: &mut Bytes) -> Result<Bytes, Error> {
    if input.len() < 8 {
        return Err(Error::Prefix);
    }
    let size = usize::try_from(input.get_u64()).map_err(|_| Error::Prefix)?;
    if size == 0 || size > input.len() {
        return Err(Error::Prefix);
    }
    Ok(input.split_to(size))
}

/// An authenticated endpoint for one voter in the installed cohort.
/// An accept reply attests durable storage of the exact named prefix.
pub trait Replica: Sync {
    fn identity(&self) -> Uuid;
    fn prepare(
        &self,
        group: Fingerprint,
        ballot: Ballot,
    ) -> impl Future<Output = Result<Promise, Error>> + Send;
    fn accept(
        &self,
        group: Fingerprint,
        ballot: Ballot,
        prefix: &Prefix,
        read_back: bool,
    ) -> impl Future<Output = Result<Vote, Error>> + Send;
}

struct PreparedRound {
    ballot: Ballot,
    voters: BTreeSet<Uuid>,
    newest_refusal: Option<Ballot>,
}

impl Group {
    /// Recovers the image confirmed by a durable quorum, without consuming a command slot.
    /// The returned image supplies observations and exact predecessors for a
    /// later command, which still enters a fresh round and rechecks authority.
    pub async fn recover<R: Replica>(&self, peers: &[R], round: u64) -> Result<State, Error> {
        let (prepared, prefix) = self.prepare(peers, round).await?;
        let state = self.replay(&prefix)?;
        if !prefix.is_empty() {
            let digest = prefix.identity(self.identity);
            self.confirm(peers, prepared, &prefix, digest, false)
                .await?;
        }
        Ok(state)
    }

    /// Rewrites the recovered image as a compact base when that saves bytes.
    /// Each acknowledging voter atomically replaces its local selected file.
    pub async fn compact<R: Replica>(&self, peers: &[R], round: u64) -> Result<(), Error> {
        let (prepared, mut prefix) = self.prepare(peers, round).await?;
        if !prefix.is_empty() {
            let state = self.replay(&prefix)?;
            if let Ok(base) = Prefix::from_base(state.encode_base(), self.max_prefix_bytes)
                && base.bytes < prefix.bytes
            {
                prefix = base;
            }
            let digest = prefix.identity(self.identity);
            self.confirm(peers, prepared, &prefix, digest, false)
                .await?;
        }
        Ok(())
    }

    /// Orders one command or returns an uncertain outcome. An identical retry
    /// uses the original request identity and deadline. The caller increments
    /// its proposed round after receiving a newer durable promise.
    ///
    /// The decision is stamped with this proposer's wall clock in milliseconds
    /// since the Unix epoch, raised to the chosen journal time if the clock is
    /// behind it. See [`Limits::clock_drift`] for the clock premise.
    pub async fn choose<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
        request: Request,
    ) -> Result<Chosen, Error> {
        self.choose_stamped(peers, round, None, request).await
    }

    /// Orders one command at an explicit journal time. A time below the
    /// chosen journal time is refused with [`Error::Time`].
    pub async fn choose_at<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
        time: u64,
        request: Request,
    ) -> Result<Chosen, Error> {
        self.choose_stamped(peers, round, Some(time), request).await
    }

    async fn choose_stamped<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
        time: Option<u64>,
        request: Request,
    ) -> Result<Chosen, Error> {
        let read_back = matches!(request.command, Command::PublishAndRotate { .. });
        if request.placement != self.initial.placement() {
            return Err(Error::Group);
        }
        let (prepared, mut prefix) = self.prepare(peers, round).await?;
        let mut state = self.replay(&prefix)?;
        let receipt = if let Some(receipt) = state.retained_receipt(&request) {
            // A promise can expose a value that had only one old vote.
            // Re-accept this prefix before releasing its receipt.
            receipt
        } else {
            if state.successor.is_some() {
                return Err(Error::Sealed);
            }
            let time = match time {
                Some(time) if time < state.time() => return Err(Error::Time),
                Some(time) => time,
                None => journal_clock().max(state.time()),
            };
            let frame = super::codec::encode_decision(time, &request);
            let position = state.position().checked_add(1).ok_or(Error::Capacity)?;
            let receipt = state
                .apply(position, time, request)
                .map_err(|_| Error::Prefix)?;
            let appended = prefix.append(frame, self.max_prefix_bytes);
            if appended.is_err() || matches!(receipt.outcome, Ok(Outcome::Trimmed(_))) {
                let compact = Prefix::from_base(state.encode_base(), self.max_prefix_bytes);
                match (appended, compact) {
                    (Err(_), Ok(base)) => prefix = base,
                    (Ok(()), Ok(base)) if base.bytes < prefix.bytes => prefix = base,
                    (Err(error), Err(_)) => return Err(error),
                    (Ok(()), _) => {}
                }
            }
            receipt
        };
        let ballot = prepared.ballot;
        let digest = prefix.identity(self.identity);
        let images = self
            .confirm(peers, prepared, &prefix, digest, read_back)
            .await?;
        Ok(Chosen {
            group: self.identity,
            cohort_size: self.voters.len(),
            ballot,
            prefix: digest,
            voters: images.iter().map(|evidence| evidence.voter).collect(),
            images,
            receipt,
            state,
        })
    }

    async fn prepare<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
    ) -> Result<(PreparedRound, Prefix), Error> {
        if round == 0 {
            return Err(Error::Group);
        }
        let mut identities = BTreeSet::new();
        for peer in peers {
            let id = peer.identity();
            if !register_peer(&self.voters, &mut identities, id) {
                return Err(Error::Group);
            }
        }
        if peers.len() < self.quorum() {
            return Err(Error::Quorum);
        }

        let ballot = Ballot {
            round,
            nonce: Uuid::new_v4(),
        };
        let mut prepares: FuturesUnordered<_> = peers
            .iter()
            .map(|peer| async move { (peer.identity(), peer.prepare(self.identity, ballot).await) })
            .collect();
        let mut voters = BTreeSet::new();
        let mut winner: Option<Accepted> = None;
        let mut refusal = None;
        while let Some((expected, reply)) = prepares.next().await {
            match reply {
                Ok(reply) if reply.voter == expected && reply.ballot == ballot => {
                    if let Some(accepted) = reply.accepted {
                        if accepted.ballot >= ballot {
                            return Err(Error::Prefix);
                        }
                        choose_base(&mut winner, accepted)?;
                    }
                    voters.insert(expected);
                    if rules::strict_majority(self.voters.len(), voters.len()) {
                        break;
                    }
                }
                Err(Error::Deposed(newer)) => {
                    refusal = Some(refusal.map_or(newer, |old: Ballot| old.max(newer)))
                }
                _ => {}
            }
        }
        if voters.len() < self.quorum() {
            return Err(refusal.map_or(Error::Quorum, Error::Deposed));
        }
        Ok((
            PreparedRound {
                ballot,
                voters,
                newest_refusal: refusal,
            },
            winner.map_or_else(Prefix::empty, |accepted| accepted.prefix),
        ))
    }

    async fn confirm<R: Replica>(
        &self,
        peers: &[R],
        prepared: PreparedRound,
        prefix: &Prefix,
        digest: Fingerprint,
        read_back: bool,
    ) -> Result<Vec<VoterSlots>, Error> {
        let PreparedRound {
            ballot,
            voters: promised,
            newest_refusal: mut refusal,
        } = prepared;
        let mut accepts: FuturesUnordered<_> = peers
            .iter()
            .filter(|peer| promised.contains(&peer.identity()))
            .map(|peer| async move {
                (
                    peer.identity(),
                    peer.accept(self.identity, ballot, prefix, read_back).await,
                )
            })
            .collect();
        let mut voters = Vec::with_capacity(self.quorum());
        while let Some((expected, reply)) = accepts.next().await {
            match reply {
                Ok(vote) => {
                    if record_vote(&mut voters, expected, ballot, digest, read_back, vote)
                        && rules::strict_majority(self.voters.len(), voters.len())
                    {
                        voters.sort_unstable_by_key(|evidence| evidence.voter);
                        let configured: Vec<_> = self.voters.iter().map(Uuid::as_u128).collect();
                        let counted: Vec<_> =
                            voters.iter().map(|evidence| evidence.voter.as_u128()).collect();
                        if !rules::configured_majority(&configured, &counted) {
                            return Err(Error::Group);
                        }
                        return Ok(voters);
                    }
                }
                Err(Error::Deposed(newer)) => {
                    refusal = Some(refusal.map_or(newer, |old| old.max(newer)))
                }
                _ => {}
            }
        }
        Err(refusal.map_or(Error::Quorum, Error::Deposed))
    }
}

fn choose_base(winner: &mut Option<Accepted>, candidate: Accepted) -> Result<(), Error> {
    if let Some(current) = winner {
        match rules::recovery_choice(current.ballot.rank(), candidate.ballot.rank()) {
            rules::RecoveryChoice::Keep => return Ok(()),
            rules::RecoveryChoice::Tie => {
                return if candidate.prefix == current.prefix {
                    Ok(())
                } else {
                    Err(Error::Diverged)
                };
            }
            rules::RecoveryChoice::Replace => {}
        }
    }
    *winner = Some(candidate);
    Ok(())
}

/// The proposer's wall clock in milliseconds since the Unix epoch.
fn journal_clock() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}
