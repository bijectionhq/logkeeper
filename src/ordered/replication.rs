//! Fixed-group prefix agreement over the ordered reducer.
//!
//! Each ballot is used for one proposed extension. Recovery adopts the
//! greatest accepted ballot and its exact prefix.
//! Transport implementations supply authenticated replies from the named
//! durable journals in the installed cohort.

mod disk;
pub mod transport;

pub use disk::DurableVoter;

use super::{
    BarrierClaim, Checkpoint, Fingerprint, Limits, Outcome, Placement, Receipt, Refusal, Request,
    State, Window,
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

#[derive(Clone)]
pub struct Group {
    identity: Fingerprint,
    initial: State,
    voters: BTreeSet<Uuid>,
    max_prefix_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prefix {
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

#[derive(Clone, Copy, Debug)]
pub struct Vote {
    pub voter: Uuid,
    pub ballot: Ballot,
    pub digest: Fingerprint,
}

pub struct Chosen {
    ballot: Ballot,
    prefix: Fingerprint,
    voters: Vec<Uuid>,
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
        let Outcome::Barrier { grant, read } = self.receipt.outcome.ok()? else {
            return None;
        };
        self.state.held_replay(self.receipt.principal, read).ok()?;
        Some(BarrierClaim {
            placement: self.receipt.placement,
            grant,
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
    #[error("ordered journal I/O failed: {0}")]
    Io(#[from] std::io::Error),
}

impl Group {
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
        let initial = State::new(placement, limits, checkpoint, window)?;
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-group.v1");
        hash.update(placement.deployment.as_bytes());
        hash.update(placement.incarnation.as_bytes());
        hash.update(placement.group.as_bytes());
        hash.update(placement.generation.to_be_bytes());
        hash.update(checkpoint.cut.history);
        hash.update(checkpoint.root);
        hash.update(checkpoint.manifest);
        hash.update(window.allocation.as_bytes());
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
        for voter in &roster {
            hash.update(voter.as_bytes());
        }
        Ok(Self {
            identity: hash.finalize().into(),
            initial,
            voters: roster,
            max_prefix_bytes,
        })
    }

    pub fn identity(&self) -> Fingerprint {
        self.identity
    }
    pub fn quorum(&self) -> usize {
        self.voters.len() / 2 + 1
    }

    fn replay(&self, prefix: &Prefix) -> Result<State, Error> {
        if prefix.bytes > self.max_prefix_bytes {
            return Err(Error::Capacity);
        }
        let mut state = self.initial.clone();
        for frame in &prefix.frames {
            let request = Request::decode(frame.clone()).map_err(|_| Error::Prefix)?;
            if request.placement != state.placement() {
                return Err(Error::Group);
            }
            let position = state.position().checked_add(1).ok_or(Error::Capacity)?;
            state.apply(position, request).map_err(|_| Error::Prefix)?;
        }
        Ok(state)
    }
}

impl Prefix {
    fn empty() -> Self {
        Self {
            frames: Vec::new(),
            bytes: 0,
        }
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
        for frame in &self.frames {
            output.put_u64(frame.len() as u64);
            output.put_slice(frame);
        }
    }

    fn decode(mut input: Bytes, limit: usize) -> Result<Self, Error> {
        if input.len() > limit {
            return Err(Error::Capacity);
        }
        let mut prefix = Self::empty();
        while !input.is_empty() {
            if input.len() < 8 {
                return Err(Error::Prefix);
            }
            let size = usize::try_from(input.get_u64()).map_err(|_| Error::Prefix)?;
            if size == 0 || size > input.len() {
                return Err(Error::Prefix);
            }
            prefix.append(input.split_to(size), limit)?;
        }
        if prefix.frames.is_empty() {
            return Err(Error::Prefix);
        }
        Ok(prefix)
    }

    fn identity(&self, group: Fingerprint) -> Fingerprint {
        let mut hash = Sha256::new();
        hash.update(b"logkeeper.ordered-prefix.v1");
        hash.update(group);
        for frame in &self.frames {
            hash.update((frame.len() as u64).to_be_bytes());
            hash.update(frame);
        }
        hash.finalize().into()
    }
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
        if !prefix.frames.is_empty() {
            let digest = prefix.identity(self.identity);
            self.confirm(peers, prepared, &prefix, digest).await?;
        }
        Ok(state)
    }

    /// Orders one command or returns an uncertain outcome. An identical retry
    /// uses the original request identity and deadline. The caller increments
    /// its proposed round after receiving a newer durable promise.
    pub async fn choose<R: Replica>(
        &self,
        peers: &[R],
        round: u64,
        request: Request,
    ) -> Result<Chosen, Error> {
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
            prefix.append(request.encode(), self.max_prefix_bytes)?;
            let position = state.position().checked_add(1).ok_or(Error::Capacity)?;
            state.apply(position, request).map_err(|_| Error::Prefix)?
        };
        let ballot = prepared.ballot;
        let digest = prefix.identity(self.identity);
        let voters = self.confirm(peers, prepared, &prefix, digest).await?;
        Ok(Chosen {
            ballot,
            prefix: digest,
            voters,
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
            if !self.voters.contains(&id) || !identities.insert(id) {
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
                    if voters.len() >= self.quorum() {
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
    ) -> Result<Vec<Uuid>, Error> {
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
                    peer.accept(self.identity, ballot, prefix).await,
                )
            })
            .collect();
        let mut voters = BTreeSet::new();
        while let Some((expected, reply)) = accepts.next().await {
            match reply {
                Ok(vote)
                    if vote.voter == expected && vote.ballot == ballot && vote.digest == digest =>
                {
                    voters.insert(expected);
                    if voters.len() >= self.quorum() {
                        return Ok(voters.into_iter().collect());
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
        if candidate.ballot < current.ballot {
            return Ok(());
        }
        if candidate.ballot == current.ballot {
            if candidate.prefix != current.prefix {
                return Err(Error::Diverged);
            }
            return Ok(());
        }
    }
    *winner = Some(candidate);
    Ok(())
}
