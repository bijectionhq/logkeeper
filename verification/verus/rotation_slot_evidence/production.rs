use std::collections::VecDeque;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpecImpl;

#[path = "../../../src/ordered/admission.rs"]
pub mod admission;
#[path = "../../../src/ordered/replication/evidence.rs"]
pub mod evidence;
#[path = "../../../src/ordered/codec/service/rotation.rs"]
mod rotation;
#[path = "../../../src/ordered/replication/rotation.rs"]
mod assemble;

pub use evidence::{RotationSlots, SlotPair, Vote, VoterSlots};

pub type Fingerprint = [u8; 32];

// The exact unsigned, big-endian representation of a UUID.
#[derive(Clone, Copy)]
pub struct Uuid(pub u128);

impl Uuid {
    #[verus_spec(value => ensures value == self.0)]
    pub fn as_u128(&self) -> u128 { self.0 }

    #[verus_spec(value => ensures value == (self.0 == 0))]
    pub fn is_nil(&self) -> bool { self.0 == 0 }
}

#[derive(Clone, Copy)]
pub struct Ballot {
    pub round: u64,
    pub nonce: Uuid,
}

// Opaque identities for whole cuts and checkpoints. Equality and the cut
// projection are the only operations needed on these identities.
#[derive(Clone, Copy)]
pub struct Cut { pub next_lsn: u64, pub identity: u64 }

verus! {
impl PartialEqSpecImpl for Cut {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool { *self == *other }
}
impl PartialEq for Cut {
    fn eq(&self, other: &Self) -> bool { self.next_lsn == other.next_lsn && self.identity == other.identity }
}
}

#[derive(Clone, Copy)]
pub struct Checkpoint {
    pub cut: Cut,
    pub identity: u64,
}
verus! {
impl PartialEqSpecImpl for Checkpoint {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool { *self == *other }
}
impl PartialEq for Checkpoint {
    fn eq(&self, other: &Self) -> bool {
        self.cut == other.cut && self.identity == other.identity
    }
}
}

#[derive(Clone, Copy)]
pub struct Grant { pub enrollment: u64, pub key_generation: u64 }

#[derive(Clone, Copy)]
pub struct Recovery {
    pub id: u64,
    pub owner: u64,
    pub checkpoint: Checkpoint,
    pub admitted_at: u64,
    pub start: Cut,
    pub through: Cut,
}

#[derive(Clone, Copy)]
pub enum Outcome {
    Granted { grant: Grant, recovery: Recovery },
    Other,
}

#[derive(Clone, Copy)]
pub struct Receipt {
    pub placement: u64,
    pub principal: u64,
    pub request: u64,
    pub outcome: Result<Outcome, ()>,
    pub position: u64,
}

pub enum Command {
    PublishAndRotate { grant: Grant, checkpoint: Checkpoint },
    Other,
}

pub struct Request {
    pub placement: u64,
    pub principal: u64,
    pub id: u64,
    pub command: Command,
}

pub struct AppendResult { pub lsn: u64 }
pub struct Record { pub result: AppendResult, pub grant: Grant }

pub struct Authority {
    pub key_generation: u64,
}

pub struct State {
    pub records: VecDeque<Record>,
    pub authority: Authority,
    pub position: u64,
    pub checkpoint: Checkpoint,
}

impl State {
    #[verus_spec(out => ensures out == self.position)]
    pub fn position(&self) -> u64 { self.position }

    #[verus_spec(out => ensures out == self.checkpoint)]
    pub fn checkpoint(&self) -> Checkpoint { self.checkpoint }
}

// Set semantics supplied by the standard library's BTreeSet operations.
pub struct BTreeSet<T> { pub members: Ghost<Set<T>> }

verus! {
impl<T> BTreeSet<T> {
    #[verifier::external_body]
    pub fn contains(&self, value: &T) -> (out: bool)
        ensures out == self.members@.contains(*value),
    { unimplemented!() }

    #[verifier::external_body]
    pub fn insert(&mut self, value: T) -> (out: bool)
        ensures out == !old(self).members@.contains(value),
            final(self).members@ == old(self).members@.insert(value),
    { unimplemented!() }
}
}

pub struct Chosen {
    pub state: State,
    pub receipt: Receipt,
    pub group: Fingerprint,
    pub cohort_size: usize,
    pub ballot: Ballot,
    pub prefix: Fingerprint,
    pub images: Vec<VoterSlots>,
}

verus! {

pub open spec fn zeros() -> Seq<u8> {
    Seq::new(32, |_: int| 0u8)
}

pub open spec fn well_formed(pair: SlotPair) -> bool {
    let selected = pair.images@[pair.selected as int];
    let alternate = pair.images@[1 - pair.selected as int];
    pair.selected < 2 && 0 < alternate.generation
        && alternate.generation as int + 1 == selected.generation as int
        && alternate.digest@ != zeros()
        && selected.digest@ != zeros()
        && selected.digest@ != alternate.digest@
}

pub open spec fn record_matches(
    vote: Vote, voter: Uuid, ballot: Ballot, digest: Fingerprint, read_back: bool,
) -> bool {
    vote.voter == voter && vote.ballot == ballot && vote.digest@ == digest@
        && well_formed(vote.slots) && vote.read_back == read_back
}

pub open spec fn valid_voter_prefix(voters: Seq<VoterSlots>, n: int) -> bool {
    &&& 0 <= n <= voters.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] voters[i].voter.0 != 0 && well_formed(voters[i].slots)
    &&& forall|i: int| 0 < i < n ==> voters[i - 1].voter.0 < #[trigger] voters[i].voter.0
}

pub open spec fn covers_rotation(evidence: &RotationSlots, receipt: Receipt) -> bool {
    match receipt.outcome {
        Ok(Outcome::Granted { grant, recovery }) =>
            evidence.group@ != zeros() && evidence.ballot.round != 0
            && evidence.ballot.nonce.0 != 0 && evidence.prefix@ != zeros()
            && receipt.position != 0 && evidence.position >= receipt.position
            && recovery.id == receipt.request && recovery.owner == grant.enrollment
            && evidence.checkpoint == recovery.checkpoint && recovery.admitted_at == receipt.position
            && recovery.start == evidence.checkpoint.cut && recovery.through == evidence.checkpoint.cut
            && evidence.key_generation == grant.key_generation && evidence.key_generation > 1
            && evidence.cohort_size >= 3 && evidence.cohort_size % 2 == 1
            && evidence.voters@.len() == evidence.cohort_size / 2 + 1
            && valid_voter_prefix(evidence.voters@, evidence.voters@.len() as int),
        _ => false,
    }
}

pub open spec fn suffix_matches(
    rows: Seq<Record>, next_lsn: u64, generation: u64, n: int,
) -> bool {
    0 <= n <= rows.len() && forall|i: int| 0 <= i < n
        && #[trigger] rows[i].result.lsn >= next_lsn ==> rows[i].grant.key_generation == generation
}

pub open spec fn agrees_with_rotation(chosen: &Chosen, request: &Request, result: &RotationSlots) -> bool {
    request.command matches Command::PublishAndRotate { grant, checkpoint }
    && request.placement == chosen.receipt.placement && request.principal == chosen.receipt.principal
    && request.id == chosen.receipt.request
    && grant.key_generation as int + 1 == chosen.state.authority.key_generation as int
    && checkpoint == chosen.state.checkpoint && checkpoint == result.checkpoint
    && suffix_matches(chosen.state.records@, checkpoint.cut.next_lsn, chosen.state.authority.key_generation,
        chosen.state.records@.len() as int)
    && result.group@ == chosen.group@ && result.cohort_size == chosen.cohort_size
    && result.ballot == chosen.ballot && result.prefix@ == chosen.prefix@
    && result.position == chosen.state.position && result.key_generation == chosen.state.authority.key_generation
    && result.voters@ == chosen.images@ && covers_rotation(result, chosen.receipt)
}

pub open spec fn be(value: nat, width: nat) -> Seq<u8> {
    Seq::new(width, |index: int| (value / pow256((width - 1 - index) as nat)) as u8)
}

pub open spec fn pow256(power: nat) -> nat
    decreases power,
{
    if power == 0 { 1 } else { 256 * pow256((power - 1) as nat) }
}

pub open spec fn voter_wire(voter: VoterSlots) -> Seq<u8> {
    let a = voter.slots.images@[0];
    let b = voter.slots.images@[1];
    be(voter.voter.0 as nat, 16) + seq![voter.slots.selected]
        + be(a.generation as nat, 8) + a.digest@
        + be(b.generation as nat, 8) + b.digest@
}

pub open spec fn voters_wire(voters: Seq<VoterSlots>) -> Seq<u8>
    decreases voters.len(),
{
    if voters.len() == 0 { Seq::empty() }
    else { voters_wire(voters.drop_last()) + voter_wire(voters.last()) }
}

pub uninterp spec fn checkpoint_wire(checkpoint: Checkpoint) -> Seq<u8>;

pub open spec fn rotation_header(evidence: &RotationSlots) -> Seq<u8> {
    evidence.group@ + be(evidence.cohort_size as nat, 8) + be(evidence.ballot.round as nat, 8)
        + be(evidence.ballot.nonce.0 as nat, 16) + evidence.prefix@
        + be(evidence.position as nat, 8) + checkpoint_wire(evidence.checkpoint)
        + be(evidence.key_generation as nat, 8) + be(evidence.voters@.len(), 8)
}

pub struct BytesMut { pub contents: Ghost<Seq<u8>> }

// Leaf contracts for bytes::BufMut and the existing UUID/checkpoint encoders.
pub trait BufMut {
    spec fn contents(&self) -> Seq<u8>;

    fn put_slice(&mut self, bytes: &[u8])
        ensures final(self).contents() == old(self).contents() + bytes@;
    fn put_u8(&mut self, value: u8)
        ensures final(self).contents() == old(self).contents() + seq![value];
    fn put_u64(&mut self, value: u64)
        ensures final(self).contents() == old(self).contents() + be(value as nat, 8);
}

impl BufMut for BytesMut {
    open spec fn contents(&self) -> Seq<u8> { self.contents@ }

    #[verifier::external_body]
    fn put_slice(&mut self, bytes: &[u8]) { unimplemented!() }

    #[verifier::external_body]
    fn put_u8(&mut self, value: u8) { unimplemented!() }

    #[verifier::external_body]
    fn put_u64(&mut self, value: u64) { unimplemented!() }
}

#[verifier::external_body]
pub fn uuid(output: &mut BytesMut, value: Uuid)
    ensures final(output).contents@ == old(output).contents@ + be(value.0 as nat, 16),
{ unimplemented!() }

#[verifier::external_body]
pub fn checkpoint(output: &mut BytesMut, value: Checkpoint)
    ensures final(output).contents@ == old(output).contents@ + checkpoint_wire(value),
{ unimplemented!() }

}
