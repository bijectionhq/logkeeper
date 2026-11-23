// Shapes projected from ordered.rs, replication.rs and service/wire.rs.
// Non-barrier command and outcome variants are opaque for these laws.
use crate::contracts::{BytesMut, Uuid};
use vstd::prelude::*;

verus! {

pub type Fingerprint = [u8; 32];

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Placement {
    pub deployment: Uuid,
    pub incarnation: Uuid,
    pub group: Uuid,
    pub generation: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Enrollment {
    pub worker: Uuid,
    pub serial: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RequestId {
    pub nonce: Uuid,
    pub expires_at: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Cut {
    pub next_lsn: u64,
    pub history: Fingerprint,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Custody {
    pub allocation: Uuid,
    pub revision: u64,
    pub provider: Fingerprint,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Checkpoint {
    pub cut: Cut,
    pub root: Fingerprint,
    pub manifest: Fingerprint,
    pub custody: Custody,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Hold {
    pub id: RequestId,
    pub owner: Enrollment,
    pub admitted_at: u64,
    pub checkpoint: Checkpoint,
    pub start: Cut,
    pub through: Cut,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Principal {
    Administrator,
    Worker(Enrollment),
    Custodian,
    RouteReader,
}

pub enum Command {
    Barrier,
    Other,
}

pub struct Request {
    pub placement: Placement,
    pub principal: Principal,
    pub id: RequestId,
    pub command: Command,
}

#[derive(Clone, Copy)]
pub enum Outcome {
    Barrier { read: Hold },
    Other,
}

#[derive(Clone, Copy)]
pub enum Refusal {
    Invalid,
    Other,
}

#[derive(Clone, Copy)]
pub struct Receipt {
    pub placement: Placement,
    pub principal: Principal,
    pub request: RequestId,
    pub position: u64,
    pub outcome: Result<Outcome, Refusal>,
}

#[derive(Clone, Copy)]
pub struct BarrierClaim {
    pub placement: Placement,
    pub read: Hold,
}

pub assume_specification[<Placement as PartialEq>::eq](a: &Placement, b: &Placement) -> (out: bool)
    ensures out == (*a == *b);
pub assume_specification[<Principal as PartialEq>::eq](a: &Principal, b: &Principal) -> (out: bool)
    ensures out == (*a == *b);
pub assume_specification[<RequestId as PartialEq>::eq](a: &RequestId, b: &RequestId) -> (out: bool)
    ensures out == (*a == *b);
pub assume_specification[<Cut as PartialEq>::eq](a: &Cut, b: &Cut) -> (out: bool)
    ensures out == (*a == *b);
pub assume_specification[<Hold as PartialEq>::eq](a: &Hold, b: &Hold) -> (out: bool)
    ensures out == (*a == *b);

pub struct RotationSlots {
    pub group: Fingerprint,
    pub evidence: Seq<u8>,
}

impl RotationSlots {
    #[verifier::external_body]
    pub fn covers(&self, receipt: Receipt) -> (out: bool)
        ensures out == covers(*self, receipt),
    { unimplemented!() }

    #[verifier::external_body]
    pub fn encode(&self, output: &mut BytesMut)
        ensures final(output)@ == old(output)@ + evidence_bytes(*self),
    { unimplemented!() }
}

pub uninterp spec fn covers(evidence: RotationSlots, receipt: Receipt) -> bool;
pub uninterp spec fn evidence_bytes(evidence: RotationSlots) -> Seq<u8>;

}

pub mod daemon {
    pub use crate::contracts::invalid;
    pub use crate::production::receipt_keys;
    pub mod sign {
        pub use crate::contracts::verify_bytes;
    }
}

pub mod replication {
    pub use super::RotationSlots;
}

pub mod service {
    pub mod wire {
        use crate::ordered::{BarrierClaim, Fingerprint, RotationSlots};

        #[derive(Clone, Copy)]
        pub struct Signature {
            pub issuer: Fingerprint,
            pub proof: [u8; 64],
        }

        #[derive(Clone, Copy)]
        pub struct SignedBarrier {
            pub claim: BarrierClaim,
            pub signature: Signature,
        }

        pub struct SignedRotationSlots {
            pub evidence: RotationSlots,
            pub signature: Signature,
        }
    }
}
