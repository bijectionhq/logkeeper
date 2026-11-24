#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/replication/rules.rs"]
mod production;
use production as rules;
#[path = "../rotation_slot_evidence/production.rs"]
mod rotation_support;
use rotation_support::{Ballot, Fingerprint, Uuid, Vote, VoterSlots, evidence, record_matches};

#[path = "../../../src/ordered/replication/confirmation.rs"]
mod confirmation;

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/cohort.rs"]
pub mod cohort;

mod ordered {
    pub use crate::cohort;
    pub use crate::rotation_support::admission;
}

mod laws;

fn main() {}
