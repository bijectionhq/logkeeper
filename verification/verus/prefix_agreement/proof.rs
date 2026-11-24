#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/replication/rules.rs"]
mod production;
#[path = "../rotation_slot_evidence/production.rs"]
mod rotation_support;

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
