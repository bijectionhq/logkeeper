#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/replication/rules.rs"]
mod production;
#[path = "../rotation_slot_evidence/production.rs"]
mod rotation_support;

pub use rotation_support::admission;
#[path = "../../../src/ordered/cohort.rs"]
pub mod cohort;

mod ordered {
    pub use crate::{admission, cohort};
}

mod laws;

fn main() {}
