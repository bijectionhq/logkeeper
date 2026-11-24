#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/replication/rules.rs"]
mod production;
#[path = "../rotation_slot_evidence/production.rs"]
mod rotation_support;

mod ordered {
    pub use crate::rotation_support::admission;
}

mod laws;

fn main() {}
