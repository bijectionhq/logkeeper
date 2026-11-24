#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;
#[path = "../../../src/ordered/writer.rs"]
mod writer;
use writer::Cut;
#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/checkpoint_guards.rs"]
mod checkpoint_guards;
#[path = "../../../src/ordered/rotation.rs"]
mod rotation;
#[path = "../../../src/ordered/replay_bounds.rs"]
mod replay_bounds;
#[path = "../../../src/ordered/lease.rs"]
mod lease;
#[path = "../../../src/ordered/lease_reducer.rs"]
mod production;

mod laws;

fn main() {}
