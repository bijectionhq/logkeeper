#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;

#[path = "../../../src/ordered/writer.rs"]
mod writer;
use writer::Cut;

#[path = "../../../src/ordered/rotation.rs"]
mod production;

#[path = "../../../src/ordered/admission.rs"]
mod admission;

#[path = "../../../src/ordered/checkpoint_guards.rs"]
mod checkpoint_guards;

mod laws;

fn main() {}
