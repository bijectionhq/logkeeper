#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;

#[path = "../../../src/ordered/writer.rs"]
mod writer;
#[path = "../../../src/ordered/lease.rs"]
mod production;

mod laws;

fn main() {}
