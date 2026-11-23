#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;

#[path = "../../../src/ordered/writer.rs"]
mod production;

mod laws;

fn main() {}
