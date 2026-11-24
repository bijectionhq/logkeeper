#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;
#[path = "../../../src/ordered/receipt.rs"]
mod production;

mod laws;

fn main() {}
