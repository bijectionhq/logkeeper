#![feature(proc_macro_hygiene)]
#![allow(non_snake_case)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/budget.rs"]
mod budget;
#[path = "../../../src/ordered/checkpoint_guards.rs"]
mod checkpoint_guards;
#[path = "../../../src/ordered/cohort.rs"]
mod cohort;
#[path = "../../../src/ordered/object_withdrawal.rs"]
mod object_withdrawal;
#[path = "../../../src/ordered/receipt.rs"]
mod receipt;
#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;
#[path = "../../../src/ordered/writer.rs"]
mod writer;
use writer::Cut;
#[path = "../../../src/ordered/rotation.rs"]
mod rotation;
#[path = "../../../src/ordered/reducer_request.rs"]
mod request;
#[path = "../../../src/ordered/reducer_retention.rs"]
mod retention;
#[path = "../../../src/ordered/reducer.rs"]
mod production;
mod laws;

fn main() {}
