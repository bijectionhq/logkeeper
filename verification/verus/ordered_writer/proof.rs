#![feature(proc_macro_hygiene)]
#![allow(non_snake_case)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/budget.rs"]
mod budget;
use budget::AppendClass;

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;

#[path = "../../../src/ordered/writer.rs"]
mod production;

#[path = "../../../src/ordered/retention.rs"]
mod retention;

mod laws;

fn main() {}
