#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/cohort.rs"]
mod production;
#[path = "../../../src/ordered/admission.rs"]
mod admission;

mod laws;

fn main() {}
