#![feature(proc_macro_hygiene)]

pub type ObjectName = [u8; 32];

#[path = "../../../src/ordered/admission.rs"]
mod admission;

#[path = "../../../src/ordered/budget.rs"]
mod budget;

#[path = "../../../src/ordered/object_names.rs"]
mod production;

mod laws;

fn main() {}
