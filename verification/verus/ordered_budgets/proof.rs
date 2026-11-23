#![feature(proc_macro_hygiene)]
#![allow(non_snake_case)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/budget.rs"]
mod production;
mod laws;

fn main() {}
