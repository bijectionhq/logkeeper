//! Verus entry point for the admission decisions called by Logkeeper.
#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/admission.rs"]
mod production;

mod laws;

fn main() {}
