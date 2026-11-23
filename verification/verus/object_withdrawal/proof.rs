#![feature(proc_macro_hygiene)]
#![allow(non_snake_case)]

#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;
#[path = "../../../src/ordered/object_withdrawal.rs"]
mod production;
mod laws;

fn main() {}
