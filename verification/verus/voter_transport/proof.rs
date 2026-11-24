#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/replication/slot_header.rs"]
mod slot_header;

#[path = "../../../src/ordered/replication/transport_fields.rs"]
mod production;

mod laws;

fn main() {}
