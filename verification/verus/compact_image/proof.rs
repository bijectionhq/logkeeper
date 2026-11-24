#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
#[path = "../../../src/ordered/refusal.rs"]
mod refusal;
use refusal::Refusal;
#[path = "../../../src/ordered/receipt.rs"]
mod receipt;
mod ordered {
    pub(crate) use crate::{admission, receipt};
}
#[path = "../../../src/ordered/codec/snapshot_checks.rs"]
mod production;

mod layout;
mod laws;

fn main() {}
