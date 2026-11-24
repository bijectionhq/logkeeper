#![feature(proc_macro_hygiene)]

#[path = "../../../src/ordered/admission.rs"]
mod admission;
mod ordered {
    pub(crate) use crate::admission;
}

pub type ObjectName = [u8; 32];
#[path = "../../../src/ordered/budget.rs"]
mod budget;
#[path = "../../../src/ordered/object_names.rs"]
mod object_names;
#[path = "../../../src/ordered/codec/frame.rs"]
mod production;

mod domains;
mod laws;

fn main() {}
