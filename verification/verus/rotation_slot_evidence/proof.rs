#![feature(proc_macro_hygiene)]

mod laws;
mod production;

mod ordered {
    pub use crate::production::admission;
}

fn main() {}
