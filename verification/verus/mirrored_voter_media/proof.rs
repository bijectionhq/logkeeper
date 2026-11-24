#![feature(proc_macro_hygiene)]

mod production;
mod ordered {
    pub(crate) use crate::production::admission;
}
mod laws;

fn main() {}
