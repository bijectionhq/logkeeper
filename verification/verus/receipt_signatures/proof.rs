#![feature(proc_macro_hygiene)]

extern crate self as bytes;
extern crate self as sha2;
extern crate self as uuid;

pub use contracts::{BufMut, Bytes, BytesMut, Digest, Sha256, Uuid};

mod contracts;
mod laws;
mod ordered;
mod production;
mod reference;

fn main() {}
