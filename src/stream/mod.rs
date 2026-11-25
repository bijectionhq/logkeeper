//! The stream journal: a writer-driven quorum per stream over one shared write-ahead log per keeper.
//! Specification: `verification/target-journal.md`. Contract: the `journal-contract` crate.

pub mod codec;
#[cfg(feature = "stream")]
pub mod consensus;
pub mod keeper;
mod proposer;
pub mod timed;
#[cfg(feature = "stream")]
pub mod transport;
pub mod wire;
pub mod writer;
