//! Messages inside `Request::Authenticated` and `Reply::Authenticated`. They are
//! bincode bodies so the keeper protobuf schema gains one opaque field each way.
//! Stream-level refusals (`NotFound`, `Deleted`, `AboveHead`, ...) use the outer
//! `Reply::Refused`.

use std::io;

use bincode::Options;
use bytes::Bytes;
use journal_contract::Lsn;
use serde::{Deserialize, Serialize, de::DeserializeOwned};

use super::{Hash, Head, HeadSignature, Leaf, SignedHead};

/// Leaves in one `Leaves` reply or `Seed` request.
pub(crate) const LEAF_PAGE: usize = 1024;
const MAX_BODY_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum AuthRequest {
    /// Whether this keeper authenticates streams and holds every leaf below its floor.
    Status,
    /// Sign the committed prefix through `size`, which must not exceed the keeper's head.
    Sign { size: u64 },
    /// Committed leaves in `[from, through]`, at most `LEAF_PAGE`.
    Leaves { from: Lsn, through: u64 },
    /// The inclusion path of `at` in the prefix through `size`.
    Path { at: Lsn, size: u64 },
    /// The consistency path between two prefix sizes.
    Consistency { earlier: u64, later: u64 },
    /// Install leaves this keeper never held because it was replaced in or synced
    /// past a trimmed prefix. Pages start at the keeper's first missing leaf; the
    /// last page carries a quorum-signed head that the keeper checks against the
    /// staged leaves and its own retained records before installing them.
    Seed {
        from: Lsn,
        leaves: Vec<Leaf>,
        head: Option<SignedHead>,
    },
}

impl AuthRequest {
    /// Seeding writes keeper files, so it needs writer authorization.
    pub(crate) fn mutates(&self) -> bool {
        matches!(self, Self::Seed { .. })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum AuthReply {
    /// `ingested` leaves are installed contiguously from LSN 1. `complete` when
    /// they reach the keeper's floor, so the keeper can sign any retained size.
    Status {
        ingested: u64,
        floor: Lsn,
        complete: bool,
    },
    Signed {
        head: Head,
        signature: HeadSignature,
    },
    Leaves(Vec<Leaf>),
    Path {
        leaf: Leaf,
        path: Vec<Hash>,
    },
    Consistency(Vec<Hash>),
    Seeded {
        ingested: u64,
    },
    /// The keeper lacks leaves `ingested + 1 .. floor` and needs a `Seed`.
    Missing {
        ingested: u64,
        floor: Lsn,
    },
    /// This keeper does not keep authenticated history.
    Unsupported,
}

fn options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
        .with_limit(MAX_BODY_BYTES)
}

pub(crate) fn encode(value: &impl Serialize) -> io::Result<Bytes> {
    options()
        .serialize(value)
        .map(Bytes::from)
        .map_err(io::Error::other)
}

pub(crate) fn decode<T: DeserializeOwned>(bytes: &[u8]) -> io::Result<T> {
    options().deserialize(bytes).map_err(io::Error::other)
}
