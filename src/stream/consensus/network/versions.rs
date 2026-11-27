//! Which wire version introduced each variant of the consensus wire enums.
//!
//! The rule: a variant of `Frame`, `Request`, `PeerRequest`, `Reply`,
//! `Outcome` or `JournalError` is only ever appended, and each is classified
//! here by the version that introduced it. An N-1 peer decodes only the
//! variants it knew, so nothing introduced later may reach it: a request is
//! refused locally (`supported_on`), a reply needs an N-1 mapping
//! (`ReplyV1::from_reply`, `outcome_v1`), and a receiver refuses an N-only
//! variant arriving on an N-1 connection. The classifications are exhaustive
//! matches, so a new variant does not compile until it is classified, and
//! the receiver's variant bounds come from the enums themselves. The tests
//! pin the N-1 variant lists, which change only when the ALPNs move.

use std::sync::LazyLock;

use journal_contract::JournalError;
use serde::{
    Deserializer,
    de::{self, DeserializeOwned, Visitor},
};

use super::{Frame, PeerRequest, Reply, Request, WireVersion};
use crate::stream::consensus::state::Outcome;

impl Request {
    /// The wire version that introduced this request.
    pub(in crate::stream::consensus) fn introduced(&self) -> WireVersion {
        match self {
            Self::Claim(genesis)
            | Self::ReadAt { genesis, .. }
            | Self::StageReplica { genesis, .. }
            | Self::InstallReplica { genesis, .. }
            | Self::StageRecovered { genesis, .. }
                if genesis.immutable =>
            {
                WireVersion::Current
            }
            Self::Claim(_)
            | Self::Locate(_)
            | Self::Stage(_)
            | Self::Bootstrap(_)
            | Self::Create(_)
            | Self::Seal { .. }
            | Self::Append { .. }
            | Self::Read { .. }
            | Self::Head(_)
            | Self::Trim { .. }
            | Self::Delete(_)
            | Self::Configuration(_)
            | Self::Replace { .. }
            | Self::PlacementProof(_)
            | Self::StageReplica { .. }
            | Self::InstallReplica { .. }
            | Self::LocalCopy(_)
            | Self::RetireCopy { .. }
            | Self::ReadAt { .. }
            | Self::AppendBatch { .. }
            | Self::StageOriginal { .. }
            | Self::AppendOriginal { .. }
            | Self::ProveOriginal { .. }
            | Self::KeeperStatus(_)
            | Self::PreferLeader { .. }
            | Self::StageRecovered { .. }
            | Self::AcknowledgeRecovery(_)
            | Self::Written { .. } => WireVersion::Previous,
            Self::LocalConfiguration(_)
            | Self::Staging(_)
            | Self::ClusterVersion
            | Self::FinalizeVersion(_)
            | Self::ClearQuarantine(_)
            | Self::RecoveryFence(_)
            | Self::AcknowledgeRecoveryWithMarker { .. }
            | Self::SealSession { .. }
            | Self::StageSessionOriginal { .. }
            | Self::OffloadStatus { .. }
            | Self::Restore { .. }
            | Self::RenewLease { .. }
            | Self::FenceKeeper(_)
            | Self::RecoverStream { .. }
            | Self::RecoverStreamFrom { .. }
            | Self::LocalProgressFencing { .. }
            | Self::LocalTip(_)
            | Self::NamedStreams(_)
            | Self::TrimCheckpoint { .. }
            | Self::InstallCheckpoint { .. }
            | Self::SelectedCheckpoint(_)
            | Self::CheckpointCustody { .. }
            | Self::AttestOriginal { .. }
            | Self::LocalProgress(_) => WireVersion::Current,
        }
    }
}

impl PeerRequest {
    /// The wire version that introduced this peer request.
    pub(in crate::stream::consensus) fn introduced(&self) -> WireVersion {
        match self {
            Self::Append(_)
            | Self::Vote(_)
            | Self::Snapshot(..)
            | Self::PreVote(_)
            | Self::TransferLeader(_)
            | Self::Park { .. } => WireVersion::Previous,
        }
    }
}

impl Frame {
    /// The wire version that introduced this frame and what it carries.
    pub(in crate::stream::consensus) fn introduced(&self) -> WireVersion {
        match self {
            Self::Client(request) => request.introduced(),
            Self::Peer(genesis, _) if genesis.immutable => WireVersion::Current,
            Self::Peer(_, request) => request.introduced(),
            Self::Liveness(_) => WireVersion::Previous,
            Self::Ping { .. } => WireVersion::Current,
        }
    }
}

impl Reply {
    /// The wire version that introduced this reply variant. An N-1 peer gets
    /// one only through `ReplyV1::from_reply`.
    pub(in crate::stream::consensus) fn introduced(&self) -> WireVersion {
        match self {
            // An immutable genesis has a layout N-1 cannot decode, whatever
            // reply carries it.
            Self::Catalog(genesis, _) | Self::ScopedPage { genesis, .. } if genesis.immutable => {
                WireVersion::Current
            }
            Self::Placement(proof) if proof.genesis.immutable => WireVersion::Current,
            Self::Decision(_)
            | Self::Leader(_)
            | Self::Catalog(..)
            | Self::Staged(_)
            | Self::Placement(_)
            | Self::Generation(_)
            | Self::ScopedPage { .. }
            | Self::Status(_) => WireVersion::Previous,
            Self::Configured(_)
            | Self::Unsupported(_)
            | Self::ClusterVersion(_)
            | Self::Lease(_)
            | Self::Recovered(_)
            | Self::Tip(_)
            | Self::Named(_)
            | Self::Progress { .. } => WireVersion::Current,
        }
    }
}

/// The wire version that introduced `outcome`. Newer outcomes are
/// translated to `Unavailable` by `outcome_v1`.
pub(in crate::stream::consensus) fn outcome_introduced(outcome: &Outcome) -> WireVersion {
    match outcome {
        // N-1 knows no entry kinds: a page with recovery entries is newer.
        Outcome::Page(page) if !page.recoveries.is_empty() => WireVersion::Current,
        Outcome::Unit
        | Outcome::Sealed(_)
        | Outcome::At(_)
        | Outcome::Page(_)
        | Outcome::Configuration(_)
        | Outcome::OriginalSample(_)
        | Outcome::OriginalEvidence(_) => WireVersion::Previous,
        Outcome::RecoveryFence(_)
        | Outcome::Offload(_)
        | Outcome::Checkpoint(_)
        | Outcome::CheckpointCustody(_)
        | Outcome::TimedCommitment(_)
        | Outcome::RecoveryPage(_) => WireVersion::Current,
        Outcome::Refused(error) => error_introduced(error),
    }
}

/// The wire version that introduced `error`. `outcome_v1` sends a newer one
/// to an N-1 peer as `Unavailable`.
pub(in crate::stream::consensus) fn error_introduced(error: &JournalError) -> WireVersion {
    match error {
        JournalError::Fenced { .. }
        | JournalError::Conflict { .. }
        | JournalError::Trimmed { .. }
        | JournalError::TooLarge { .. }
        | JournalError::Full { .. }
        | JournalError::NotFound
        | JournalError::Deleted
        | JournalError::Unavailable
        | JournalError::Recovered { .. } => WireVersion::Previous,
        JournalError::Unsupported | JournalError::Corrupted => WireVersion::Current,
    }
}

/// The variant names of a serde enum, in declaration order, which is the
/// order of its bincode variant tags.
pub(super) fn variants<T: DeserializeOwned>() -> &'static [&'static str] {
    struct Introspect<'a>(&'a mut Option<&'static [&'static str]>);

    impl<'de> Deserializer<'de> for Introspect<'_> {
        type Error = de::value::Error;

        fn deserialize_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value, Self::Error> {
            Err(de::Error::custom("not an enum"))
        }

        fn deserialize_enum<V: Visitor<'de>>(
            self,
            _: &'static str,
            variants: &'static [&'static str],
            _: V,
        ) -> Result<V::Value, Self::Error> {
            *self.0 = Some(variants);
            Err(de::Error::custom("introspected"))
        }

        serde::forward_to_deserialize_any! {
            bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes
            byte_buf option unit unit_struct newtype_struct seq tuple tuple_struct map
            struct identifier ignored_any
        }
    }

    let mut names = None;
    let _ = T::deserialize(Introspect(&mut names));
    names.expect("a serde enum")
}

/// Variant counts of the enums whose tags a receiver checks before decoding.
pub(super) struct Counts {
    pub frame: u32,
    pub request: u32,
    pub peer: u32,
}

pub(super) static COUNTS: LazyLock<Counts> = LazyLock::new(|| Counts {
    frame: variants::<Frame>().len() as u32,
    request: variants::<Request>().len() as u32,
    peer: variants::<PeerRequest>().len() as u32,
});

#[cfg(test)]
mod tests;
