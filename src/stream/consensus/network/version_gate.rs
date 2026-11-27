//! Compatibility decisions shared by the request and reply codecs.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Wire protocol version negotiated via TLS ALPN. Rolling upgrades support
/// adjacent versions `Previous` (N-1) and `Current` (N) only.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq, PartialOrd, Ord))]
pub(crate) enum WireVersion {
    Previous,
    Current,
}

impl WireVersion {
    /// Whether `connection` knows a value introduced in `self`.
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == (self is Previous || connection is Current),
    ))]
    pub(crate) fn supported_on(self, connection: Self) -> bool {
        matches!(self, Self::Previous) || matches!(connection, Self::Current)
    }
}

/// Projects a value carried inside a legacy reply. The caller supplies a
/// legacy representation (Unavailable for outcomes the old peer cannot read).
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if introduced is Previous { value } else { fallback },
))]
pub(super) fn legacy_payload<T>(introduced: WireVersion, value: T, fallback: T) -> T {
    if introduced.supported_on(WireVersion::Previous) {
        value
    } else {
        fallback
    }
}

/// Whether a value N-1 knows, carrying only rosters N-1 reads, may be sent
/// unchanged to an N-1 peer.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (introduced is Previous && legacy),
))]
pub(super) fn legacy_sends(introduced: WireVersion, legacy: bool) -> bool {
    introduced.supported_on(WireVersion::Previous) && legacy
}

/// How a frame travels on a connection.
pub(super) enum FrameSend {
    /// Unchanged.
    Encode,
    /// As the N-1 liveness frame: only a ping, which N-1 knows as liveness.
    Liveness,
    /// Not at all: the peer could not decode it.
    Refuse,
}

/// How a frame introduced in `introduced` travels on `connection`. `ping`
/// says it is a ping, and `legacy` that every roster it carries has three
/// voters, the only size an N-1 peer reads.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Encode) == (connection is Current || (!ping && introduced is Previous && legacy)),
        (out is Liveness) == (connection is Previous && ping),
))]
pub(super) fn frame_send(
    connection: WireVersion,
    introduced: WireVersion,
    ping: bool,
    legacy: bool,
) -> FrameSend {
    match connection {
        WireVersion::Current => FrameSend::Encode,
        WireVersion::Previous if ping => FrameSend::Liveness,
        WireVersion::Previous if legacy_sends(introduced, legacy) => FrameSend::Encode,
        WireVersion::Previous => FrameSend::Refuse,
    }
}
