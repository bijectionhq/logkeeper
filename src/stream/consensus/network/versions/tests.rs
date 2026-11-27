//! A wire variant added without classifying it, out of order, or reaching an
//! N-1 peer fails here. When the ALPNs move, the N-1 lists below become the
//! variants of the release that is now N-1.

use bytes::Bytes;
use journal_contract::{
    Epoch, JournalError, Lsn, Page, RecoveryFence, StreamId, WriterFence, WriterSessionId,
};
use openraft::raft::{AppendEntriesRequest, TransferLeaderRequest, VoteRequest};
use serde::Serialize;

use super::super::{
    DecodedFrame, Frame, PeerRequest, Proof, Reply, ReplyV1, Request, SnapshotChunk, WireVersion,
    decode_frame, encode_reply,
};
use super::{error_introduced, outcome_introduced, variants};
use crate::stream::consensus::{
    Configuration, Fence, Genesis, KeeperStatus, Sealed, SnapshotMeta, Stage, Vote, encode,
    state::Outcome,
};

/// The variants of `logkeeper-consensus/1` and its sibling lanes, which N-1
/// (Logkeeper 44d3f2a) decodes.
const REQUESTS_N1: &[&str] = &[
    "Claim",
    "Locate",
    "Stage",
    "Bootstrap",
    "Create",
    "Seal",
    "Append",
    "Read",
    "Head",
    "Trim",
    "Delete",
    "Configuration",
    "Replace",
    "PlacementProof",
    "StageReplica",
    "InstallReplica",
    "LocalCopy",
    "RetireCopy",
    "ReadAt",
    "AppendBatch",
    "StageOriginal",
    "AppendOriginal",
    "ProveOriginal",
    "KeeperStatus",
    "PreferLeader",
    "StageRecovered",
    "AcknowledgeRecovery",
    "Written",
];
const FRAMES_N1: &[&str] = &["Client", "Peer", "Liveness"];
const PEER_REQUESTS_N1: &[&str] = &[
    "Append",
    "Vote",
    "Snapshot",
    "PreVote",
    "TransferLeader",
    "Park",
];
const REPLIES_N1: &[&str] = &[
    "Decision",
    "Leader",
    "Catalog",
    "Staged",
    "Placement",
    "Generation",
    "ScopedPage",
    "Status",
];
const OUTCOMES_N1: &[&str] = &[
    "Unit",
    "Sealed",
    "At",
    "Page",
    "Refused",
    "Configuration",
    "OriginalSample",
    "OriginalEvidence",
];
const ERRORS_N1: &[&str] = &[
    "Fenced",
    "Conflict",
    "Trimmed",
    "TooLarge",
    "Full",
    "NotFound",
    "Deleted",
    "Unavailable",
    "Recovered",
];

const STREAM: StreamId = StreamId(9);

fn genesis() -> Genesis {
    Genesis {
        stream: STREAM,
        voters: [1, 2, 3].map(uuid::Uuid::from_u128),
        quota_bytes: 4096,
        immutable: false,
    }
}

fn stage() -> Stage {
    Stage {
        stream: STREAM,
        source: 1,
        old: [1, 2, 3].map(uuid::Uuid::from_u128),
        target: [1, 2, 4].map(uuid::Uuid::from_u128),
    }
}

fn fence() -> Fence {
    Fence {
        epoch: Epoch(1),
        writer: uuid::Uuid::from_u128(7),
    }
}

fn configuration() -> Configuration {
    Configuration {
        revision: 1,
        voters: [1, 2, 3].map(uuid::Uuid::from_u128),
    }
}

fn vote() -> Vote {
    Vote::new(1, 1)
}

fn status() -> KeeperStatus {
    KeeperStatus {
        keeper: uuid::Uuid::from_u128(1),
        accepting: true,
        streams: 0,
        led: 0,
        replica: None,
        build_version: String::new(),
        features: 0,
        cluster_version: 1,
    }
}

/// One request of each variant, by tag. A new variant needs a sample here.
fn request(tag: usize) -> Option<Request> {
    let bytes = Bytes::from_static(b"x");
    Some(match tag {
        0 => Request::Claim(genesis()),
        1 => Request::Locate(STREAM),
        2 => Request::Stage(stage()),
        3 => Request::Bootstrap(STREAM),
        4 => Request::Create(STREAM),
        5 => Request::Seal {
            stream: STREAM,
            expected: Epoch(0),
            writer: uuid::Uuid::from_u128(7),
        },
        6 => Request::Append {
            stream: STREAM,
            fence: fence(),
            at: Lsn(1),
            payload: bytes,
        },
        7 => Request::Read {
            stream: STREAM,
            from: Lsn(1),
            limit: 1,
            wait_ms: 0,
        },
        8 => Request::Head(STREAM),
        9 => Request::Trim {
            stream: STREAM,
            fence: fence(),
            through: Lsn(1),
        },
        10 => Request::Delete(STREAM),
        11 => Request::Configuration(STREAM),
        12 => Request::Replace {
            stream: STREAM,
            expected: 1,
            voters: [1, 2, 4].map(uuid::Uuid::from_u128),
        },
        13 => Request::PlacementProof(STREAM),
        14 => Request::StageReplica {
            genesis: genesis(),
            stage: stage(),
        },
        15 => Request::InstallReplica {
            genesis: genesis(),
            stage: stage(),
            generation: 1,
            through: crate::stream::consensus::LogId::new(
                openraft::vote::leader_id_std::CommittedLeaderId::new(1),
                1,
            ),
        },
        16 => Request::LocalCopy(STREAM),
        17 => Request::RetireCopy {
            stream: STREAM,
            authority: uuid::Uuid::from_u128(1),
            revision: 1,
            generation: 1,
        },
        18 => Request::ReadAt {
            genesis: genesis(),
            from: Lsn(1),
            minimum_head: Lsn(0),
            limit: 1,
            wait_ms: 0,
        },
        19 => Request::AppendBatch {
            stream: STREAM,
            fence: fence(),
            at: Lsn(1),
            payloads: vec![bytes],
        },
        20 => Request::StageOriginal {
            stream: STREAM,
            revision: 1,
            original: Vec::new(),
            payload: bytes,
        },
        21 => Request::AppendOriginal {
            stream: STREAM,
            fence: fence(),
            evidence: Vec::new(),
            payload: bytes,
        },
        22 => Request::ProveOriginal {
            stream: STREAM,
            at: Lsn(1),
        },
        23 => Request::KeeperStatus(STREAM),
        24 => Request::PreferLeader {
            stream: STREAM,
            keeper: uuid::Uuid::from_u128(1),
        },
        25 => Request::StageRecovered {
            genesis: genesis(),
            stage: stage(),
        },
        26 => Request::AcknowledgeRecovery(STREAM),
        27 => Request::Written {
            stream: STREAM,
            fence: fence(),
            at: Lsn(1),
            payloads: vec![bytes],
        },
        28 => Request::LocalConfiguration(STREAM),
        29 => Request::Staging(STREAM),
        30 => Request::ClusterVersion,
        31 => Request::FinalizeVersion(2),
        32 => Request::ClearQuarantine(STREAM),
        33 => Request::RecoveryFence(STREAM),
        34 => Request::AcknowledgeRecoveryWithMarker {
            stream: STREAM,
            fence: RecoveryFence {
                epoch: Epoch(1),
                head: Lsn(1),
            },
            payload: bytes,
        },
        35 => Request::SealSession {
            stream: STREAM,
            expected_writer_epoch: Epoch(1),
            writer_session_id: WriterSessionId(7),
        },
        36 => Request::StageSessionOriginal {
            fence: WriterFence {
                stream: STREAM,
                writer_epoch: Epoch(1),
                writer_session_id: WriterSessionId(7),
            },
            revision: 1,
            original: Vec::new(),
            payload: bytes,
        },
        37 => Request::OffloadStatus {
            stream: STREAM,
            flush: true,
        },
        38 => Request::Restore {
            stream: STREAM,
            restore: crate::stream::consensus::state::Restore {
                lineage: 1,
                floor: Lsn(1),
                head: Lsn(0),
                epoch: Epoch(0),
                replace: true,
            },
        },
        39 => Request::RenewLease {
            keeper: uuid::Uuid::from_u128(1),
            incarnation: uuid::Uuid::from_u128(9),
            epoch: 1,
        },
        40 => Request::FenceKeeper(uuid::Uuid::from_u128(1)),
        41 => Request::RecoverStream {
            stage: stage(),
            dead: Vec::new(),
        },
        _ => return None,
    })
}

fn peer_request(tag: usize) -> Option<PeerRequest> {
    Some(match tag {
        0 => PeerRequest::Append(AppendEntriesRequest {
            vote: vote(),
            prev_log_id: None,
            entries: Vec::new(),
            leader_commit: None,
        }),
        1 => PeerRequest::Vote(VoteRequest::new(vote(), None)),
        2 => PeerRequest::Snapshot(
            SnapshotChunk {
                vote: vote(),
                meta: SnapshotMeta {
                    last_log_id: None,
                    last_membership: Default::default(),
                    snapshot_id: String::new(),
                },
                offset: 0,
                data: Vec::new(),
                done: true,
            },
            [0; 32],
        ),
        3 => PeerRequest::PreVote(VoteRequest::new(vote(), None)),
        4 => PeerRequest::TransferLeader(TransferLeaderRequest::new(vote(), 2, None)),
        5 => PeerRequest::Park {
            vote: vote(),
            last: None,
        },
        _ => return None,
    })
}

fn frame(tag: usize) -> Option<Frame> {
    Some(match tag {
        0 => Frame::Client(request(1)?),
        1 => Frame::Peer(genesis(), peer_request(5)?),
        2 => Frame::Liveness(uuid::Uuid::from_u128(1)),
        3 => Frame::Ping {
            incarnation: uuid::Uuid::from_u128(1),
            version: String::new(),
            features: 0,
        },
        _ => return None,
    })
}

fn reply(tag: usize) -> Option<Reply> {
    Some(match tag {
        0 => Reply::Decision(Outcome::Unit),
        1 => Reply::Leader(None),
        2 => Reply::Catalog(genesis(), Vec::new()),
        3 => Reply::Staged(stage()),
        4 => Reply::Placement(Proof {
            genesis: genesis(),
            configuration: configuration(),
            joint: None,
            stage: None,
        }),
        5 => Reply::Generation(1),
        6 => Reply::ScopedPage {
            genesis: genesis(),
            configuration: None,
            outcome: Outcome::Unit,
        },
        7 => Reply::Status(status()),
        8 => Reply::Configured(None),
        9 => Reply::Unsupported(String::new()),
        10 => Reply::ClusterVersion(1),
        11 => Reply::Lease(crate::stream::consensus::Grant {
            granted: true,
            enforced: true,
            epoch: 1,
            fenced: Default::default(),
            reused: false,
            duration_ms: 30_000,
            margin_ms: 3_000,
        }),
        12 => Reply::Recovered(crate::stream::consensus::Recovered {
            fenced: Vec::new(),
            unleased: Vec::new(),
            wait_ms: 33_000,
            written: true,
        }),
        _ => return None,
    })
}

fn error(tag: usize) -> Option<JournalError> {
    Some(match tag {
        0 => JournalError::Fenced { current: Epoch(1) },
        1 => JournalError::Conflict { head: Lsn(1) },
        2 => JournalError::Trimmed { floor: Lsn(1) },
        3 => JournalError::TooLarge { max: 1 },
        4 => JournalError::Full { floor: Lsn(1) },
        5 => JournalError::NotFound,
        6 => JournalError::Deleted,
        7 => JournalError::Unavailable,
        8 => JournalError::Recovered { head: Lsn(1) },
        9 => JournalError::Unsupported,
        10 => JournalError::Corrupted,
        _ => return None,
    })
}

fn outcome(tag: usize) -> Option<Outcome> {
    Some(match tag {
        0 => Outcome::Unit,
        1 => Outcome::Sealed(Sealed {
            fence: fence(),
            head: Lsn(0),
        }),
        2 => Outcome::At(Lsn(1)),
        3 => Outcome::Page(Page {
            floor: Lsn(1),
            records: Vec::new(),
            head: Lsn(0),
        }),
        4 => Outcome::Refused(JournalError::NotFound),
        5 => Outcome::Configuration(configuration()),
        6 => Outcome::OriginalSample(Vec::new()),
        7 => Outcome::OriginalEvidence(Vec::new()),
        8 => Outcome::RecoveryFence(None),
        9 => Outcome::Offload(crate::stream::consensus::OffloadStatus {
            stream: STREAM,
            offloaded_through: Lsn(0),
            lineage: 0,
            lineages: vec![(0, Lsn(1))],
            floor: Lsn(1),
            local_floor: Lsn(1),
            head: Lsn(0),
            epoch: Epoch(0),
        }),
        _ => return None,
    })
}

/// Checks one wire enum: its variants only ever grow after the N-1 list,
/// every variant has a sample whose bincode tag is its position, and a
/// variant is classified N-1 exactly when N-1 knew it.
fn check<T: Serialize + serde::de::DeserializeOwned>(
    name: &str,
    previous: &[&str],
    sample: impl Fn(usize) -> Option<T>,
    introduced: impl Fn(&T) -> WireVersion,
) {
    let names = variants::<T>();
    assert!(
        names.starts_with(previous),
        "{name} variants {names:?} must start with the N-1 variants {previous:?}: \
         variants are only appended, and a reordered or renamed one breaks N-1"
    );
    for (tag, variant) in names.iter().enumerate() {
        let sample = sample(tag).unwrap_or_else(|| {
            panic!("{name}::{variant} (tag {tag}) needs a sample in network/versions/tests.rs")
        });
        let bytes = encode(&sample).unwrap();
        assert_eq!(
            u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize,
            tag,
            "the {name} sample for tag {tag} is not {variant}"
        );
        let expected = if tag < previous.len() {
            WireVersion::Previous
        } else {
            WireVersion::Current
        };
        assert_eq!(
            introduced(&sample),
            expected,
            "{name}::{variant} is classified as introduced in the wrong version"
        );
    }
}

#[test]
fn every_wire_variant_is_classified_by_the_version_that_introduced_it() {
    check("Request", REQUESTS_N1, request, Request::introduced);
    check(
        "PeerRequest",
        PEER_REQUESTS_N1,
        peer_request,
        PeerRequest::introduced,
    );
    check("Reply", REPLIES_N1, reply, Reply::introduced);
    check("JournalError", ERRORS_N1, error, error_introduced);
    check("Outcome", OUTCOMES_N1, outcome, |outcome| match outcome {
        // The refusal's version is its error's, checked above.
        Outcome::Refused(_) => WireVersion::Previous,
        other => outcome_introduced(other),
    });
    // A frame's version is the newest of the frame and what it carries.
    check("Frame", FRAMES_N1, frame, |frame| match frame {
        Frame::Client(_) | Frame::Peer(..) => WireVersion::Previous,
        other => other.introduced(),
    });
}

#[test]
fn the_n_minus_1_reply_codec_is_the_n_minus_1_reply_layout() {
    assert_eq!(variants::<ReplyV1>(), REPLIES_N1);
    for tag in 0..variants::<Reply>().len() {
        let reply = reply(tag).unwrap();
        let introduced = reply.introduced();
        match encode_reply(reply, WireVersion::Previous) {
            Ok(bytes) => {
                assert_eq!(introduced, WireVersion::Previous);
                assert_eq!(
                    u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize,
                    tag
                );
            }
            Err(_) => assert_eq!(introduced, WireVersion::Current),
        }
    }
    for tag in 0..variants::<JournalError>().len() {
        let error = error(tag).unwrap();
        let sent = encode_reply(
            Reply::Decision(Outcome::Refused(error.clone())),
            WireVersion::Previous,
        )
        .unwrap();
        let expected = if error_introduced(&error) == WireVersion::Previous {
            error
        } else {
            JournalError::Unavailable
        };
        assert_eq!(
            sent,
            encode(&ReplyV1::Decision(Outcome::Refused(expected))).unwrap()
        );
    }
}

#[test]
fn requests_reach_only_peers_that_know_them() {
    for tag in 0..variants::<Request>().len() {
        let request = request(tag).unwrap();
        let known = tag < REQUESTS_N1.len();
        assert_eq!(request.supported_on(WireVersion::Previous), known);
        assert!(request.supported_on(WireVersion::Current));
        let frame = Frame::Client(request);
        let current = frame.encode_for(WireVersion::Current).unwrap();
        assert!(matches!(
            decode_frame(&current, WireVersion::Current),
            Ok(DecodedFrame::Frame(_))
        ));
        assert_eq!(frame.encode_for(WireVersion::Previous).is_ok(), known);
        // An N-only request arriving on an N-1 connection is refused.
        assert_eq!(decode_frame(&current, WireVersion::Previous).is_ok(), known);
    }
}

#[test]
fn unknown_variant_tags_are_unsupported_from_the_enums_own_bounds() {
    let mut bytes = encode(&Frame::Client(Request::Head(STREAM))).unwrap();
    let past = variants::<Request>().len() as u32;
    bytes[4..8].copy_from_slice(&past.to_le_bytes());
    assert!(matches!(
        decode_frame(&bytes, WireVersion::Current),
        Ok(DecodedFrame::Unsupported(_))
    ));
    assert!(decode_frame(&bytes, WireVersion::Previous).is_err());
    let mut bytes = encode(&Frame::Liveness(uuid::Uuid::nil())).unwrap();
    let past = variants::<Frame>().len() as u32;
    bytes[..4].copy_from_slice(&past.to_le_bytes());
    assert!(matches!(
        decode_frame(&bytes, WireVersion::Current),
        Ok(DecodedFrame::Unsupported(_))
    ));
}
