# Rotation slot evidence (L13)

Verus imports the shipped [voter collection checks](../../../src/ordered/replication/evidence.rs),
[rotation assembly](../../../src/ordered/replication/rotation.rs) and
[rotation encoder](../../../src/ordered/codec/service/rotation.rs).
They run on the ordered choose and receipt paths. The
[prefix agreement area](../prefix_agreement/README.md) checks the same
`record_vote` used by `Group::confirm`. This area uses the
[media readback laws](../mirrored_voter_media/README.md) for the local disk
side of the proof.

| Lean `Logkeeper.SelectionFence` | Rust and Verus correspondence |
| --- | --- |
| `StrictMajority` and `RotationEvidence` | `register_peer` admits only new configured identities. `record_vote` takes an exact reply from the expected peer and copies its slot pair. `RotationSlots::covers` requires exactly `cohort_size / 2 + 1` rows in strict UUID order. The laws derive pairwise distinctness and a strict majority of the configured roster. |
| `AtFence` | The ballot is the full round and nonce pair, and the prefix is the group-scoped digest of the exact re-accepted head. `record_vote` compares both fields and requires the requested readback flag. For a rotation that flag is true. |
| `MirrorsFence` | An authenticated `Vote` with readback attests the two validated visits. The row keeps its selected physical index and both authenticated slot descriptors. The selected generation is one greater than the other. Rust also checks that both digests are nonzero and distinct. |
| `rotation_evidence_names_a_majority_with_both_exact_reads` | The collection law preserves exact configured rows on each recorded reply. The assembly law binds those unchanged rows and the chosen group, ballot, prefix and position to the requested invocation, exact checkpoint, and immediate successor key generation. The suffix at and beyond the checkpoint is entirely from the successor generation. |

The fresh path certifies the prefix chosen for the rotation. The retained
path certifies the prefix re-accepted at the new ballot. That prefix can
cover a later position, while keeping the exact checkpoint and successor
generation of the rotation receipt. The receipt guard checks the invocation,
exact held recovery cut and successor generation.
The recovery hold must carry the original rotation request ID and the successor grant’s enrollment, even when the cut and generation match.

The checked encoder preserves the fields of `RotationSlots` and writes
every row in order. Each row consists of the UUID, selected index, A's
generation and digest, then B's generation and digest. The shipped
`RotationSlots::signing_bytes` prefixes the encoder output with the
rotation domain and the receipt, and the reply encoder uses the same
rotation encoder. The existing checkpoint serializer and byte-buffer
operations supply the documented codec contracts.

The proof uses authenticated, stable `Replica` identities. The inspected
asynchronous shell checks the configured peers before preparing, builds the
private `PreparedRound` from matching responses, and calls accept only on
those prepared endpoints. Sorting changes only the order of the collected
rows. A successful remote readback is the authenticated peer's attestation
that it ran the disk readback check. The SHA-256 and signature contracts,
transport authentication, the asynchronous shell and semantic prefix
replay are premises or inspected wiring. The signed payload is checked on
the issuer side. The decoder's canonicality and the RTDB erasure gate are
separate L3 and R5 obligations.

The Lean witness uses a configured roster of three and two exact attestations.
The majority and exact-read theorem is general in the roster and evidence
list lengths.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
