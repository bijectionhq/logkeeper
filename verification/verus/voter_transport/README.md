# LKORPC04 voter transport fields

The area imports the [shipped field parsers](../../../src/ordered/replication/transport_fields.rs) used by the [async voter exchange](../../../src/ordered/replication/transport.rs).
It also verifies the byte operations imported from the [slot header codec](../voter_slot_header/README.md).

| Lean definition in [Logkeeper.VoterTransport](../../lean/Logkeeper/VoterTransport.lean) | Shipped check or Verus law |
| --- | --- |
| `transportMagic`, `transportGroupMatches` | The eight protocol bytes are fixed. The request group must equal both the channel's authorized group and the voter's installed group. |
| `responseKind` | The expected tag, depose tag, reject tag and unexpected tag have their distinct dispositions. The echoed voter byte array must match the expected voter. |
| `ballotBytes`, `ballotValid` | The 24-byte ballot carries a big-endian nonzero round and a non-nil nonce. `transport_ballot_round_trips` applies to every such field pair. |
| `voteSlotsMatch` | The response preserves the selector byte and the exact two generation/digest pairs in physical order. The coordinator separately checks the selector and mirrored pair before using the evidence. |
| `voteReadBackMatches` | The witness-mode tag must encode the requested Boolean exactly. |

The adapter reads fields in protocol order and handles one request or reply. An envelope may be followed by bytes on the underlying stream, as witnessed by the native vote fixture. The bounds on the transported prefix length and the promise flag are covered by [ordered codec framing](../ordered_codec/README.md). Async I/O, echoed ballot comparison, the depose ordering test, server dispatch, and nested `Prefix::decode` and replay remain to be composed end to end.

The [manifest](area.json) checks each declared mutation against the associated law.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
