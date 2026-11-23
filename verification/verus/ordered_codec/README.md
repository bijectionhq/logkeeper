# Ordered codec framing

This area imports the shipped [frame checks](../../../src/ordered/codec/frame.rs).
The command decoder and the decision-header reader use the same v8 version check.
The decision encoder writes the version followed by the eight big-endian journal-time bytes.
The decision decoder recovers those bytes and leaves command decoding to `Request::decode`.

| Lean definition in [Logkeeper.Codec](../../lean/Logkeeper/Codec.lean) | Verus obligation |
| --- | --- |
| `commandVersion` | `has_command_version` accepts exactly byte 8. |
| `decisionHeader`, `decisionHeaderMatches` | `decision_header` writes the specified nine bytes and `read_decision_time` succeeds exactly on that prefix of an arbitrary slice. |
| `flagByte`, `readFlag` | `encode_flag` and `decode_flag` round-trip the two Boolean values and reject every other spelling. |
| `bodyLengthBounded`, `boundedBodyLength` | `bounded_body_length` accepts the inclusive bounds and returns the original declared length. |
| `objectNameCountFits` in [Logkeeper.CompactImage](../../lean/Logkeeper/CompactImage.lean) | `object_name_count` validates both the count limit and the entire fixed-width name extent. |

The Lean byte lists correspond to Verus slice and array views.
The length bounds use mathematical naturals in Lean and the nonnegative integer views of Rust values in Verus.
The journal-time proof starts and ends at the eight time bytes. The Rust adapters perform the standard big-endian conversion.

The flag functions serve the command, compact-image and application codecs and the accepted-prefix flag in voter transport.
The length check bounds the declared application body in [LKAPPC12](../../../src/ordered/service/wire.rs), slot payload in [LKORV005](../../../src/ordered/replication/disk.rs) and prefix body in [LKORPC04](../../../src/ordered/replication/transport.rs).
The async reads and writes, the media checksum and ballot checks, command variants, object-name content and order, and application request and reply bodies are outside the Verus obligations.

The native codec tests exercise an enrollment command and its stamped decision, including every proper prefix, an added byte, and the non-Boolean option marker.
They also exhibit three different append payloads whose encodings extend one another.
A shorter or longer append payload is another canonical command and decision.
The outer frame or digest must establish the intended extent.
For voter transport, `RemoteVoter::accept` reads the vote fields and can return with further bytes left on the stream.
The native test also supplies selector 2, which the decoder returns and the caller's `SlotPair::is_mirrored` rejects.
The application length defines the body boundary and the declared media length excludes preallocated slot slack.

The [manifest](area.json) records seven source mutations and their expected diagnostics.
The pinned baseline verified 15 items and all seven mutations failed at their declared obligations.
