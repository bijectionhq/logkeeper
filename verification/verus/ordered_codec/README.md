# Ordered codec framing

This area imports the shipped [frame checks](../../../src/ordered/codec/frame.rs).
The command decoder and the decision-header reader use the same v9 version check.
The decision encoder writes the version followed by the eight big-endian journal-time bytes.
The decision decoder recovers those bytes and leaves command decoding to `Request::decode`.

| Lean definition in [Logkeeper.Codec](../../lean/Logkeeper/Codec.lean) | Verus obligation |
| --- | --- |
| `commandVersion` | `has_command_version` accepts exactly byte 9. |
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

## Encoder preconditions

[CodecDomains](../../lean/Logkeeper/CodecDomains.lean) and [Verus domains](domains.rs)
name the restrictions on typed values passed to the version 9 command and decision
body codecs and the application body codecs. The restrictions apply to the nested
typed values as well. The transport still supplies the enclosing extent and its
configured frame limit.

| Encoder | Predicate and caller precondition |
| --- | --- |
| `Request::encode` | `commandAdmissible`. An optional reference list on `Append` or `PrepareCheckpoint` has at most 16,384 nonzero names in strict byte order. A `WithdrawObject` has both a nonzero name and a nonzero version. The remaining typed command fields have fixed, total encodings. |
| `encode_decision` | `decisionBodyAdmissible`. The request is codec-admissible and the journal time is represented by eight big-endian bytes. |
| `Operation::encode` | `serviceOperationAdmissible`. An `Execute` request or `Reconcile` original is command-admissible. Scope binding and operation authorization are service checks. |
| `Reply::encode` | `serviceReplyAdmissible`. Withdrawn-worker pages have at most 64 rows. Replay records have codec-admissible reference lists and byte lengths below the reference marker bit. A withdrawal outcome contains a nonzero name and version. A barrier decision carries an exact canonical claim and matching receipt. A rotation decision carries covering slot evidence and no barrier. A plain decision has no barrier outcome. |
| `State::encode_base` | `compactImageAdmissible` is documented in the [compact-image area](../compact_image/README.md). |

For barrier decisions, exact matching includes placement, worker origin, request
ID, admission position and the full hold. A canonical claim starts at the
checkpoint cut, ends at or after it, retains the same history when the cuts have
equal coordinates, and has a positive admission position below expiry. Rotation
coverage means the shipped `RotationSlots::covers` check. Signature authentication
is a separate service responsibility.

## Checked composition

`decisionRequestBytes` is `frame.take(1) ++ frame.drop(9)` in both provers.
Verus proves that the shipped `decision_request_parts` returns the exact time and
the two request slices, for any serialized v9 request and arbitrary command extent.
The Lean decision-body theorem composes that reconstruction with a supplied command
left inverse. Verus also checks the shipped withdrawal identity gate and proves that
the admitted worker-page count survives the encoder's byte cast and the decoder's
bound. The shared object-name gate is checked in the [object-name area](../object_name_codec/README.md)
and serves the command, embedded operation and record domains.
The shared `read_fixed_field` function returns the exact fixed-width prefix and
rejects short input. It implements `readFixedField` for command, compact-image
and application field reads.

The full typed left inverses still require refinement of `Bytes` reads and writes,
fixed field and tag composition, and the service decision evidence and replay record
adapters.
