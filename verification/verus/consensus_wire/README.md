# Consensus wire version gate

`proof.rs` imports the shipped `src/stream/consensus/network/version_gate.rs`. `network/versions.rs` classifies each variant of `Frame`, `Request`, `PeerRequest`, `Reply`, `Outcome` and `JournalError` by the `WireVersion` that introduced it. `network.rs` sends with the functions verified here: `Frame::encode_for` asks `frame_send` how a frame travels on the connection, `ReplyV1::from_reply` asks `legacy_sends` whether a reply may reach an N-1 peer, `outcome_v1` replaces a nested N-only outcome with `legacy_payload`, and `decode_frame` refuses an N-only frame arriving on an N-1 connection with `WireVersion::supported_on`. The harness uses no custom axioms, assumptions or external bodies.

| Law | Property | Shipped functions |
| --- | --- | --- |
| `an_n_only_value_cannot_pass_the_n_minus_one_gate`, `every_classified_value_can_travel_on_the_current_connection` | An N-only value is unknown on N-1 and every value is known on N | `supported_on` |
| `an_n_only_frame_never_travels_on_n_minus_one` | No N-only frame is encoded on an N-1 connection; only a ping goes, as the N-1 liveness frame | `frame_send` |
| `a_five_voter_roster_never_travels_on_n_minus_one` | A frame or reply carrying a five-voter roster never reaches N-1 | `frame_send`, `legacy_sends` |
| `n_minus_one_receives_every_frame_it_reads` | A frame N-1 knows, with rosters it reads, goes unchanged, and every frame goes unchanged on N | `frame_send` |
| `an_n_only_reply_never_travels_on_n_minus_one` | A reply reaches N-1 only when N-1 knows it | `legacy_sends` |
| `a_new_nested_outcome_is_replaced_by_the_legacy_fallback`, `a_previous_nested_outcome_is_preserved` | An N-only outcome inside a reply becomes `Unavailable` for N-1, and an N-1 outcome is kept | `legacy_payload` |

## Scope

The classification functions match on the wire enums, which hold OpenRaft and serde types Verus does not import. They are exhaustive matches without a wildcard, so a new variant does not compile until it is classified. `every_wire_variant_is_classified_by_the_version_that_introduced_it` in `network/versions/tests.rs` checks that each variant past the pinned N-1 list is classified N, with a sample per variant, and `requests_reach_only_peers_that_know_them` and `the_n_minus_1_reply_codec_is_the_n_minus_1_reply_layout` check the send paths end to end. Which roster a frame or reply carries (`legacy_roster`) is unverified Rust covered by the same tests.

## Controls

`area.json` declares 6 production mutations: treat every value as known on N-1, pass an N-only nested outcome, send an N-only frame or a five-voter roster to N-1, forward a ping unchanged, and refuse frames N-1 reads. The baseline verifies 13 functions, and each control fails exactly its declared contracts.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_wire
```
