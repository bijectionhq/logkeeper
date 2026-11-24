# Stream keeper verification

`proof.rs` imports the shipped `rules.rs`. The harness verifies the primitive decisions used for Create, Seal, Sync, Append, Trim, Check, Read, Delete and Replace. It verifies equal-epoch proposal matching, one compressed epoch run's bounds, and the per-record quota charge. The Replace and ensemble proofs cover the projected inputs, validity of three unsigned 128-bit keeper IDs, and the installed ensemble and learner flag returned to `state::apply`. The link runner checks the corresponding Lean definitions. `laws.rs` states the independent primitive checks. Controls either break a shipped postcondition or change a decision and its postcondition to break an independent law. The harness uses no custom axioms.

The retained range and staging helpers specify their exact indices and boundary
conditions. The shipped quota loop checks every supplied record length and
clamps the sum to the maximum `u64`. Its verified caller premise supplies the
length at each index. The link compares the loop's sum specification to the
Lean sum of per-record charges. Each new helper and the quota loop has a
production mutation checked at its own contract or loop invariant.

The Rust tests exercise request dispatch, byte comparisons, WAL encoding and replay, rotation, learner installation and the TCP/TLS boundary. They cover reachable success and refusal states, including two simultaneous streams, one durable stream checkpoint with another pending, and a learner facing one or two surviving members and a split ensemble installation. The Verus area contains no state-space model.

Run the proof from the repository root with `python3 verification/verus/run.py stream_keeper --verus /Users/sachaichbiah/code/codesign-agents/tools/verus`. Run the independent I/O mutations with `python3 verification/verus/stream_keeper/runtime-controls.py` after committing the keeper sources. The runtime runner copies the sources into an ignored evidence directory and mutates the copy.
