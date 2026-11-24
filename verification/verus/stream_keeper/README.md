# Stream keeper verification

`proof.rs` imports the shipped `rules.rs`. The harness verifies the primitive decisions used for Create, Seal, Sync, Append, Trim, Check, Read, Delete and Replace over the full Boolean and unsigned 64-bit domains. `laws.rs` states the independent checks. Each Verus control changes a decision and its matching postcondition, so it must fail at the corresponding law. The harness uses no custom axioms.

The Rust tests exercise request dispatch, byte comparisons, WAL encoding and replay, rotation, learner installation and the TCP/TLS boundary. They cover reachable success and refusal states, including two simultaneous streams, one durable stream checkpoint with another pending, and a learner facing one or two surviving members and a split ensemble installation. The Verus area contains no state-space model.

Run the proof from the repository root with `python3 verification/verus/run.py stream_keeper --verus /Users/sachaichbiah/code/codesign-agents/tools/verus`. Run the independent I/O mutations with `python3 verification/verus/stream_keeper/runtime-controls.py` after committing the keeper sources. The runtime runner temporarily mutates and restores source in the current worktree. Run it while no other build is using that worktree.
