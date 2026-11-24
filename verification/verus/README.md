# Logkeeper production proofs

Use Verus `0.2026.11.20.9da409b`, Rust `1.100.0` and Z3 `4.16.0`.
On the co-design machine, the shared launcher selects the pinned Rust
toolchain and Z3. Run from the Logkeeper checkout root.

```sh
tools=/Users/sachaichbiah/code/codesign-agents/tools
python3 verification/verus/run.py --verus "$tools/verus" ordered_admission
```

Omit the area name to run every area, or pass several area names to run them
in sequence. With a standalone Verus installation, pass its executable
with `--verus` and set `VERUS_Z3_PATH` to the pinned Z3 executable.
The runner saves each command, stdout and stderr, the area manifest and
SHA-256 hashes of the baseline inputs under `verification/verus/.results/`.
Use `--evidence PATH` to choose a fresh output directory.

## Area layout

- `proof.rs` includes shipped Rust as the `production` module through relative
  `#[path = "..."]` attributes. Use those attributes for dependencies outside
  the area so the runner can copy them into each case.
- `laws.rs` checks the production code against named reference definitions.
  Record the Lean names, the mapping of inputs and outputs, and the scope
  of the proof in the area's README.
- `area.json` supplies Verus `flags`, the baseline `min_verified_functions`
  and named `controls`. Use `--no-external-by-default` and select
  `--verify-module production` and `--verify-module laws`. Keep the functions
  under proof and their laws free of unchecked bodies, assumptions and proof stubs.

Each control declares a defect, an ordered list of `mutate` edits, expected
diagnostics in `expect`, and its own `min_verified_functions`. An edit has
a repository-relative `file`, a unique `find` string and a `replace` string.
Each control edits at least one shipped file under `src/`. An expected
diagnostic names the repository-relative `file`, the Rust `function` and Verus
diagnostic `category`, such as `postcondition not satisfied`.
The runner makes a fresh copy for the baseline and for each control. Success
requires the baseline to verify and each control to produce exactly its
declared proof failures while meeting its verification count.

Run the [mechanical Lean correspondence checker](../link/README.md) alongside
the Verus runner. It regenerates Lean predicates from the live Rust spec
functions, checks the named equivalences, and runs controls on both sides.

```sh
python3 verification/link/run.py
```

The area READMEs describe the checked production functions and Lean mappings.

- [Compact image](compact_image/README.md)
- [Mirrored voter media](mirrored_voter_media/README.md)
- [Object-name codec](object_name_codec/README.md)
- [Object withdrawal](object_withdrawal/README.md)
- [Ordered admission](ordered_admission/README.md)
- [Ordered budgets](ordered_budgets/README.md)
- [Ordered checkpoint custody](ordered_checkpoint/README.md)
- [Ordered codec](ordered_codec/README.md)
- [Ordered cohort confirmation and repair](ordered_cohort/README.md)
- [Ordered lease reducer](ordered_lease_reducer/README.md)
- [Ordered receipt retention and retry](ordered_receipt/README.md)
- [Ordered reducer projections](ordered_reducer/README.md)
- [Ordered replay interval and cursor](ordered_replay/area.json)
- [Ordered rotation](ordered_rotation/README.md)
- [Ordered serving lease](ordered_serving_lease/README.md)
- [Ordered trim](ordered_trim/README.md)
- [Ordered writer](ordered_writer/README.md)
- [Prefix agreement](prefix_agreement/README.md)
- [Receipt signatures and repair keys](receipt_signatures/README.md)
- [Rotation slot evidence](rotation_slot_evidence/README.md)
- [Voter slot header](voter_slot_header/README.md)
- [Voter transport](voter_transport/README.md)
