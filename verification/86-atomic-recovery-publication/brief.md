# Study 86 · Serialize local recovery publication and protect use separately

2026-11-23

## Question

Can a delayed recovery image overwrite a newer local serving image or authorize a new effect after authority moves, and can admitted work still complete through quorum loss?

## Sources

Use [S04, S10, S11, S70–S72, L02, and L05](../requirements.md), [ranked named recovery](../85-ranked-named-recovery/report.md), and [regional retirement and exact custody](../61-regional-retirement/report.md).

## Model and comparisons

Separate authority installation, local attachment, matching ordered use, and completion under exact protection.
Compare one atomic local attachment decision with a cached precheck, a missing stamp field, an overwrite of a filled slot, and use based on the attached image alone.
Compare completion under the original physical borrow with completion after effective stop and completion that requires a still-live quorum.
Use a bounded single-image model for the races and the combined journal and protected read reducer for general trace proofs.
Abstract device and transport effects at their stated authority and custody boundaries.

## Properties and programs

- The initial attachment compares the bound lineage, revision, ordered frontier, and serving session at the publication effect.
- Recovery fills an empty slot. Chosen incremental replay advances live state without replacing it through bootstrap.
- A fresh use needs authority and protected inputs independent of the local cache.
- An admitted exact operation can finish through quorum loss under its own still-held borrow. An effective stop prevents completion.
- A receipt sender can recover a live original invocation even if the caller lost the permit along with its first response.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
Run negative controls before trusting baselines.
Keep proof, mutation, and compile-fail output in .results/.
