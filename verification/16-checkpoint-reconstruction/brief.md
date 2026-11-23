# Study 16 · Checkpoint reconstruction

## Question

Which evidence lets an RTDB worker trim the journal and reconstruct exactly the committed cut it captured, including when a child deployment shares a parent's immutable objects?

## Sources

Use [S06, P06 and M05](../requirements.md), the [logical kernel](../07-reference/Kernel.lean), and the [replay custody study](../15-replay-permits/report.md).
The RTDB contracts are `TrimCertifiedReplicaPrefix`, checkpoint receipt closure and fork initialization in `allium/rtdb-multi.allium`, plus `dev/lean/CheckpointReplay.lean`.

## Model and properties

TLC models publication, checkpoint selection, logical trim, and the bounds of a captured read.
The state image aggregates two possible records, allowing different ordered prefixes to yield identical state.
Fork genesis gives the child inherited data and its own initially empty history.
The invariants require exact subject and ordered prefix, a compatible root with closed dependencies, and an exact response insulated from subsequent appends.
Lean states recovery generically over a deterministic database reducer and checks that certified publication refines the logical kernel.
Authentication, provider custody, scheduling and the actual Arrow decoder are premises or outside this study.

## Comparison

Check the same laws with numeric-cut-only or state-only admission, incomplete closure, different formats, dynamic head selection, and incomplete tail replay.
Exercise fork bootstrap and recovery following trim while later commits proceed.
The runner checks the deliberately weakened Lean rules and TLC controls before accepting each tool's positive result.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and the pinned Lean 4.35.0 toolchain.
Run `python3 verification/16-checkpoint-reconstruction/run.py` with `JAVA_BIN` and `LEAN_BIN` set as in the [verification index](../README.md).
The runner keeps the tool and logs in study-local ignored directories.
See the [report](report.md) for results and scope.
