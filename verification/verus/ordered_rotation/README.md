# Ordered erasure rotation (L9)

The inventory's rotation ships as `Command::PublishAndRotate`. Its reducer arm
calls the shipped guards in `src/ordered/rotation.rs` and PL1's writer
operations in `src/ordered/writer.rs`. The authenticated issuer is the
custodian. The request and erasure preparation bind the exact incumbent grant.

| Shipped operation | Law | Lean reference |
| --- | --- | --- |
| `check_rotation`, `same_cut` | `rotation_requires_exact_incumbent_and_head` | `ErasureCommit.rotation_head` |
| `check_preparation` | `rotation_requires_exact_preparation` | `ErasureCommit.exact_preparation` |
| `successor_generation` | `rotation_installs_successor_generation` | `ErasureCommit.successor_generation` |
| `successor_generation`, `writer::next_epoch`, `Authority::install`, `writer::authorize` | `rotated_suffix_refuses_superseded_grant` | `ErasureCommit.rotate`, `abstract_grant`, `rotated_suffix_refuses_superseded_grant` and `Logkeeper.Kernel.Ordered.authorize_writer` |
| `Authority::vacate`, `Authority::install` | `generation_survives_vacancy` | `ErasureCommit.vacate` and the generation-preserving `Step.grant` |
| `publish_selection`, `admits_history` | `publication_closes_old_history` | `ErasureCommit.erasure_floor` and `admits_history` |

The writer projection reuses PL1's enrollment, epoch and generation identity.
The Rust cut projects as an exact LSN and prefix digest pair. Preparation
validation compares the cut, root and custody to the request, resolves the
exact retained cut and requires a nonzero manifest. An erasure preparation
must also name the same current grant and published base. The successor is
bounded by the two `u64` counters.

The reducer first validates, admits the recovery hold at the requested
checkpoint, and installs the successor. It then closes the old roots and
updates the selected checkpoint and erasure floor in the same decision.
The floor applies to fresh replay admission and checkpoint opening. The
Verus laws cover the guards, selection fields, authority and append writer
check. The branch sequencing and iteration that closes old roots have source
inspection and native acceptance coverage. An exact mutation retry can still
return an earlier successful append's receipt through PL1's receipt rules.

[Study 112](../../112-erasure-rotation/ErasureCommit.lean) defines
`MayCommit` and `Fenced` over crash-selectable images. The
[package model](../../lean/Logkeeper/ErasureCommit.lean) carries that theorem
and adds the ordered rotation reference. In its unbounded authority traces,
ordinary grants and vacancy preserve the generation and rotations increase
it. Exact append authorization then excludes the revoked generation from
fresh suffix writes. Study 112's recovery result also requires every
selectable slot to hold a clean root. Establishing that premise, the semantic
cleanliness of a checkpoint, physical key custody, snapshot establishment,
and end-to-end reducer refinement remain outside the production proof.

With the pinned F0 runner, run
`python3 verification/verus/run.py --verus /path/to/shared/tools/verus ordered_rotation`.
Run `python3 verification/lean/run_ordered_lease_rotation.py` for the
reference theorems and controls, and `run_ordered_correspondence.py` in the
same directory for sampled Lean and Verus agreement.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
