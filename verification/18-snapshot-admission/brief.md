# Study 18 · Snapshot admission under checkpoint publication

## Question

Can an ordinary latest read obtain a reconstructable cut under concurrent checkpoint publication, trim, handoff, and delayed object disposal?

## Sources

Use [checkpoint reconstruction](../16-checkpoint-reconstruction/report.md), [physical read custody](../14-read-custody/report.md), and the [reference stream kernel](../07-reference/Kernel.lean).
RTDB Multi at `fc6da3a4a3` describes atomic root metadata and replay protection in `PublishCheckpoint` in `allium/rtdb-multi.allium`.
The corresponding path in `rust/crates/multi/src/store.rs` registers both fields in the storage-region directory update for normal receipted startup.
It separately refuses an explicit snapshot block if the checkpoint advanced.

## Model and properties

TLC models checkpoint custody registration, publication, logical and physical stages of disposal, read admission and response, WAL trim, one placement move, and reader connectivity.
Checkpoint starts, committed positions, and retention capacity are bounded.
Check that current and reserved bases stay available, retention stays bounded, and responses use their captured cut.
Check request progress under weakly fair install, admission and fetch with eventually stable reader connectivity.
Lean quantifies over arbitrary finite histories, checkpoint starts, read IDs and moves at the logical custody boundary, with capacity and effective drain as explicit premises.
It checks constructive admission and a projection onto the existing nonempty replay program.

## Comparison

Compare a fixed cut selected before reservation with selection and admission in one ordered decision.
Test variants that skip prior custody, reuse a receipt while disposal is in flight, and leave either old checkpoint or replay range unprotected.
Exercise an old basis read that reserved on the source and completes after migration and newer publication, plus one that needs only its checkpoint after trim.
Prepare endpoint or provider failures as controls for weakly fair progress.
The model abstracts actual manifest bytes, concurrent physical I/O within one fetch, retirement, and physical provider replication.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/18-snapshot-admission/run.py` with tool paths as in the [verification index](../README.md).
The runner checks separate Lean guard weakenings and bounded negative controls before each matching positive result.
See the [report](report.md) for results and scope.
