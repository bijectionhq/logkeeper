# Study 87 · Authorize recovered replies in the journal order

2026-11-23

## Question

Can a recovery endpoint reissue the original protected reply under current authority while competing with close, slot reuse, and handoff?

## Sources

Use [S04, S08, S11, S68–S73, L05, and B23](../requirements.md), the [read-index proof](../29-read-index/report.md), the [read admission and nonce proofs](../84-read-invocation-floor/report.md), and [atomic attachment and protected delivery](../86-atomic-recovery-publication/report.md).

## Model and comparisons

Compare a chosen control frame with reusing a read-index probe as delivery permission, accepting a data frontier as a command frontier, and weakening permit, payment, position, or scope checks.
Exercise an unseen close, overlapping close, permit-slot reuse, retirement, a sealed predecessor, and a prepared operation overtaken by another command.
Model the data frontier as fixed in these histories.
For the general proofs, use the shared ordered reducer, exact quorum choice, and the scoped protected delivery token.
Abstract the authenticity of the installed journal identity and the physical borrow evidence.

## Properties and programs

- A successful delivery uses the exact live original row, permit serial, basis, and independently paid protection at its chosen position.
- A closed or recycled row and a sealed predecessor refuse a new delivery.
- Recovery by the original invocation locates the exact result without the caller's old permit.
- A prepared physical proof remains usable by the same operation if only its proposed ordered position changed and its original basis is still live.
- A chosen exact result can complete through authority loss while its original borrow remains held.
- An already protected retired result remains recoverable under the current journal with its original backing.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0, and Python 3.13.
Run negative controls first.
Keep the generated commands, proof logs and traces in .results/.
