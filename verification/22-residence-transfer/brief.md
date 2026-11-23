# Study 22 · Checkpoint transfer between physical residences

## Question

What lets a referrer adopt a physically different copy of its checkpoint, keep its exact replay basis, and eventually allow safe erasure of the old residence?

## Sources

Use [checkpoint reconstruction](../16-checkpoint-reconstruction/report.md), [snapshot admission](../18-snapshot-admission/report.md), [shared object custody](../19-shared-object-custody/report.md), and the [custody channel lifecycle](../21-custody-channel-lifecycle/report.md).
RTDB Multi at `fc6da3a4a3` specifies this boundary through `TransferSharedObjects`, `EraseAndProve`, `WithdrawForkReferences`, and `AuthorizeHostedVersionErasure`.
`ForkAcrossOrganisations` and `HostedCheckpointCapture` specify exact physical pack dependencies and verification of complete capture inputs.

## Model and properties

TLC models one or two referrers of a source, a target preparation, an optional target incarnation change before activation, a catalog revision change, one old logical snapshot, one admitted physical borrow, and source connectivity.
The pack model distinguishes logical contents from their physical encoding and lookup index.
Check that an activated root has the exact current origin and target scope, complete equivalent contents, and protected source custody for every remaining referrer and reader.
Check weakly fair activation while exact registration and publication eligibility remain stable, and weakly fair disposal after authorization and eventual stable source access.
Lean models arbitrary declared members and immutable pack ranges, validates the effect of a repack on every declared read sequence, and composes replacement with checkpoint replay and exact shared-custody disposal.

## Comparison

Compare equality at logical member boundaries with byte-for-byte equality of the carrier.
Compare overlapping source and target reads with drain-before-publication.
Check incomplete or wrong bytes, a physical pack substituted after verification, activation from a stale receipt, and disposal with a live referrer, old snapshot or active read remaining.
Exercise activation after source access fails, later new I/O from an already reserved old snapshot, and disposal of the source only after both referrers have moved and the old read has finished.

The study assumes authentic source captures, complete dependency enumeration, deterministic checkpoint decoding, and provider version identity and custody matching the receipts.
It abstracts provider cryptography, simultaneous transfers of the same referrer, actual authority voting, and old namespaces with incomplete multipart cleanup.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/22-residence-transfer/run.py` with tool paths as in the [verification index](../README.md).
The runner stores exact commands, configs, proof controls, and traces under the ignored results directory.
See the [report](report.md) for results and limits.
