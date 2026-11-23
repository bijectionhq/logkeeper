# Study 19 · Custody of shared checkpoint objects

## Question

Can a checkpoint, fork or admitted reader retain an immutable physical version while other roots release it and a delayed reaper runs?

## Sources

Use the [snapshot admission model](../18-snapshot-admission/report.md), [checkpoint exact-cut model](../16-checkpoint-reconstruction/report.md), [physical borrow model](../14-read-custody/report.md), and [terminal erasure model](../04-retirement/report.md).
RTDB Multi at `fc6da3a4a3` specifies same-lineage sharing, independent copies across organisations, lineage revisions and retirement fences in `Fork`, `ForkAcrossOrganisations`, `TransferSharedObjects`, and `AuthorizeHostedVersionErasure`.
The existing RTDB spec requires surviving referrers to receive readable copies before the source residence is erased.

## Model and properties

TLC models two versions, two or three manifest roots, a delayed acquisition per declared root-version pair, release, one physical borrow, and separate disposal fencing and provider deletion.
Both versions may share a provider name.
The graph distinguishes a direct receipt from the complete flattened dependency closure.
The safety laws require complete live roots, exact-version protection for references and borrows, and terminal release.
The temporal check requires weakly fair provider deletion and eventual stable access after authorization.
Lean models arbitrary root and version universes indexed by natural identities, arbitrary dependency graphs, arbitrarily many borrows counted per version, and arbitrary finite traces.
Its product model links the snapshot catalog's registered root to all reachable physical versions.

## Comparison

Compare publish-before-complete, scan-then-delete without revalidation, acquisition against a closed version, release that permits a delayed acquisition, early withdrawal of a live root, deletion based on a key alone, and reclaiming while a borrow remains.
Require acceptance traces for a surviving fork, a release that arrives before its acquisition, and a replacement root in place before withdrawal and deletion of the source version.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/19-shared-object-custody/run.py` from the checkout with tool paths as in the [verification index](../README.md).
The runner stores exact commands and diagnostics in the ignored study-local results directory.
See the [report](report.md) for outcomes and scope.
