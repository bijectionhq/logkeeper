# Study 22 report · Checkpoint transfer between physical residences

2026-11-22

## Verdict

Publish the replacement only after verifying each required logical member against the captured source and durably registering the exact target dependency versions.
Physical locations and pack layouts can change.
The publication decision compares the current referrer's root and catalog revision against the captured origin, and checks the destination's exact current residence and root version.

New snapshots can use the replacement immediately.
Existing snapshots and physical reads keep their source custody until their own release conditions hold.
A verified current target can publish during source disconnection.
Source erasure still waits for its outstanding interests and verifiable disposal.

## TLC results

The three safety invariants and both conditional progress properties hold across 512 distinct states with one referrer and 4,672 with two.
The drain-first candidate holds the safety and disposal properties across 464 states with one referrer.
Its separate witness search with observation enabled excludes concurrent new and old reads in 512 states.
The whole-pack equality candidate is safe and enforces the same conditional progress for admitted copies at the one-referrer bound, across 416 states, but excludes the valid repack program.

| Amendment | Weakening | Shortest safety counterexample |
| --- | --- | --- |
| A71 | `skip_bytes` | Prepare a different logical image, approve it, and publish. Three transitions. |
| A71 | `skip_closure` | Publish with an omitted dependency even though the observed input values agree. Three transitions. |
| A72 | `stale_catalog` | Advance the referrer's catalog between preparation and publication, then activate the old proof. Four transitions. |
| A72 | `stale_target` | Replace the physical destination after verification and activate using its old receipt. Four transitions. |
| A72 | `wrong_referrer` | Apply one referrer's copy receipt to another referrer with the same view shape. Three transitions. |
| A73 | `reclaim_verified` | Verify the copy, reclaim its registered staging bytes, and activate under the stale receipt. Four transitions. |
| A73 | `swap_verified_version` | Verify a complete pack, substitute its index and contents under the receipt, then activate. Four transitions. |
| A74 | `skip_referrer` | Move one referrer and authorize source disposal while another still points there. Four transitions. |
| A74 | `skip_snapshot` | Reserve a snapshot, publish the replacement, and authorize disposal while the old snapshot can still open dependencies. Five transitions. |
| A74 | `skip_reader` | Admit an old I/O borrow, publish the replacement, and authorize disposal while the borrow is active. Five transitions. |

The positive repack takes three transitions.
Activation after source disconnection takes four.
A five-transition witness opens a new borrow after the swap using an earlier snapshot's still-live source reservation.
In eleven transitions two referrers move, an old admitted borrow overlaps a new target read, the old borrow finishes, and the source is erased.
One fourteen-transition witness couples the repack with offline activation, then opens a dependency through the old snapshot after source access returns and settles both referrers before erasing the source.
The model authorizes irreversible disposition at `FenceSource`.
Earlier closure of new source admission can occur while old borrowed bytes remain protected.

When activation requires the source link, TLC finds a temporal counterexample with a stable ready target.
When the source remains inaccessible after disposition authorization, unconditional erasure completion fails.
The baseline checks fair activation for continuously eligible targets and fair disposal after authorization when source access stabilizes.

## General proofs

Fourteen [Lean theorems](ResidenceTransfer.lean) use only standard axioms.
They prove exact member range selection and reject out-of-range or truncated reads.
Equivalent closures give identical inputs for every finite read sequence over the declared members.
A concrete repack preserves all logical members while changing the carrier bytes.
A different index over the same destination carrier fails that equivalence.

The publication evidence binds the verified manifests to the authenticated current source capture and the exact installed destination.
The destination registration must still be live.
Binding the same logical inputs to the checkpoint codec yields an equally certified replacement and identical replay for every journal suffix.
A constructive adoption refines the prior catalog transition while leaving the logical stream state and published cut equal.
The disposal proof composes the shared-custody trace and preserves every live root after safely erasing an unreferenced, unborrowed physical version.
An admitted old snapshot blocks disposition of any reachable physical version even before it has issued its first I/O.

Four proof controls break the laws when source capture binding, target binding, logical equivalence, or live target registration is removed.

## Residue

The range and replay proofs assume complete enumeration of actual RTDB dependencies and the authenticated decoder that gives each captured or installed manifest its logical members.
The model treats representation changes such as re-encryption through that decoder boundary.
Actual decoder refinement, provider attestation and destination write fencing remain open.
The bounded runs permit one target incarnation change before any referrer activates.
Repeated simultaneous rehomes, durable installation of registration metadata, source write-lease and inventory settlement, and closure of the old custody route across authority changes remain obligations.
For an installed grant, the source residence and its read or release path stay addressable until exact settlement.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/22-residence-transfer/run.py
```
