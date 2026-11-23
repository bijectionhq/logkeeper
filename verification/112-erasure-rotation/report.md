# Study 112 · Erase journal-retained history by key-generation rotation

2026-11-23

## Verdict

An erasure rotates the journal payload key generation at an ordered cut, where a clean successor root is published.
The commit must wait until every crash-selectable slot holds a clean root.
Otherwise a crash can select the older root, which either restores erased history before revocation or needs the revoked key afterwards.
This refines A445: an older selector keeps its holds while selectable, and an erasure must first make it unselectable.

Every record after the cut must use the new generation.
The Logkeeper grant fence enforces this when the generation rides on the grant: the rotation installs a new grant for the same worker, and the journal refuses appends under the superseded grant.
Held views keep their answers until the deadline and then receive `rtdb/erased-under-view`.
Revoking them at commit breaks RTDB's admitted-view contract.

The RTDB audit at `fd3d6dcb32` shows none of this exists yet.
RTDB has one key per deployment, SQL `ERASE` destroys no key, replay fails closed on a missing key, and `erased-under-view` is not implemented.

## General proofs

Lean 4.35.0 checked three theorems with standard axioms only.
`every_selectable_recovery_avoids_the_revoked_generation` holds for any list of selectable images under the commit rule and the grant fence.
`an_older_selectable_root_forbids_the_commit` and `an_unfenced_old_record_is_unreadable_after_revocation` show both premises are necessary.
The Lean control drops the fence and fails at the main proof.

## Bounded comparison

| Weakened design | Result |
| --- | --- |
| Commit while the old root is selectable | Restores erased history in four transitions. |
| Revoke with the old root selectable | Recovery becomes impossible in five transitions. |
| Admit an old-generation append after the cut | Recovery becomes impossible in seven transitions. |
| Revoke the held view at commit | The view fails before its deadline in five transitions. |

The reference holds in 78 states, with eventual commit and deadline under fairness of rotation, slot publication, commit and expiry.
Witnesses reach clean recovery after the deadline in six transitions and an erased held view in six transitions.

## Amendments

[A461–A463](../amendments.md#study-112--2026-11-23).

## Residue

The model abstracts the provider's revocation guarantee, the clock, cache invalidation and the content of the clean successor.
Constructing the clean successor (RTDB R7 step 2), the per-generation key service, the generation tag on grants, and tolerant replay in RTDB are implementation work.
A generation tag on the grant needs a Logkeeper grant field and a codec change.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/112-erasure-rotation/run.py
```

## Logkeeper implementation review

The C3 patch proposes an ordered rotation that compares the exact current grant, exact published checkpoint, and data head.
The head must still equal the checkpoint cut when the decision applies.
An intervening append makes the rotation stale.
An accepted rotation advances the writer epoch and key generation together, retaining the same worker enrollment and admitting an empty-suffix recovery hold at the checkpoint.
Ordinary writer replacement preserves the generation, including after a vacancy.
The record hash covers the grant's key generation, and held replay returns each record's original grant.

The application reducer checks journal identities and the published cut.
RTDB must establish that the selected checkpoint is semantically clean and that every crash-selectable slot carries a clean recovery image before committing revocation.
The model's two slots denote those crash-selectable images.
The reducer's selected checkpoint is the ordered recovery basis used to condition the grant change.

The implementation test exercises a stale cut, stale grant, a grant with the wrong generation at the current writer epoch, retained old-view replay, and vacant-state recovery after rotation.
The Logkeeper suite passed 76 tests, with one throughput test ignored.
Removing the exact-head check or bypassing the append fence failed the corresponding assertion in the rotation test.
The bounded model continues to cover one rotation, two selectable slots, at most one append from each modeled generation, one crash selection, and one held read.
