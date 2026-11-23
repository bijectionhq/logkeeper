#!/usr/bin/env python3
"""Check published provider fences, exact media, and usable recovery selectors."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("NoRetiredScopeReopens", "ExactApplication", "RecoveryOnlyAppliesChosen", "HasDurableRetirement")


def check(name, laws, *, limit=2, variant="reference", expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"'}
    check_tla(ROOT, "DurableRoot", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("omit_data_barrier", "HasDurableRetirement"),
        ("omit_name_barrier", "HasDurableRetirement"),
        ("open_at_base", "NoRetiredScopeReopens"),
        ("intact_is_chosen", "RecoveryOnlyAppliesChosen"),
    ):
        check(f"control-{variant}", (law,), limit=1, variant=variant, expected=law)
    for missing in ("data", "name"):
        law = "NoRetiredScopeReopens"
        check(f"control-crash-without-{missing}-barrier", (law,), limit=1,
              variant=f"omit_{missing}_barrier", expected=law)
    check("two-root-decisions", LAWS)
    check("three-root-decisions", LAWS, limit=3)
    law = "NeverRejectsDelayedCreateAfterRecovery"
    check("witness-refuse-old-create-after-rotation", (law,), limit=3, expected=law)
    law = "NeverRecoversUnlearnedRetirement"
    check("witness-earlier-selector-and-unlearned-retirement", (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "25-media-crash-consistency/MediaCrash.lean",
        "26-journal-rotation/JournalRotation.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "55-pool-incarnations/PoolIncarnations.lean",
        "58-storage-effect-boundary/StorageBoundary.lean",
        "59-namespace-closure/NamespaceClosure.lean",
    ))
    source = ROOT / "DurableRoot.lean"
    check_lean_mutation(ROOT, command, source, "publish-before-byte-sync",
        (("if vote.bytesStable = true ∧ vote.nameStable = true", "if True ∧ vote.nameStable = true"),),
        "refine ⟨⟨permitted.1, permitted.2.1⟩")
    check_lean_mutation(ROOT, command, source, "admit-intact-unchosen-frames",
        (("then some (physical.take chosen.length) else none", "then some physical else none"),),
        "exact List.take_append_length")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
