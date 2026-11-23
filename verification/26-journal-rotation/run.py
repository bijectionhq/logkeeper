#!/usr/bin/env python3
"""Compare restart, repeated rotation, and exact extent reclamation policies."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("EveryCrashRootRecovers", "VisibleRootRecovers", "ExactBorrowSurvives", "TwoPossibleRoots")


def check(name, laws, *, variant="bound_parent", expected=None, generations=2, records=2, losses=1):
    constants = {"Variant": f'"{variant}"', "MaxGeneration": generations,
                 "MaxRecord": records, "MaxPowerLosses": losses}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "Rotation", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
    ))
    source = ROOT / "JournalRotation.lean"
    check_lean_mutation(ROOT, command, source, "allow-second-uncertain-selector",
        (("def CanPublish (state : State Record) : Prop :=\n  state.stable = state.visible",
          "def CanPublish (_state : State Record) : Prop := True"),),
        "exact allowed\n      intro view")
    check_lean_mutation(ROOT, command, source, "forget-stable-recovery-view",
        (("  ¬ Needed state.stable extent ∧ ¬ Needed state.visible extent ∧ state.pins extent = none\n\ndef update",
          "  ¬ Needed state.visible extent ∧ state.pins extent = none\n\ndef update"),),
        "exact allowed\n\nprivate theorem erase_preserves_exact")
    check_lean_mutation(ROOT, command, source, "permit-reclaim-while-borrowed",
        (("  ¬ Needed state.stable extent ∧ ¬ Needed state.visible extent ∧ state.pins extent = none\n\ndef update",
          "  ¬ Needed state.stable extent ∧ ¬ Needed state.visible extent\n\ndef update"),),
        "exact allowed\n\nprivate theorem erase_preserves_exact")
    check_lean_mutation(ROOT, command, source, "count-copies-without-local-exact-records",
        (("    (copyRefines : ∀ replica ∈ journal.members, ∀ position entry, available replica = true →\n"
          "      journal.copies replica position entry → (before replica).history[position]? = some entry)",
          "    (copyRefines : ∀ replica ∈ journal.members, ∀ position entry, available replica = true →\n"
          "      journal.copies replica position entry → True)"),),
        "exact copyRefines replica member position entry online copy")
    check_lean_theorems(ROOT, command, source, count=14)


def main():
    verify_lean()
    for variant, law in (
        ("trust_warm_name", "EveryCrashRootRecovers"),
        ("trust_warm_name", "VisibleRootRecovers"),
        ("forget_borrow_after_restart", "ExactBorrowSurvives"),
        ("stale_base", "EveryCrashRootRecovers"),
        ("stack_unstable", "EveryCrashRootRecovers"),
        ("stack_unstable", "TwoPossibleRoots"),
    ):
        check(f"control-{variant}-{law}", (law,), variant=variant, expected=law)
    for records in (2, 3):
        check(f"parent-{records}", LAWS, records=records, losses=2)
    check("revalidate", LAWS, variant="revalidate", records=3, losses=2)
    check("stable-open", (*LAWS, "NeverWarmServesBeforeSync"), variant="stable_open")
    check("drain-before-publish", (*LAWS, "NeverPinsOldWhileReclaimsMiddle"), variant="drain_before_publish")
    check("witness-restart-before-sync", ("NeverWarmServesBeforeSync",),
          expected="NeverWarmServesBeforeSync")
    check("witness-revalidate-stale-parent", ("NeverStaleCandidatePublishes",),
          variant="revalidate", expected="NeverStaleCandidatePublishes")
    for law in ("NeverRecoversWarmVoteOnPredecessor", "NeverPinsOldWhileReclaimsMiddle",
                "NeverRecoversTwoSuccessiveLosses"):
        check(f"witness-{law}", (law,), expected=law, losses=2)


if __name__ == "__main__":
    main()
