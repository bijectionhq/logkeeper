#!/usr/bin/env python3
"""Check bounded activation attempt markers and the compressed logical view."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("NoReopenClosed", "NoStrandedPreparation", "RecordedPhysicalObligations",
          "PreservesSelection", "BoundedCredit", "BoundedMarkers", "BoundedPins")


def check(name, laws, *, attempts=4, width=2, pins=2, policy="ready_or_spent",
          variant="reference", expected=None):
    constants = {"Attempts": attempts, "Width": width, "PinLimit": pins,
                 "Policy": f'"{policy}"', "Variant": f'"{variant}"'}
    check_tla(ROOT, "AttemptCompaction", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("ignore_floor", "NoReopenClosed"),
        ("forget_floor", "NoReopenClosed"),
        ("skip_unresolved", "NoStrandedPreparation"),
        ("forget_live", "PreservesSelection"),
        ("forget_cleanup", "RecordedPhysicalObligations"),
        ("offer_is_credit", "BoundedCredit"),
        ("unmetered", "BoundedPins"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law, pins=1 if variant == "unmetered" else 2)
    for attempts, width, pins in ((3, 1, 1), (5, 3, 2)):
        for policy in ("ready_or_spent", "terminal_only"):
            check(f"{policy}-{attempts}-{width}-{pins}", SAFETY, attempts=attempts, width=width,
                  pins=pins, policy=policy)
    program = "NeverIssuesPastWidthWhileOldChoiceHeld"
    check("terminal-only-excludes-ready-compaction", (program,), policy="terminal_only",
          attempts=3, width=1, pins=1)
    check("witness-ready-compaction", (program,), attempts=3, width=1, pins=1, expected=program)
    for law in ("NeverKeepsCleanupThroughCompactionAndReplacement", "NeverSettlesAfterCompactionAndReplacement"):
        check(f"witness-{law}", (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "34-pending-activation/PendingActivation.lean",
    ))
    source = ROOT / "AttemptCompaction.lean"
    check_lean_mutation(ROOT, command, source, "compact-over-unresolved-attempt",
        (("def Resolved (table : Nat → Holding Image) (id : Nat) : Prop :=\n  table id ≠ .absent",
          "def Resolved (_table : Nat → Holding Image) (_id : Nat) : Prop := True"),),
        "exact safe.2")
    check_lean_mutation(ROOT, command, source, "delete-live-rows-below-cutoff",
        (("    | holding => holding", "    | .ready _ => .absent\n    | .absent => .absent"),),
        "have exactWhenCovered")
    check_lean_mutation(ROOT, command, source, "discard-cleanup-with-closed-marker",
        (("{book with cutoff, raw := {book.raw with attempts := Trimmed cutoff book.raw.attempts}}",
          "{book with cutoff, raw := {book.raw with attempts := Trimmed cutoff book.raw.attempts}, cleanup := fun _ => False}"),),
        "exact Eq.refl book.cleanup")
    check_lean_theorems(ROOT, command, source, count=7)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
