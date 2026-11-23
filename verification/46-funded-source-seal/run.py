#!/usr/bin/env python3
"""Compare source-ordered and externally bound recovery capacity decisions."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("Pointwise", "ExactVector", "FencesHold", "NoStrandedCommitment", "RetirementResolvesPlans")
TEMPORAL = ("RetirementFinishes", "AbortsSettle", "SealedInstalls")


def check(name, laws, *, attempts=1, variant="joint", moving=False, expected=None):
    constants = {"Attempts": attempts, "Variant": f'"{variant}"', "Moving": "TRUE" if moving else "FALSE"}
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    check_tla(ROOT, "FundedSeal", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law, attempts in (
        ("split", "NoStrandedCommitment", 1),
        ("seal_partial", "ExactVector", 1),
        ("borrow_old_receipts", "ExactVector", 2),
        ("forgotten_plan", "RetirementResolvesPlans", 1),
        ("reclaim_on_retirement", "ExactVector", 1),
        ("reopen_canceled_key", "FencesHold", 1),
    ):
        check(f"control-{variant}", (law,), variant=variant, attempts=attempts, expected=law)
    check("control-install-needs-source", ("SealedInstalls",),
          variant="requires_source_for_install", expected="liveness")
    check("joint-moving-pools", (*LAWS, *TEMPORAL), moving=True)
    check("joint-repeat-attempt", (*LAWS, *TEMPORAL), attempts=2)
    check("joint-repeat-with-moving-pools", LAWS, attempts=2, moving=True)
    for law, attempts, moving in (
        ("NeverRetiresWhilePoolMovesAndCloses", 1, True),
        ("NeverInstallsThenRetiresAtCapacity", 1, True),
        ("NeverCancelsThenSealsSecond", 2, False),
    ):
        check(f"witness-{law}", (law,), attempts=attempts, moving=moving, expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "44-prepared-capacity/PreparedCapacity.lean",
    ))
    source = ROOT / "FundedSeal.lean"
    check_lean_mutation(ROOT, command, source, "receipt-only-matches-target",
        (("  receipt.intent = intent ∧ receipt.pool = pool ∧ receipt.bytes = intent.needs pool",
          "  receipt.intent.target = intent.target ∧ receipt.pool = pool ∧ receipt.bytes = intent.needs pool"),),
        "exact matched.1")
    check_lean_mutation(ROOT, command, source, "release-without-source-abort",
        (("(abortEvidence : CanRelease system.source receipt.intent)",
          "(abortEvidence : True)"),),
        "have exactAbort : CanRelease before.source receipt.intent := handed")
    check_lean_theorems(ROOT, command, source, count=12)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
