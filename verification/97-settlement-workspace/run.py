#!/usr/bin/env python3
"""Check independent settlement with a fixed owner-local workspace."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, *, jobs=2, scratch=1, scenario="stalled-peer", variant="reference",
            invariant=None, expected=None):
    constants = {
        "JobCount": jobs, "ScratchUnits": scratch,
        "Scenario": f'"{scenario}"', "Variant": f'"{variant}"',
    }
    laws = ("Fits", "ChargedUntilPublished", "ExactPublication", "OnlyReadyHoldsWorkspace", "ScratchBound")
    checks = [("INVARIANT", law) for law in ((invariant,) if invariant else laws)]
    if not invariant:
        if variant == "hold-while-waiting":
            checks.remove(("INVARIANT", "OnlyReadyHoldsWorkspace"))
        checks.extend((("PROPERTY", "ReadyFinishes"), ("PROPERTY", "DelayedEvidenceSettles")))
    specification = "Spec" if invariant else "Fair"
    check_tla(ROOT, "SettlementWorkspace", name, specification, constants, checks, expected=expected)


def verify_tla():
    compare("remote-holder-safety", variant="hold-while-waiting",
            invariant="OnlyReadyHoldsWorkspace", expected="OnlyReadyHoldsWorkspace")
    compare("remote-holder-progress", variant="hold-while-waiting", expected="liveness")
    compare("fully-shared-progress", variant="no-reserve", expected="liveness")
    compare("refund-needs-ordinary-room", variant="require-ordinary-room", expected="liveness")
    compare("foreign-evidence", variant="foreign-evidence", invariant="ExactPublication",
            expected="ExactPublication")
    compare("refund-before-publication", variant="early-refund", invariant="ChargedUntilPublished",
            expected="ChargedUntilPublished")

    compare("stalled-peer")
    compare("all-ready", jobs=3, scenario="all-ready")
    compare("evidence-arrives", jobs=3, scenario="evidence-arrives")
    compare("per-obligation-extra-budget", scratch=2, variant="per-obligation")
    compare("restart-refund-and-refill", invariant="NoRestartRefundAndRefill",
            expected="NoRestartRefundAndRefill")
    for variant, expected in (("race", "liveness"), ("growing-order", "liveness"), ("round-robin", None)):
        check_tla(ROOT, "ReadyTurns", f"ready-turns-{variant}", "Fair", {"Variant": f'"{variant}"'},
                  [("INVARIANT", "ParkedNeverOccupies"), ("PROPERTY", "ReadyTargetFinishes")],
                  expected=expected)


def verify_lean():
    pool_path = "72-pool-local-issuance/PoolState.lean"
    modules = ORDERED_SOURCE_MODULES[:ORDERED_SOURCE_MODULES.index(pool_path) + 1]
    command = compile_lean_modules(ROOT, modules)
    source = ROOT / "SettlementWorkspace.lean"
    check_lean_mutation(ROOT, command, source, "scratch-on-remote-wait",
                        [("  _hasLocalEvidence = true\n\ntheorem",
                          "  _hasLocalEvidence = _hasLocalEvidence\n\ntheorem")],
                        "  exact ready")
    check_lean_theorems(ROOT, command, source, count=9)
    check_lean_theorems(ROOT, command, ROOT / "ReadyTurns.lean", count=7, case="lean-ready-turns")


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
