#!/usr/bin/env python3
"""Verify one-use read invocations and the durable bounded floor."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(scenario, name, laws=(), *, temporal=None, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if temporal:
        checks.append(("PROPERTY", temporal))
    variant = name if expected else "reference"
    check_tla(ROOT, "InvocationFloor", name, "Fair" if temporal else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("compact", "live-rows-only", ("ExactlyOnce",), expected="ExactlyOnce")
    check("compact", "rollback-floor", ("ExactlyOnce",), expected="ExactlyOnce")
    check("gap", "high-water", ("NoImplicitSkip",), expected="NoImplicitSkip")
    check("gap", "no-abandon", temporal="GapProgress", expected="liveness")
    check("fence", "no-grant", ("CurrentGrant",), expected="CurrentGrant")
    check("exhaust", "wrap", ("ExactlyOnce",), expected="ExactlyOnce")

    laws = ("ExactlyOnce", "NoImplicitSkip", "CurrentGrant", "WithinLimit")
    check("compact", "compacted-retry", laws)
    check("gap", "chosen-abandon", laws, temporal="GapProgress")
    check("fence", "replacement", laws, temporal="FenceProgress")
    check("exhaust", "exhausted", laws)


def verify_lean():
    floor = "83-ordered-read-replay/ReadInvocationFloor.lean"
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        floor,
                                        "83-ordered-read-replay/OrderedReadReplay.lean"))
    check_lean_mutation(ROOT, command, ROOT.parent / floor, "allow-gaps",
                        [("nonce = floor + 1 ∧ nonce < wordLimit width",
                          "floor + 1 ≤ nonce ∧ nonce < wordLimit width")],
                        "  exact Nat.le_of_eq fresh.2.1")
    check_lean_theorems(ROOT, command, ROOT / "InvocationFloorProof.lean", count=11)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
