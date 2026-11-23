#!/usr/bin/env python3
"""Check selective admission through ordered read recovery and writer handoff."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, variant="reference", selector="old", invariant=None, expected=None):
    constants = {
        "Scenario": f'"{scenario}"', "Variant": f'"{variant}"', "Select": f'"{selector}"',
    }
    laws = ("NoDuplicate", "CurrentGrantOnly", "ClosesKeepDelivery")
    checks = [("INVARIANT", law) for law in ((invariant,) if invariant else laws)]
    if not invariant:
        checks.append(("PROPERTY", "Progress"))
    check_tla(ROOT, "SelectiveOrderedRecovery", name, "Spec" if invariant else "Fair",
              constants, checks, expected=expected)


def verify_tla():
    compare("old-selector-omits-suffix", "same-scope", variant="omit-suffix", invariant="NoDuplicate",
            expected="NoDuplicate")
    compare("new-selector-loses-bitmap", "same-scope", variant="drop-sparse-marks", selector="new",
            invariant="NoDuplicate", expected="NoDuplicate")
    compare("close-resets-bitmap", "same-scope", variant="clear-window-on-close", invariant="NoDuplicate",
            expected="NoDuplicate")
    compare("ignore-exact-grant", "handoff", variant="ignore-grant", invariant="CurrentGrantOnly",
            expected="CurrentGrantOnly")
    compare("close-removes-independent-use", "handoff", variant="drop-delivery-on-close",
            invariant="ClosesKeepDelivery", expected="ClosesKeepDelivery")
    compare("strict-next-stalls-on-gap", "same-scope", variant="next-only", expected="liveness")
    for selector in ("old", "new"):
        compare(f"same-scope-{selector}", "same-scope", selector=selector)
        compare(f"sealed-handoff-{selector}", "handoff", selector=selector)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        "83-ordered-read-replay/OrderedReadReplay.lean",
                                        "84-read-invocation-floor/InvocationFloorProof.lean",
                                        "88-retained-delivery/DeliveryBook.lean",
                                        "88-retained-delivery/RetainedDelivery.lean",
                                        "88-retained-delivery/DeliveryRecovery.lean",
                                        "101-selective-read-window/SelectiveReadWindow.lean"))
    source = ROOT / "SelectiveOrderedRecovery.lean"
    check_lean_mutation(ROOT, command, source, "ignore-exact-grant",
                        [("  current = .active writer\n\ntheorem",
                          "  current = current ∧ writer = writer\n\ntheorem")],
                        "  exact active")
    check_lean_theorems(ROOT, command, source, count=11)
    compile_lean_modules(ROOT, ("102-selective-ordered-recovery/SelectiveOrderedRecovery.lean",))
    check_lean_theorems(ROOT, command, ROOT / "SelectiveCheckpoint.lean", count=5, case="lean-checkpoint")


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
