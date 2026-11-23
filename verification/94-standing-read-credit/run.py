#!/usr/bin/env python3
"""Check pool-local standing read funding through rotation and handoff."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def run(policy, scenario, *, variant="reference", progress=None, invariant=None, expected=None):
    values = {"Policy": f'"{policy}"', "Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (invariant,) if invariant else ("Conserves", "OriginalStillPaid", "ExactNewOwner", "KeepsOrder", "NoReinstall")
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    check_tla(ROOT, "StandingReadCredit", f"{policy}-{scenario}-{variant}", "Fair" if progress else "Spec",
              values, checks, expected=expected)


def verify_tla():
    run("advance-issued-first", "orphan", progress="Finishes", expected="liveness")
    run("standing", "orphan", variant="rebind-old-physical-credit", invariant="ExactNewOwner", expected="ExactNewOwner")
    run("standing", "hidden", variant="refund-from-silence", invariant="OriginalStillPaid", expected="OriginalStillPaid")
    run("standing", "hidden", variant="omit-hidden-assignment", invariant="OriginalStillPaid", expected="OriginalStillPaid")
    run("standing", "reoffer", variant="forget-window-watermark", invariant="NoReinstall", expected="NoReinstall")
    run("standing", "full", variant="ignore-overlap", invariant="Conserves", expected="Conserves")
    run("standing", "uncovered", variant="require-fusion-for-publication",
        progress="WritesAndFallsBack", expected="liveness")

    for scenario in ("orphan", "hidden", "full", "reoffer"):
        run("standing", scenario, progress="Finishes")
    run("standing", "uncovered", progress="WritesAndFallsBack")


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
                                        "88-retained-delivery/DeliveryBook.lean",
                                        "88-retained-delivery/RetainedDelivery.lean",
                                        "93-atomic-read-capture/AtomicReadCapture.lean"))
    source = ROOT / "StandingReadCredit.lean"
    check_lean_mutation(ROOT, command, source, "exhaustion",
                        [("  available : grant.used < grant.window.serials.size",
                          "  available : True")],
                        "  exact ready.available")
    check_lean_mutation(ROOT, command, source, "watermark",
                        [("  newer : state.installedThrough < next.generation",
                          "  newer : True")],
                        "    exact Nat.not_lt_of_ge spent ready.newer")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
