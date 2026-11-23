#!/usr/bin/env python3
"""Compare fixed preparation, split admission, and delegated atomic capture."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def run(path, scenario, *, variant="reference", progress=None, invariant=None, expected=None):
    values = {"Path": f'"{path}"', "Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (invariant,) if invariant else ("Exact", "Funded", "Atomic", "NoReuse", "FewerDecisions")
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    check_tla(ROOT, "AtomicReadCapture", f"{path}-{scenario}-{variant}", "Fair" if progress else "Spec",
              values, checks, expected=expected)


def verify_tla():
    run("fixed", "churn", progress="Finishes", expected="liveness")
    run("fixed", "churn", variant="trust-overtaken", invariant="Exact", expected="Exact")
    run("delegated", "uncovered", variant="uncovered-credit", invariant="Funded", expected="Funded")
    run("delegated", "fenced", variant="cached-credit", invariant="Funded", expected="Funded")
    run("delegated", "full", variant="keep-partial-capture", invariant="Atomic", expected="Atomic")
    run("delegated", "duplicate", variant="reuse-credit", invariant="NoReuse", expected="NoReuse")
    run("delegated", "duplicate", variant="abandon-assigned", invariant="Funded", expected="Funded")
    run("delegated", "loss", variant="recontact", progress="Finishes", expected="liveness")

    run("delegated", "still", variant="provider-withdraws", invariant="Funded", expected="Funded")
    run("delegated", "replacement", variant="old-writer-only", progress="ReturnsAfterReplacement", expected="liveness")

    run("fixed", "still", progress="Finishes")
    run("delegated", "still", progress="Finishes")
    run("delegated", "replacement", progress="ReturnsAfterReplacement")
    run("split", "churn", progress="Finishes")
    run("delegated", "churn", progress="Finishes")
    run("delegated", "loss", progress="Finishes")
    run("delegated", "duplicate", progress="Finishes")
    for scenario in ("uncovered", "fenced", "full"):
        run("delegated", scenario, progress="Refuses")


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
                                        "88-retained-delivery/RetainedDelivery.lean"))
    source = ROOT / "AtomicReadCapture.lean"
    check_lean_mutation(ROOT, command, source, "ignore-exact-basis",
                        [("  coverage : rules.covers credit basis",
                          "  coverage : True")],
                        "  exact paid.coverage")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
