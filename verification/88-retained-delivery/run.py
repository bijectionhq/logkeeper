#!/usr/bin/env python3
"""Check the bounded delivery book, recovery, and exact settlement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(scenario, name, laws=(), *, progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "Finishes"))
    variant = name if expected else "reference"
    check_tla(ROOT, "RetainedDelivery", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("recovery", "couple-read-slot", ("Recoverable",), expected="Recoverable")
    check("recovery", "visible-only", ("Recoverable",), expected="Recoverable")
    check("wrong-settlement", "ignore-settlement-identity", ("ExactSettlement",), expected="ExactSettlement")
    check("reuse", "ignore-issued", ("NoReuse",), expected="NoReuse")
    check("capacity", "ignore-capacity", ("Fits",), expected="Fits")
    check("recovery", "pin-raw-frame", progress=True, expected="liveness")

    laws = ("Recoverable", "ExactSettlement", "NoReuse", "Fits")
    check("recovery", "recover-after-compaction", laws, progress=True)
    check("wrong-settlement", "exact-settlement", laws)
    check("reuse", "recycled-slot", laws)
    check("capacity", "bounded-capacity", laws)


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
                                        "88-retained-delivery/RetainedDelivery.lean"))
    source = ROOT / "RetainedDelivery.lean"
    check_lean_mutation(ROOT, command, source, "bypass-the-book",
                        [("  | .source (.deliver _ _) => (advance before, .refused)\n",
                          "  | .source (.deliver request evidence) =>\n"
                          "      (advance before, .source (OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence))\n")],
                        "  rfl\n\ntheorem a_successful_grant")
    check_lean_theorems(ROOT, command, ROOT / "DeliveryRecovery.lean", count=20)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
