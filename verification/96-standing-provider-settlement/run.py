#!/usr/bin/env python3
"""Check original-provider closure and bounded retirement of standing windows."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def run(scenario, *, variant="reference", invariant=None, progress=False, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (invariant,) if invariant else (
        "HeldExactly", "CanStartOnlyAdmitted", "NoReuse", "ChargedUntilAbsent", "Fits", "BoundedEvidence",
    )
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallyRotates"))
    check_tla(ROOT, "StandingProviderSettlement", f"{scenario}-{variant}", "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    run("hidden", variant="fence-local-seen", invariant="HeldExactly", expected="HeldExactly")
    run("unused", variant="fence-not-exact", invariant="CanStartOnlyAdmitted", expected="CanStartOnlyAdmitted")
    run("hidden", variant="ignore-terminal", invariant="NoReuse", expected="NoReuse")
    run("retained", variant="refund-with-data", invariant="ChargedUntilAbsent", expected="ChargedUntilAbsent")
    run("unused", variant="permit-absent-issued", invariant="NoReuse", expected="NoReuse")
    run("retained", variant="keep-tombstones", invariant="BoundedEvidence", expected="BoundedEvidence")
    run("retained", variant="need-spare-to-refund", progress=True, expected="liveness")
    for scenario in ("hidden", "retained", "unused"):
        run(scenario, progress=True)


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
                                        "84-read-invocation-floor/InvocationFloorProof.lean",
                                        "88-retained-delivery/DeliveryRecovery.lean",
                                        "89-sealed-delivery-handoff/SealedDeliveryHandoff.lean",
                                        "93-atomic-read-capture/AtomicReadCapture.lean",
                                        "94-standing-read-credit/StandingReadCredit.lean",
                                        "95-standing-read-recovery/StandingReadRecovery.lean"))
    source = ROOT / "StandingProviderSettlement.lean"
    check_lean_mutation(ROOT, command, source, "ignore-frozen-row",
                        [("  _fence.book.rows _operation.slot = some _operation.entry\n\ntheorem",
                          "  True\n\ntheorem")],
                        "  exact selected")
    check_lean_theorems(ROOT, command, source, count=14)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
