#!/usr/bin/env python3
"""Check exact combined seal transfer and the original delivery lifecycle."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(scenario, name, laws=(), *, progress=None, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    variant = name if expected else "reference"
    check_tla(ROOT, "SealedDeliveryHandoff", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("stale", "stale-data-frontier", ("ExactControl",), expected="ExactControl")
    check("split", "split-control", ("ExactControl",), expected="ExactControl")
    check("missing-extent", "forget-independent-extent", ("KeepsCustody",), expected="KeepsCustody")
    check("settle", "reset-delivery-floor", ("NoReuse",), expected="NoReuse")
    check("settle", "reparent-borrow", ("OriginalCustodian",), expected="OriginalCustodian")
    check("settle", "sealed-source-clears", ("OnlySuccessorClears",), expected="OnlySuccessorClears")
    check("complete", "recontact", progress="Finishes", expected="liveness")

    laws = ("ExactControl", "KeepsCustody", "OriginalCustodian", "OnlySuccessorClears", "NoReuse")
    check("complete", "source-loss-completion", laws, progress="Finishes")
    check("settle", "original-stop-on-successor", laws, progress="StopsAndClears")
    check("missing-extent", "refuse-without-custody", laws, progress="RejectsInvalidCut")
    check("stale", "refuse-stale-data-frontier", laws, progress="RejectsInvalidCut")
    check("split", "refuse-split-control", laws, progress="RejectsInvalidCut")


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
                                        "88-retained-delivery/DeliveryRecovery.lean"))
    source = ROOT / "SealedDeliveryHandoff.lean"
    check_lean_mutation(ROOT, command, source, "split-delivery-control",
                        [("∧ before.delivery = after.delivery",
                          "∧ before.delivery = before.delivery")],
                        "  exact agreed.2.2\n")
    check_lean_theorems(ROOT, command, source, count=13)



if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
