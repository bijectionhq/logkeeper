#!/usr/bin/env python3
"""Check durable receipt selection and reclamation across crash."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(scenario, name, laws=(), *, progress=None, expected=None, specification="Spec"):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    variant = name if expected else "reference"
    case = f"{name}-{scenario}" if expected else name
    check_tla(ROOT, "ReceiptSelectors", case, specification,
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("pending", "bytes-only", ("HasSelectedReceipt",), expected="HasSelectedReceipt")
    check("pending", "foreign-bytes", ("HasSelectedReceipt",), expected="HasSelectedReceipt")
    check("detached", "visible-only", ("ReadySelectors",), expected="ReadySelectors")
    check("detached", "clear-is-reclaim", ("ReadySelectors",), expected="ReadySelectors")
    check("inline", "visible-tail", ("ReadySelectors",), expected="ReadySelectors")
    check("borrowed", "ignore-borrower", ("SafelyBorrowed",), expected="SafelyBorrowed")

    check("detached", "keep-every-receipt", progress="Reclaims", expected="liveness",
          specification="FairWithoutCrash")

    laws = ("ReadySelectors", "SafelyBorrowed", "HasSelectedReceipt", "ReadyToReopen")
    for scenario in ("pending", "detached", "inline", "borrowed"):
        check(scenario, f"crash-{scenario}", laws, progress="Continues", specification="Fair")
    for scenario in ("detached", "inline", "borrowed"):
        check(scenario, f"reclaim-{scenario}", laws, progress="Reclaims", specification="FairWithoutCrash")


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
                                        "89-sealed-delivery-handoff/SealedDeliveryHandoff.lean",
                                        "90-terminal-delivery-witness/TerminalDeliveryWitness.lean"))
    source = ROOT / "SelectorReceipts.lean"
    check_lean_mutation(ROOT, command, source, "receipt-bytes-without-name",
                        [("  media.bytes name = some ticket ∧ media.names name",
                          "  media.bytes name = some ticket ∧ True")],
                        "  exact durable.2")
    check_lean_theorems(ROOT, command, source, count=12)



if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
