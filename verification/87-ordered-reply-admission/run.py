#!/usr/bin/env python3
"""Check authority ordering for reissuing previously admitted read results."""

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
    check_tla(ROOT, "ReplyAdmission", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("overlap", "probe-authorizes", ("ExactLiveRow",), expected="ExactLiveRow")
    check("unseen-close", "data-floor", ("CoversOrderedClose",), expected="CoversOrderedClose")
    check("slot-reused", "omit-serial", ("ExactLiveRow",), expected="ExactLiveRow")
    check("unpaid", "ignore-payment", ("PaidBeforeChoice",), expected="PaidBeforeChoice")
    check("stale-position", "ignore-position", ("ExactPosition",), expected="ExactPosition")
    check("sealed", "allow-sealed", ("OnlyInstalledOwner",), expected="OnlyInstalledOwner")

    laws = ("ExactLiveRow", "PaidBeforeChoice", "ExactPosition", "OnlyInstalledOwner", "CoversOrderedClose")
    for scenario in ("overlap", "unseen-close", "slot-reused", "unpaid", "stale-position", "sealed"):
        check(scenario, scenario, laws)
    check("protected", "independent-completion", laws, progress=True)
    check("retired", "retained-after-retirement", laws, progress=True)
    check("reframe", "reframe-paid-borrow", laws, progress=True)


def verify_lean():
    replay = "83-ordered-read-replay/OrderedReadReplay.lean"
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "29-read-index/ReadIndexProof.lean",
                                        "33-activation-slot/ActivationSlot.lean",
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        replay,
                                        "84-read-invocation-floor/InvocationFloorProof.lean",
                                        "85-ranked-named-recovery/RankedNamedRecovery.lean",
                                        "86-atomic-recovery-publication/AtomicPublication.lean"))
    check_lean_mutation(ROOT, command, ROOT.parent / replay, "omit-exact-permit",
                        [("row.serial = delivery.permit.serial ∧ row.reply.invocation = delivery.call",
                          "row.serial = row.serial ∧ row.reply.invocation = delivery.call")],
                        "  exact bound.1\n\ndef PaidDelivery")
    check_lean_theorems(ROOT, command, ROOT / "OrderedReplyAdmission.lean", count=13)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
