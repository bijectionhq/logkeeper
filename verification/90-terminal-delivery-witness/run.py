#!/usr/bin/env python3
"""Check exact terminal witnesses in a sealed handoff."""

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
    case = f"{name}-{scenario}" if expected else name
    check_tla(ROOT, "TerminalDeliveryWitness", case, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    terminal_progress = "FinishesWithoutOldRoutes"
    check("terminal", "require-original-extent", progress=terminal_progress, expected="liveness")
    check("terminal", "recontact-provider", progress=terminal_progress, expected="liveness")
    check("terminal", "erase-at-mount", ("PreservesSealedBook",), expected="PreservesSealedBook")
    check("terminal", "receipt-authorizes-use", ("NoStoppedReply",), expected="NoStoppedReply")
    check("volatile", "volatile-is-durable", ("Reopens",), expected="Reopens")
    for scenario in ("stale-slot", "other-pool", "other-lineage"):
        check(scenario, "slot-only", ("Justified",), expected="Justified")
    for scenario in ("shared-read", "shared-replay", "shared-delivery"):
        check(scenario, "ignore-other-owner", ("ProtectsOtherOwners",), expected="ProtectsOtherOwners")

    check("uncovered-old-base", "visible-only-reclaim", ("KeepsSelectableBasis",), expected="KeepsSelectableBasis")

    laws = ("Justified", "ProtectsOtherOwners", "PreservesSealedBook", "NoStoppedReply", "Reopens", "SettlesExactly", "KeepsSelectableBasis")
    check("terminal", "exact-durable-stop", laws, progress=terminal_progress)
    check("live", "unaffected-live-delivery", laws, progress="RecoversLiveAndReplies")
    check("stopped-with-media", "present-extent-does-not-reopen-stop", laws, progress="StopsWithMedia")
    check("uncovered-old-base", "keep-older-basis", laws)
    check("covered-old-base", "receipt-covers-older-basis", laws)
    for scenario in ("no-proof", "volatile", "stale-slot", "other-pool", "other-lineage",
                     "shared-read", "shared-replay", "shared-delivery"):
        check(scenario, f"refuse-{scenario}", laws)


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
                                        "89-sealed-delivery-handoff/SealedDeliveryHandoff.lean"))
    source = ROOT / "TerminalDeliveryWitness.lean"
    check_lean_mutation(ROOT, command, source, "drop-base-need",
                        [("\n    ¬ store.baseNeeds object ∧\n", "\n    True ∧\n")],
                        "  exact replacement.2.1 necessary")
    check_lean_theorems(ROOT, command, source, count=13)



if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
