#!/usr/bin/env python3
"""Check standing credit across checkpoint selection and sealed handoff."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def run(scenario, *, variant="reference", progress=None, invariant=None, expected=None):
    values = {"Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (invariant,) if invariant else (
        "NoDuplicate", "SealedHasNoCurrent", "NewerAfterTransfer", "KeepsOriginalFunding", "EligibleScope", "CursorFits",
    )
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    check_tla(ROOT, "StandingReadRecovery", f"{scenario}-{variant}", "Fair" if progress else "Spec",
              values, checks, expected=expected)


def verify_tla():
    run("cursor-limit", variant="check-issued-id-only", invariant="CursorFits", expected="CursorFits")
    run("stable", variant="reset-empty-book", invariant="NoDuplicate", expected="NoDuplicate")
    run("older-base", variant="ignore-chosen-suffix", invariant="NoDuplicate", expected="NoDuplicate")
    run("sealed", variant="drop-watermark", invariant="NewerAfterTransfer", expected="NewerAfterTransfer")
    run("sealed", variant="carry-old-current", invariant="SealedHasNoCurrent", expected="SealedHasNoCurrent")
    run("sealed", variant="retire-on-install", invariant="KeepsOriginalFunding", expected="KeepsOriginalFunding")
    run("foreign-proof", variant="ignore-proof-placement", invariant="EligibleScope", expected="EligibleScope")
    run("missing-live", variant="historical-proof-authorizes-use", invariant="EligibleScope", expected="EligibleScope")
    run("missing-live", variant="live-required-for-replay", progress="WritesWithoutOptional", expected="liveness")

    for scenario in ("stable", "older-base", "sealed"):
        run(scenario, progress="Completes")
    run("foreign-proof", progress="RejectsForeign")
    run("missing-live", progress="WritesWithoutOptional")
    run("cursor-limit", progress="WritesWithoutOptional")


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
                                        "94-standing-read-credit/StandingReadCredit.lean"))
    source = ROOT / "StandingReadRecovery.lean"
    check_lean_mutation(ROOT, command, source, "skip-placement",
                        [("  samePlacement : placementOf authority = some window.placement",
                          "  samePlacement : True")],
                        "  exact valid.samePlacement")
    check_lean_theorems(ROOT, command, source, count=15)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
