#!/usr/bin/env python3
"""Check exact issuance and delivery of a chosen read marker's applied outcome."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", scenario="live", progress=False, expected=None):
    properties = [("INVARIANT", law) for law in laws]
    if progress:
        properties.append(("PROPERTY", "CompletesAfterSourceLoss"))
    check_tla(ROOT, "AppliedBarrierReceipt", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, properties, expected=expected)


def verify_tla():
    check("sign-before-apply", ("OnlyAppliedSuccessIssues",), variant="sign-before-apply",
          expected="OnlyAppliedSuccessIssues")
    check("sign-refusal", ("OnlyAppliedSuccessIssues",), variant="sign-refusal",
          scenario="retired", expected="OnlyAppliedSuccessIssues")
    check("sign-head", ("IssuedOriginalResult",), variant="sign-head", expected="IssuedOriginalResult")
    for variant in ("omit-cut", "omit-position"):
        check(variant, ("DeliveryIsExact",), variant=variant, expected="DeliveryIsExact")
    check("omit-scope", ("DeliveryIsExact",), variant="omit-scope", scenario="foreign",
          expected="DeliveryIsExact")
    check("need-live-signer", (), variant="need-live-signer", progress=True, expected="liveness")
    laws = ("OnlyAppliedSuccessIssues", "IssuedOriginalResult", "DeliveryIsExact", "RetiredNeverServes")
    check("successful-offline-delivery", laws, progress=True)
    check("ordered-before-retirement", laws, scenario="overlap", progress=True)
    check("no-result-at-retired-marker", laws, scenario="retired")
    check("foreign-attestation", laws, scenario="foreign")


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean"))
    check_lean_theorems(ROOT, command, ROOT / "AppliedBarrierReceipt.lean", count=9)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
