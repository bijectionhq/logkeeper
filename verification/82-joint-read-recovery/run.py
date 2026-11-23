#!/usr/bin/env python3
"""Check selected and sealed checkpoint recovery of protected reads."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", scenario="close-before-seal", progress=False, expected=None):
    properties = [("INVARIANT", law) for law in laws]
    if progress:
        properties.append(("PROPERTY", "CompletesFromExactMount"))
    check_tla(ROOT, "JointReadRecovery", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, properties, expected=expected)


def verify_tla():
    for variant in ("data-cut-only", "split-control"):
        check(variant, ("BindsChosenControl",), variant=variant, expected="BindsChosenControl")
    check("reopen-old-slot", ("ClosedDoesNotReopen",), variant="data-cut-only", expected="ClosedDoesNotReopen")
    check("skip-dependencies", ("AdmittedBasisCovered",), variant="skip-dependencies",
          scenario="missing-basis", expected="AdmittedBasisCovered")
    check("old-source-closes", ("ClosedDoesNotReopen",), variant="old-source-closes",
          scenario="close-after-seal", expected="ClosedDoesNotReopen")
    check("reuse-cached-read", ("ClosedDoesNotReopen",), variant="reuse-cached-read",
          scenario="target-close", expected="ClosedDoesNotReopen")
    check("recontact", (), variant="recontact", progress=True, expected="liveness")
    laws = ("BindsChosenControl", "AdmittedBasisCovered", "ClosedDoesNotReopen")
    check("closed-before-seal", laws, progress=True)
    check("after-seal-closure", laws, scenario="close-after-seal", progress=True)
    check("missing-original-basis", laws, scenario="missing-basis")
    check("close-at-installed-target", laws, scenario="target-close")


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean"))
    check_lean_theorems(ROOT, command, ROOT / "JointReadRecovery.lean", count=13)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
