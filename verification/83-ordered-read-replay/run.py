#!/usr/bin/env python3
"""Check ranked replay of the protected read book with the journal."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, coverage=True, custody=True, progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "ServesOffline"))
    variant = name if expected else "reference"
    check_tla(ROOT, "OrderedReadReplay", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Coverage": "TRUE" if coverage else "FALSE",
               "Custody": "TRUE" if custody else "FALSE"},
              checks, expected=expected)


def verify_tla():
    check("projection-only", ("FullFrame",), expected="FullFrame")
    check("omit-hold", ("Paired",), expected="Paired")
    check("omit-release", ("NoResurrection",), expected="NoResurrection")
    check("ignore-serial", ("LatestSurvives",), expected="LatestSurvives")
    check("skip-current", ("CurrentCoverage",), custody=False, expected="CurrentCoverage")
    check("recheck-live", (), progress=True, expected="liveness")

    laws = ("FullFrame", "Paired", "NoResurrection", "LatestSurvives", "CurrentCoverage")
    check("full-coverage", laws, progress=True)
    check("uncovered", laws, coverage=False)
    check("missing-current-custody", laws, custody=False)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean"))
    source = ROOT / "OrderedReadReplay.lean"
    check_lean_mutation(ROOT, command, source, "bare-marker",
                        [("| .stream (.read _ _) => False", "| .stream (.read _ _) => True")],
                        "= (advance before, .refused) := by")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
