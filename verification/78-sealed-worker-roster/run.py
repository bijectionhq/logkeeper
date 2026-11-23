#!/usr/bin/env python3
"""Check the canonical worker roster at the seal and recovery boundaries."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "InstallsOffline"))
    check_tla(ROOT, "RosterTransfer", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"'}, checks, expected=expected)


def verify_tla():
    for variant in ("cut-only", "omit-watermark"):
        check(f"{variant}-mount", ("MountedExact",), variant=variant, expected="MountedExact")
        check(f"{variant}-old-grant", ("NoWithdrawnGrant",), variant=variant, expected="NoWithdrawnGrant")
    check("use-cache", ("ActiveBookMatchesOrExtends",), variant="use-cache",
          expected="ActiveBookMatchesOrExtends")
    check("need-source", (), variant="need-source", progress=True, expected="liveness")
    check("reference", ("MountedExact", "ActiveBookMatchesOrExtends", "NoWithdrawnGrant"), progress=True)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "77-ordered-worker-eligibility/OrderedEligibility.lean"))
    check_lean_theorems(ROOT, command, ROOT / "SealedWorkers.lean", count=9)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
