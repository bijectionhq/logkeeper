#!/usr/bin/env python3
"""Check a portable same-placement writer grant and exact funded continuation."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", eligible=True, temporal=False, expected=None):
    constants = {"Variant": f'"{variant}"', "DirectoryUp": "FALSE", "OldWorkerUp": "FALSE",
                 "AllocatorUp": "FALSE", "Eligible": "TRUE" if eligible else "FALSE"}
    check_tla(ROOT, "WorkerHandoff", name, "Fair" if temporal else "Spec", constants,
              tuple(("PROPERTY" if temporal else "INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (("old_epoch", "OldEpochCannotCommit"),
                         ("serve_early", "CatchUpPrecedesServing"),
                         ("skip_nomination", "AuthorizedHolder")):
        check(f"control-{variant}", (law,), variant=variant, eligible=variant != "skip_nomination", expected=law)
    for variant in ("directory", "recipient_needs_release", "migrate"):
        check(f"control-{variant}", ("Serves",), variant=variant, temporal=True, expected="liveness")
    check("exact-grant", ("OldEpochCannotCommit", "CatchUpPrecedesServing", "AuthorizedHolder"))
    check("fair-worker-replacement", ("Serves",), temporal=True)
    law = "NeverServeAfterLastOldCommit"
    check("witness-reuse-under-control-and-pool-outage", (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, ORDERED_SOURCE_MODULES)
    source = ROOT / "StableGrant.lean"
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
