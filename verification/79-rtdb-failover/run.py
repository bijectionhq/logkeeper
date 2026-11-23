#!/usr/bin/env python3
"""Check the RTDB failover acceptance program on the chosen journal reference."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", coverage="exact", progress=False, expected=None):
    properties = [("INVARIANT", law) for law in laws]
    if progress:
        properties.append(("PROPERTY", "Completes"))
    check_tla(ROOT, "RTDBFailover", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Coverage": f'"{coverage}"'}, properties, expected=expected)


def verify_tla():
    for variant, law in (
        ("prefer-stage", "RecoverExact"),
        ("trust-position", "ReconcileExact"),
        ("accept-old-epoch", "OldEpochFenced"),
        ("ignore-nonce", "InvocationFresh"),
        ("reuse-nonce", "InvocationFresh"),
        ("serve-before-apply", "ReadIsApplied"),
        ("replace-window", "UsesOriginalWindow"),
    ):
        check(variant, (law,), variant=variant, expected=law)
    check("skip-coverage", ("RecoverExact",), variant="skip-coverage", coverage="missing", expected="RecoverExact")
    for variant in ("need-directory", "need-allocator"):
        check(variant, (), variant=variant, progress=True, expected="liveness")

    laws = ("RecoverExact", "ReconcileExact", "OldEpochFenced", "InvocationFresh",
            "ReadIsApplied", "UsesOriginalWindow", "NoServiceWithoutCoverage")
    check("exact-survivors", laws, progress=True)
    check("missing-exact-source", laws, coverage="missing")


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean"))
    check_lean_theorems(ROOT, command, ROOT / "RTDBFailover.lean", count=9)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
