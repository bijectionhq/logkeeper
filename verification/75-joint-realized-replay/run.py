#!/usr/bin/env python3
"""Check exact ranked replay of the augmented realized source record."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "JointRealized", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    law = "HandoffStillHasItsVector"
    check_tla(ROOT, "HandoffRetention", "control-ack-only", "Spec", {"Variant": '"ack_only"'},
              (("INVARIANT", law),), expected=law)
    check_tla(ROOT, "HandoffRetention", "handoff-retention", "Spec", {"Variant": '"reference"'},
              (("INVARIANT", law),))
    witness = "NeverActivateAndCompactAfterEarlyAcknowledgments"
    check_tla(ROOT, "HandoffRetention", "witness-ack-install-compact", "Spec", {"Variant": '"reference"'},
              (("INVARIANT", witness),), expected=witness)
    for variant, law in (
        ("drop_vector", "NoMutableSealReplay"),
        ("position_only", "NoMutableSealReplay"),
        ("live_route", "NoMutableSealReplay"),
        ("base_only", "ExactRecoveredCut"),
    ):
        check("control-" + variant, (law,), variant=variant, expected=law)
    check("ranked-joint-recovery", ("ExactRecoveredCut", "NoMutableSealReplay"))
    for law in ("NeverReopenBothThroughRouteLoss", "NeverReopenBothWithReclaimedPrefix"):
        check("witness-" + law, (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, ORDERED_SOURCE_MODULES[:-1])
    joint = ROOT / "JointSource.lean"
    check_lean_mutation(ROOT, command, joint, "compact-while-handoff-uses-vector",
        (("      if usesHandoff image key then refuses image else", "      if False then refuses image else"),),
        "  exact ite_eq_left referenced")
    check_lean_theorems(ROOT, command, joint, count=6)
    compile_lean_modules(ROOT, ("75-joint-realized-replay/JointSource.lean",))
    check_lean_theorems(ROOT, command, ROOT / "RankedJointReplay.lean", count=6)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
