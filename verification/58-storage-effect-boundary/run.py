#!/usr/bin/env python3
"""Check atomic provider effects, reuse, and independent staged-byte custody."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ExactBody", "NoWriteAfterFence", "RetiredHasNoBody", "AllWorkCharged", "WithinBudget")


def check(name, laws, *, scopes=2, capacity=2, stage=False, versions=False,
          variant="reference", expected=None):
    constants = {"MaxScope": scopes, "Capacity": capacity, "Variant": f'"{variant}"',
                 "IncludeStage": str(stage).upper(), "KeepVersions": str(versions).upper()}
    check_tla(ROOT, "StorageBoundary", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("checked_then_raw", "NoWriteAfterFence"),
        ("absent_grants_creation", "RetiredHasNoBody"),
        ("content_tag_alias", "ExactBody"),
        ("forget_fence", "NoWriteAfterFence"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-ignore-stage", ("AllWorkCharged",), stage=True,
          variant="ignore_stage", expected="AllWorkCharged")
    check("control-ignore-prior-version", ("AllWorkCharged",), versions=True,
          variant="ignore_prior_version", expected="AllWorkCharged")
    check("atomic-slot", LAWS)
    check("atomic-slot-with-staging", LAWS, stage=True)
    check("three-allocations-two-charges", LAWS, scopes=3, capacity=2, stage=True, versions=True)
    reuse = "NeverReclaimAndReuse"
    check("witness-reclaim-and-reuse", (reuse,), capacity=1, stage=True, expected=reuse)
    staged = "NeverReuseWithOldStaging"
    check("witness-reuse-after-stage-lands-late", (staged,), stage=True,
          variant="stage_after_clear", expected=staged)
    retained = "NeverReuseWithOldVersion"
    check("witness-reuse-with-prior-version", (retained,), versions=True, expected=retained)


def verify_lean():
    command = compile_lean_modules(ROOT, ("40-provider-io-closure/ProviderIOClosure.lean",))
    source = ROOT / "StorageBoundary.lean"
    check_lean_mutation(ROOT, command, source, "ignore-the-permission-serial",
        (("if permit.location = slot.location ∧ permit.serial = slot.issued ∧ slot.body.armedNow = true then",
          "if permit.location = slot.location ∧ slot.body.armedNow = true then"),),
        "exact ⟨eligible, rfl⟩")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
