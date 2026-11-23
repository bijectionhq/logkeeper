#!/usr/bin/env python3
"""Check whole namespace provisioning, durable closure, and capacity settlement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ExactGuards", "OnlyPaidWork", "TerminalNoWork", "NoNewArmsAfterSeal", "AllLiveSlotsSeeded")


def check(name, laws, *, scopes=2, width=1, variant="reference", scenario="general",
          fast=True, liveness=False, expected=None):
    constants = {"MaxScope": scopes, "Width": width, "Variant": f'"{variant}"',
                 "Scenario": f'"{scenario}"', "FastEmpty": str(fast).upper()}
    checks = tuple(("INVARIANT", law) for law in laws)
    if liveness:
        checks += (("PROPERTY", "RetirementCompletes"),)
    check_tla(ROOT, "NamespaceClosure", name, "FairClosure" if liveness else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("raw_create", "TerminalNoWork"),
        ("route_only", "ExactGuards"),
        ("observation_only", "TerminalNoWork"),
        ("arm_after_seal", "NoNewArmsAfterSeal"),
        ("ignore_auxiliary", "TerminalNoWork"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-wait-for-create-response", (), scopes=1, scenario="stall_seed",
          variant="wait_for_receipts", liveness=True, expected="liveness")
    check("one-planned-slot", LAWS)
    check("two-planned-slots", LAWS, width=2)
    check("stalled-seed-seal-first", LAWS, scopes=1, scenario="stall_seed", fast=False, liveness=True)
    check("stalled-seed-atomic-empty", LAWS, scopes=1, scenario="stall_seed", liveness=True)
    for name, law in (
        ("reuse-with-delayed-seed", "NeverReuseAfterDelayedSeed"),
        ("drain-created-guard", "NeverAbortAfterDrain"),
    ):
        check(f"witness-{name}", (law,), expected=law)
    funded_child = "NeverHonorFundedChildAfterSeal"
    check("witness-funded-child-after-seal", (funded_child,), variant="late_child", expected=funded_child)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "55-pool-incarnations/PoolIncarnations.lean",
        "58-storage-effect-boundary/StorageBoundary.lean",
    ))
    source = ROOT / "NamespaceClosure.lean"
    check_lean_mutation(ROOT, command, source, "seed-without-exact-root-identity",
        (("if scope = current bank ∧ bank.phase = .provisioning", "if bank.phase = .provisioning"),),
        "exact ⟨allowed, rfl⟩")
    check_lean_mutation(ROOT, command, source, "finish-without-auxiliary-evidence",
        (("(empty : AllMissing bank) (settled : rules.auxiliaryClosed (current bank)) :\n      Step rules bank",
          "(empty : AllMissing bank) (settled : True) :\n      Step rules bank"),
         (".finish live allowed empty settled", ".finish live allowed empty trivial")),
        "exact settled")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
