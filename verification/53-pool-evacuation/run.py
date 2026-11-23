#!/usr/bin/env python3
"""Check independently funded repair and original allocation disposition."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "PointwiseBudget", "UnsettledCharged", "ServingExact", "RecoverableAfterFault",
    "AdvertisesExactProtection", "PreservesPlannedEnvelope", "OldBorrowCovered",
)


def check(name, invariants, *, limit=1, scenario="general", variant="reference",
          liveness=False, expected=None):
    constants = {"Limit": limit, "Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    checks = tuple(("INVARIANT", law) for law in invariants)
    if liveness:
        checks += (("PROPERTY", "Repaired"),)
    check_tla(ROOT, "PoolEvacuation", name, "FairSpec" if liveness else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("release_on_failure", "UnsettledCharged"),
        ("unbound_receipt", "ServingExact"),
        ("count_pools", "AdvertisesExactProtection"),
        ("weak_planned_cut", "PreservesPlannedEnvelope"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-use-offline-credit", ("PointwiseBudget",), limit=2, scenario="saturated",
          variant="use_offline_credit", expected="PointwiseBudget")
    check("control-wait-for-old", (), scenario="repair", variant="wait_for_old",
          liveness=True, expected="liveness")
    check("physical-evacuation", LAWS)
    check("physical-evacuation-limit-two", LAWS, limit=2)
    check("fair-repair-during-original-outage", LAWS, scenario="repair", liveness=True)
    check("saturated-replacement-excluded", (*LAWS, "NeverBookSaturatedReplacement"), limit=2,
          scenario="saturated")
    repair = "NeverRepairWithOldBorrow"
    check("witness-repair-keeps-old-borrow", (repair,), scenario="outage_witness", expected=repair)
    for name, law in (("planned-drain-settles", "NeverDisposeAfterWithdrawal"),
                      ("co-located-replacement-remains-degraded", "NeverServeCoLocatedDegraded")):
        check(f"witness-{name}", (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
    ))
    source = ROOT / "PoolEvacuation.lean"
    check_lean_mutation(ROOT, command, source, "foreign-image-joining",
        (("(exact : image version = required)\n      (registered",
          "(exact : True)\n      (registered"),), "exact ⟨exact, registered⟩")
    check_lean_mutation(ROOT, command, source, "unfunded-domain-cut",
        (("(coverage : Protected layout zone (dropPlacement state version))",
          "(coverage : True)"),
         (".withdraw original inPlacement built", ".withdraw original inPlacement trivial")),
        "exact coverage")
    check_lean_theorems(ROOT, command, source, count=8)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
