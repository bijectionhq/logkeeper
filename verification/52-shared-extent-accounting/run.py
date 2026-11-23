#!/usr/bin/env python3
"""Check sharing, exact physical charges, borrows and local capacity."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("PoolBounds", "ExactAllocationsCharged", "OldBorrowsCovered",
        "LiveReferencesCovered", "RefundHasExactAbsence")


def check(name, laws, *, extents=2, limit=2, policy="physical", variant="reference",
          scenario="general", expected=None):
    constants = {"ExtentCount": extents, "Limit": limit, "Policy": f'"{policy}"',
                 "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    check_tla(ROOT, "SharedExtents", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("digest_dedup", "ExactAllocationsCharged"),
        ("refund_on_reference_release", "ExactAllocationsCharged"),
        ("ignore_borrow", "OldBorrowsCovered"),
        ("same_digest_receipt", "RefundHasExactAbsence"),
        ("lose_debits", "ExactAllocationsCharged"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("physical-two", LAWS)
    check("per-reference-two", LAWS, policy="per_reference")
    check("physical-two-pool", LAWS, extents=3)
    check("physical-custodian-unreachable", LAWS, extents=3, scenario="old_unreachable")
    share = "NeverSharesAtFullAndRecovers"
    check("witness-shared-at-capacity", (share,), expected=share)
    check("per-reference-excludes-sharing-at-capacity", (share,), policy="per_reference")
    separate = "NeverChargesSameContentInSeparatePools"
    check("witness-independent-copies", (separate,), extents=3, expected=separate)
    repack = "NeverChargesARepackAlongsideItsOldBorrow"
    check("witness-repack-keeps-old-borrow", (repack,), expected=repack)
    outage = "NeverRetainsDebitDuringOutage"
    check("witness-old-custody-remains-charged", (outage,), extents=3, scenario="old_unreachable",
          expected=outage)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
    ))
    source = ROOT / "SharedExtentAccounting.lean"
    check_lean_mutation(ROOT, command, source, "refund-with-foreign-evidence",
        (("(version evidence : Nat) : Prop :=\n  evidence = version ∧",
          "(_version evidence : Nat) : Prop :=\n  True ∧"),), "exact allowed.1")
    check_lean_mutation(ROOT, command, source, "provider-effect-without-debit",
        (("| providerEvent {state next} (version : Nat) (charged : version ∈ state.debits)",
          "| providerEvent {state next} (version : Nat) (charged : True)"),), "exact charged")
    check_lean_theorems(ROOT, command, source, count=8)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
