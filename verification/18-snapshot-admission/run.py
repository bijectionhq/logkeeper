#!/usr/bin/env python3
"""Compare cut-first and atomic recovery admission under checkpoint churn."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("CurrentHasCustody", "CurrentNotDeleting", "ProtectedRoot",
        "ProtectedSuffix", "RetentionBound", "ResponseAtCut")


def check(name, checks, *, variant="atomic", expected=None, head=3, capacity=2):
    constants = {"Variant": f'"{variant}"', "MaxHead": head, "Capacity": capacity}
    check_tla(ROOT, "Admission", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
    ))
    source = ROOT / "SnapshotAdmission.lean"
    check_lean_mutation(ROOT, command, source, "publish-without-live-custody",
        (("(registered : view.custody root = .ready start)", "(registered : True)"),),
        "have backed")
    check_lean_mutation(ROOT, command, source, "dispose-held-root",
        (("(unheld : ∀ id basis, view.snapshots id = some basis → root ≠ basis.root)",
          "(unheld : ∀ id basis, view.snapshots id = some basis → True)"),),
        "have untouched : basis.root ≠ root")
    check_lean_mutation(ROOT, command, source, "trim-borrowed-tail",
        (("(keeps : ∀ id basis, view.snapshots id = some basis → basis.start < basis.stop → floor ≤ basis.start)",
          "(keeps : ∀ id basis, view.snapshots id = some basis → basis.start < basis.stop → True)"),),
        "have retainedTail")
    check_lean_theorems(ROOT, command, source, count=12)


def main():
    verify_lean()
    for variant, law in (
        ("before_custody", "CurrentHasCustody"),
        ("accept_old_receipt", "CurrentNotDeleting"),
        ("split_root_hold", "ProtectedRoot"),
        ("split_wal_hold", "ProtectedSuffix"),
        ("read_live_head", "ResponseAtCut"),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law)
    for variant in ("fixed_then_reserve", "unfair_fetch"):
        check(f"control-{variant}", (("PROPERTY", "CompletesWithStableLink"),),
              variant=variant, expected="liveness", head=2)
    check("fixed-cut-safety-prefix", (("INVARIANT", "NeverOvertaken"),),
          variant="fixed_then_reserve", expected="NeverOvertaken", head=2)
    check("permanent-link-loss", (("PROPERTY", "CompletesWithoutStableLink"),),
          variant="permanent_link_loss", expected="liveness", head=2)
    for head, capacity in ((2, 1), (3, 2)):
        checks = tuple(("INVARIANT", law) for law in LAWS)
        checks += (("PROPERTY", "CompletesWithStableLink"),)
        check(f"baseline-{head}-{capacity}", checks, head=head, capacity=capacity)
    for law in ("NeverServesOldBasisAfterMove", "NeverStallsAtBound", "NeverReclaimsOldBasis",
                "NeverFinishesEmptySuffixAfterTrim"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law)


if __name__ == "__main__":
    main()
