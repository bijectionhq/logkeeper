#!/usr/bin/env python3
"""Compare version-scoped reference admission with revocable and scanned custody."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("EveryLiveRootComplete", "EveryPinFencesDisposal", "PhysicalVersionsRemain",
        "EveryBorrowFencesDisposal", "ReleaseIsTerminal")


def check(name, checks, *, variant="fenced", expected=None, roots=2):
    constants = {"Variant": f'"{variant}"', "RootCount": roots}
    check_tla(ROOT, "GraphCustody", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
    ))
    source = ROOT / "SharedCustody.lean"
    check_lean_mutation(ROOT, command, source, "missing-manifest-dependency",
        (("(complete : ∀ version, needs root version → store.refs root version = .held)",
          "(complete : ∀ version, needs root version → True)"),),
        "exact allHeld version dep")
    check_lean_mutation(ROOT, command, source, "resurrect-released-reference",
        (("(unused : store.refs root version = .unused)", "(unused : True)"),),
        "have priorUnused")
    check_lean_mutation(ROOT, command, source, "physical-close-with-live-checkpoint",
        (("(effect : Step needs (LogicalRelease view.catalog) view.store store)",
          "(effect : Step needs (fun _ => True) view.store store)"),),
        "physically_live_while_logical_custody_held effect ready")
    check_lean_theorems(ROOT, command, source, count=13)


def main():
    verify_lean()
    for variant, law in (
        ("skip_dependency", "EveryLiveRootComplete"),
        ("release_live_root", "EveryLiveRootComplete"),
        ("stale_scan", "EveryPinFencesDisposal"),
        ("accept_during_disposal", "EveryPinFencesDisposal"),
        ("unfenced_release", "ReleaseIsTerminal"),
        ("ignore_borrow", "EveryBorrowFencesDisposal"),
        ("delete_by_key", "PhysicalVersionsRemain"),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law)
    check("inaccessible-provider", (("PROPERTY", "SettlesWithoutAccess"),),
          variant="permanent_loss", expected="liveness")
    checks = tuple(("INVARIANT", law) for law in LAWS) + (("PROPERTY", "SettlesWithAccess"),)
    for roots in (2, 3):
        check(f"baseline-{roots}", checks, roots=roots)
    for law, roots in (("NeverServesForkAfterParentWithdrawal", 2),
                       ("NeverRejectsAfterEarlyRelease", 2), ("NeverCollectsAfterRehome", 3)):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, roots=roots)


if __name__ == "__main__":
    main()
