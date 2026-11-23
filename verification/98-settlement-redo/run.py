#!/usr/bin/env python3
"""Compare crash-stable refund publication and reserved redo."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, *, candidate="redo", variant="reference", rounds=3, workspace=3, sync=True,
            invariant=None, progress="EventuallyCycles", expected=None):
    constants = {
        "Rounds": rounds, "Workspace": workspace, "Candidate": f'"{candidate}"',
        "Variant": f'"{variant}"', "SyncAvailable": "TRUE" if sync else "FALSE",
    }
    laws = ("Fits", "VerifiedAbsence", "RecoveredRefunds", "RecoveredCapacity")
    checks = [("INVARIANT", law) for law in ((invariant,) if invariant else laws)]
    if not invariant:
        checks.append(("PROPERTY", progress))
    check_tla(ROOT, "SettlementRedo", name, "Spec" if invariant else "Fair",
              constants, checks, expected=expected)


def verify_tla():
    compare("volatile-selector-credit", candidate="barrier", variant="visible-is-durable",
            workspace=2, invariant="RecoveredCapacity", expected="RecoveredCapacity")
    compare("redo-has-bytes-only", variant="bytes-without-name",
            invariant="RecoveredRefunds", expected="RecoveredRefunds")
    compare("redo-trim-by-visible", variant="reclaim-by-visible",
            invariant="RecoveredRefunds", expected="RecoveredRefunds")
    compare("redo-without-peak-headroom", workspace=2, expected="liveness")
    compare("barrier-waits-for-selector", candidate="barrier", workspace=2, sync=False,
            progress="FirstRefund", expected="liveness")
    compare("barrier-full-cycle", candidate="barrier", workspace=2)
    compare("redo-full-cycle")
    compare("redo-first-refund-without-selector", sync=False, progress="FirstRefund")
    compare("early-spend-covered-by-redo", invariant="NoEarlySpendWithPredecessor",
            expected="NoEarlySpendWithPredecessor")
    compare("redo-crashes-and-reuses", invariant="NoTwoCrashRepeatedReuse",
            expected="NoTwoCrashRepeatedReuse")


def verify_lean():
    pool_path = "72-pool-local-issuance/PoolState.lean"
    modules = ORDERED_SOURCE_MODULES[:ORDERED_SOURCE_MODULES.index(pool_path) + 1]
    command = compile_lean_modules(ROOT, modules)
    source = ROOT / "SettlementRedo.lean"
    check_lean_mutation(ROOT, command, source, "drop-original-serial",
                        [("row.key = original.key ∧ row.serial = original.serial\n\ntheorem",
                          "row.key = original.key ∧ row.serial = row.serial\n\ntheorem")],
                        "  exact matching.2")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
