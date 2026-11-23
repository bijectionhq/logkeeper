#!/usr/bin/env python3
"""Check ranked recovery of refunds and the charges that consumed them."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, failed=1, variant="reference", invariant=None, expected=None):
    constants = {
        "Scenario": f'"{scenario}"', "Failed": failed, "Variant": f'"{variant}"',
    }
    laws = ("ExactVotes", "Inherited", "NoDoubleSpend", "EffectUsesChosenDebit", "StagingIsNotAChoice")
    checks = [("INVARIANT", law) for law in ((invariant,) if invariant else laws)]
    if not invariant:
        checks.append(("PROPERTY", "Outcome"))
    check_tla(ROOT, "RankedPoolRefund", name, "Spec" if invariant else "Fair",
              constants, checks, expected=expected)


def verify_tla():
    compare("ignore-hidden-refund", "refund", variant="learned-only", invariant="Inherited", expected="Inherited")
    compare("forget-the-hidden-spend", "spent", variant="refund-only", invariant="NoDoubleSpend",
            expected="NoDoubleSpend")
    compare("reused-historical-receipt", "spent", variant="receipt-is-credit", invariant="NoDoubleSpend",
            expected="NoDoubleSpend")
    compare("wrong-roots-counted", "refund", variant="count-visible-only", invariant="ExactVotes",
            expected="ExactVotes")
    compare("same-length-rival", "refund", variant="compare-length-only", invariant="ExactVotes",
            expected="ExactVotes")
    compare("unselected-stage-funds-effect", "refund", variant="stage-is-credit", invariant="EffectUsesChosenDebit",
            expected="EffectUsesChosenDebit")
    compare("promote-raw-old-staging", "staged", variant="adopt-staging", invariant="StagingIsNotAChoice",
            expected="StagingIsNotAChoice")
    for failed in (1, 2, 3):
        compare(f"refund-az-{failed}-lost", "refund", failed=failed)
        compare(f"spent-az-{failed}-lost", "spent", failed=failed)
    compare("only-unchosen-staging", "staged")
    compare("adopt-reported-minority", "minority", failed=2)


def verify_lean():
    pool_path = "72-pool-local-issuance/PoolState.lean"
    modules = ORDERED_SOURCE_MODULES[:ORDERED_SOURCE_MODULES.index(pool_path) + 1]
    command = compile_lean_modules(ROOT, (*modules, "98-settlement-redo/SettlementRedo.lean"))
    source = ROOT / "RankedPoolRefund.lean"
    check_lean_mutation(ROOT, command, source, "accept-equal-length",
                        [("  localHistory = installedHistory\n\ntheorem",
                          "  localHistory.length = installedHistory.length\n\ntheorem")],
                        "  exact verified")
    check_lean_theorems(ROOT, command, source, count=6)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
