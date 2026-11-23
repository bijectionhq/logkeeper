#!/usr/bin/env python3
"""Check exact source outcome replay, retention and sparse compaction."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("PreservesUnsettled", "IssuedMonotone", "ExactAck", "BoundedRows",
          "ClosedHasNoDebt", "NoInventedResult", "CompactedStaysMissing")
TEMPORAL = {"Installs", "SettledCreditReturns"}


def check(name, laws, *, attempts=2, width=1, policy="sparse", variant="reference",
          scenario="general", expected=None):
    constants = {"Attempts": attempts, "Width": width, "Policy": f'"{policy}"',
                 "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    spec = "Fair" if TEMPORAL.intersection(laws) else "Spec"
    check_tla(ROOT, "SourceOutcomes", name, spec,
              constants, checks, expected=expected)


def verify_tla():
    for variant, law, width in (
        ("learned_only", "PreservesUnsettled", 1),
        ("early_compact", "PreservesUnsettled", 1),
        ("foreign_ack", "ExactAck", 2),
        ("lose_issuance", "IssuedMonotone", 1),
        ("absence_is_abort", "NoInventedResult", 1),
    ):
        check(f"control-{variant}-{law}", (law,), width=width, variant=variant, expected=law)
    check("control-learned-only-undoes-compaction", ("CompactedStaysMissing",),
          variant="learned_only", expected="CompactedStaysMissing")
    check("control-replay-needs-participant", ("Installs",), variant="lookup_required",
          scenario="old_offline", expected="liveness")
    check("prefix-stalls-settled-credit", ("SettledCreditReturns",), policy="prefix",
          attempts=3, width=2, scenario="old_offline", expected="liveness")
    check("sparse-general", (*SAFETY, "Installs", "SettledCreditReturns"))
    check("sparse-outage", (*SAFETY, "Installs", "SettledCreditReturns"), attempts=3, width=2,
          scenario="old_offline")
    check("prefix-outage", (*SAFETY, "Installs"), policy="prefix", attempts=3, width=2,
          scenario="old_offline")
    witness = "NeverCompactsPastAStuckResult"
    check("witness-reuse-outside-prefix", (witness,), attempts=3, width=2,
          scenario="old_offline", expected=witness)
    check("prefix-excludes-reuse", (witness,), attempts=3, width=2, policy="prefix",
          scenario="old_offline")
    witness = "NeverRecoversHiddenResult"
    check("witness-hidden-result", (witness,), scenario="old_offline", expected=witness)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
    ))
    source = ROOT / "SourceOutcomes.lean"
    check_lean_mutation(ROOT, command, source, "ack-matches-only-slot",
        (("  receipt.decision.binding = row.binding ∧\n  row.result =",
          "  True ∧\n  row.result ="),), "exact eligible.1")
    check_lean_mutation(ROOT, command, source, "compact-with-outstanding-debt",
        (("  row.result.isSome ∧ row.waiting = []",
          "  row.result.isSome ∧ True"),), "exact eligible.2")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
