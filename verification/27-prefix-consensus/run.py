#!/usr/bin/env python3
"""Check fixed-group prefix voting across competing recovery ballots."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("AllChosenPrefixesAgree", "NewBallotReinheritsChosen")


def check(name, laws, *, variant="ranked_prefix", scenario="general", expected=None, ballots=2, depth=1):
    constants = {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"',
                 "MaxBallot": ballots, "MaxDepth": depth}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "PrefixConsensus", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    modules = (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
    )
    command = compile_lean_modules(ROOT, modules)
    agreement = ROOT / "PrefixAgreement.lean"
    rule = "def WinnerDominates (observed winner : Vote Command) : Prop :=\n  RankLE observed winner"
    for weakening, reduced in (
        ("ignore-length", "observed.ballot ≤ winner.ballot"),
        ("ignore-ballot", "observed.history.length ≤ winner.history.length"),
    ):
        check_lean_mutation(ROOT, command, agreement, weakening,
            ((rule, rule.replace("RankLE observed winner", reduced)),), "exact dominates")
    check_lean_theorems(ROOT, command, agreement, count=8)
    command = compile_lean_modules(ROOT, (*modules, "27-prefix-consensus/PrefixAgreement.lean"))
    acceptor = ROOT / "DurableAcceptor.lean"
    check_lean_mutation(ROOT, command, acceptor, "forget-promise-on-restart",
        (("| restart {state} : Step state state",
          "| restart {state} : Step state {state with promised := 0}"),),
        "| restart => exact sound")
    check_lean_theorems(ROOT, command, acceptor, count=5)


def main():
    verify_lean()
    for variant, scenario, ballots, depth in (
        ("length_only", "forked_tail", 3, 2),
        ("ballot_only", "general", 2, 2),
        ("lose_promise", "general", 2, 1),
        ("promote_promise", "general", 2, 1),
    ):
        for law in LAWS:
            check(f"control-{variant}-{law}", (law,), variant=variant, scenario=scenario, expected=law,
                  ballots=ballots, depth=depth)
    check("control-aggregate-votes", ("ReceiptAgreesWithDecisions",), variant="aggregate_votes",
          scenario="mixed_receipt", ballots=4, expected="ReceiptAgreesWithDecisions")
    for ballots, depth in ((2, 1), (2, 2), (3, 1)):
        check(f"ranked-{ballots}-{depth}", LAWS, ballots=ballots, depth=depth)
    check("ranked-forked-tail", LAWS, scenario="forked_tail", ballots=3, depth=2)
    check("ranked-mixed-receipt", (*LAWS, "ReceiptAgreesWithDecisions"),
          scenario="mixed_receipt", ballots=4)
    for law, scenario, ballots, depth in (
        ("NeverFinishesWithLongerDivergentMinority", "forked_tail", 3, 2),
        ("NeverAdoptsMinority", "general", 2, 1),
        ("NeverHasMixedWithoutSameBallot", "general", 2, 1),
        ("NeverCertifiesFinalDecision", "mixed_receipt", 4, 1),
    ):
        check(f"witness-{law}", (law,), scenario=scenario, expected=law, ballots=ballots, depth=depth)


if __name__ == "__main__":
    main()
