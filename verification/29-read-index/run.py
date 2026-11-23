#!/usr/bin/env python3
"""Check fresh no-marker reads, exact cut coverage, and batch semantics."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("FreshRound", "EarlierFenceBlocksRound", "IncludesPriorChoices",
        "ExactAppliedPrefix", "ExactCutInWindow")


def check(name, laws, *, variant="read_index", expected=None, bound=1):
    constants = {"Variant": f'"{variant}"', "MaxDepth": bound}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "ReadIndex", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "28-ordered-application/OrderedApplication.lean",
    ))
    source = ROOT / "ReadIndexProof.lean"
    check_lean_mutation(ROOT, command, source, "reuse-old-round",
        (("def RoundIsFresh (call : Invocation) (round : Round Replica Command) : Prop :=\n"
          "  call.started ≤ round.opened",
          "def RoundIsFresh (_call : Invocation) (_round : Round Replica Command) : Prop := True"),),
        "exact checked.fresh")
    check_lean_mutation(ROOT, command, source, "accept-fenced-observation",
        (("def EligiblePromise (state : ReplicaState Command) (scope : Scope) : Prop :=\n"
          "  state.promised = scope.ballot",
          "def EligiblePromise (_state : ReplicaState Command) (_scope : Scope) : Prop := True"),),
        "exact eligible")
    check_lean_mutation(ROOT, command, source, "ignore-sampled-maximum",
        (("def Dominates (round : Round Replica Command) (replica : Replica) : Prop :=\n"
          "  (round.observed replica).held.length ≤ round.target.length",
          "def Dominates (_round : Round Replica Command) (_replica : Replica) : Prop := True"),),
        "exact checked.maximum replica belongs answered")
    check_lean_mutation(ROOT, command, source, "apply-by-length-without-prefix",
        (("def AppliesExactTarget (round : Round Replica Command) (applied : List Command) : Prop :=\n"
          "  round.target <+: applied",
          "def AppliesExactTarget (round : Round Replica Command) (applied : List Command) : Prop :=\n"
          "  round.target.length ≤ applied.length"),),
        "exact installed.1")
    check_lean_theorems(ROOT, command, source, count=12)


def main():
    verify_lean()
    for variant, law, bound in (
        ("reuse_old_round", "FreshRound", 1),
        ("reuse_old_round", "IncludesPriorChoices", 1),
        ("ignore_promise", "EarlierFenceBlocksRound", 1),
        ("open_before_coverage", "IncludesPriorChoices", 1),
        ("known_cut_only", "IncludesPriorChoices", 1),
        ("expose_candidate", "ExactAppliedPrefix", 1),
        ("apply_by_position", "ExactAppliedPrefix", 1),
        ("atomic_batch", "ExactCutInWindow", 2),
    ):
        check(f"control-{variant}-{law}", (law,), variant=variant, expected=law, bound=bound)
    for bound in (1, 2):
        check(f"read-index-{bound}", LAWS, bound=bound)
    check("sandwich-2", (*LAWS, "NeverRepliesBeyondStartingAppliedCut"), variant="sandwich", bound=2)
    check("certified-at-least-1", LAWS, variant="certified_at_least")
    check("witness-revalidated-prefix", ("NeverRevalidatesSamePositionWithDifferentBytes",),
          variant="certified_at_least", expected="NeverRevalidatesSamePositionWithDifferentBytes")
    check("witness-physical-batch", ("NeverConfirmsPrecertifiedPhysicalBatch",),
          variant="sandwich", expected="NeverConfirmsPrecertifiedPhysicalBatch", bound=2)
    for law in ("NeverRepliesBeyondStartingAppliedCut", "NeverCoversChoiceAheadOfLearnerAtInvoke",
                "NeverFinishesAfterAbandoningCandidate",
                "NeverServesDuringPartialFence", "NeverDeliversEarlierRoundAfterActivation"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
