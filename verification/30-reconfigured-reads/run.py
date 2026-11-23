#!/usr/bin/env python3
"""Check scoped quorums and the lifetime of read reservations across reconfiguration."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("OneExactQuorum", "CannotOpenAfterRetirementOfScope", "RoundCoversInvocation",
        "ExactBasisProtected", "ReturnedCutInInvocation")


def check(name, laws, *, transition="joint", read_mode="dual", variant="carry",
          expected=None, bound=1, scenario="general"):
    constants = {"Transition": f'"{transition}"', "ReadMode": f'"{read_mode}"',
                 "Variant": f'"{variant}"', "MaxHead": bound, "Scenario": f'"{scenario}"'}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "ReconfiguredReads", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "28-ordered-application/OrderedApplication.lean",
        "29-read-index/ReadIndexProof.lean",
    ))
    source = ROOT / "ReconfiguredReads.lean"
    check_lean_mutation(ROOT, command, source, "fence-only-successor",
        (("def FencesBoth (old new : List Replica) (fenced : Replica → Bool) : Prop :=\n"
          "  Majority old fenced ∧ Majority new fenced",
          "def FencesBoth (_old new : List Replica) (fenced : Replica → Bool) : Prop :=\n"
          "  True ∧ Majority new fenced"),), "exact closed.1")
    check_lean_mutation(ROOT, command, source, "reserve-behind-observed-cut",
        (("def ReachesFloor (floor : Nat) (certified : List Value) : Prop :=\n"
          "  floor ≤ certified.length",
          "def ReachesFloor (_floor : Nat) (_certified : List Value) : Prop := True"),),
        "exact reserved.coversObserved")
    check_lean_mutation(ROOT, command, source, "reserve-for-wrong-invocation",
        (("def BindsInvocation (call : Invocation) (round : Round Replica Value) : Prop :=\n"
          "  round.invocation = call.nonce",
          "def BindsInvocation (_call : Invocation) (_round : Round Replica Value) : Prop := True"),
         ("⟨evidence.invocation, (ReadIndexProof.successful_round_follows_invocation evidence).1,",
          "⟨True.intro, (ReadIndexProof.successful_round_follows_invocation evidence).1,"),
         ("⟨evidence.invocation.symm, evidence.fresh,", "⟨True.intro, evidence.fresh,")),
        "exact floor.invocation")
    check_lean_theorems(ROOT, command, source, count=11)


def main():
    verify_lean()
    for variant, law, read_mode in (
        ("mix_scopes", "OneExactQuorum", "dual"),
        ("fence_new_only", "CannotOpenAfterRetirementOfScope", "one_side"),
        ("fence_new_only", "RoundCoversInvocation", "one_side"),
        ("fence_new_only", "ReturnedCutInInvocation", "one_side"),
        ("ignore_observed_floor", "ReturnedCutInInvocation", "dual"),
        ("forget_hold", "ExactBasisProtected", "dual"),
        ("collect_pinned_root", "ExactBasisProtected", "dual"),
    ):
        check(f"control-{variant}-{law}", (law,), variant=variant, expected=law, read_mode=read_mode)
    for transition, read_mode in (("joint", "dual"), ("joint", "one_side"),
                                  ("joint", "successor"), ("sealed", "dual")):
        check(f"{transition}-{read_mode}-1", LAWS, transition=transition, read_mode=read_mode)
    check("joint-dual-two-records", LAWS, bound=2, scenario="two_records")
    witness = "NeverUsesEarlierRoundAtLaterRoot"
    for variant in ("current_scope_only", "fixed_cut"):
        check(variant, (*LAWS, witness), variant=variant)
    for law in (witness, "NeverServesPinnedAcrossAdoption", "NeverRetriesDiscardedFloor"):
        check(f"witness-{law}", (law,), expected=law)
    for transition in ("joint", "sealed"):
        check(f"witness-prefinished-{transition}", (witness,), expected=witness,
              transition=transition, scenario="prefinished_round")
    law = "NeverServesWithOnlyOneJointSide"
    check("witness-one-side-joint", (law,), read_mode="one_side", expected=law)
    check("witness-successor-side-joint", (law,), read_mode="successor", expected=law)


if __name__ == "__main__":
    main()
