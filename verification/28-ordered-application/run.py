#!/usr/bin/env python3
"""Check the application and read boundary after group choice."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("AppliedMatchesReference", "FencedWriterCannotAppend",
        "ReplyHasExactAppliedAppend", "ReplyNeverConfirmsRefusedCommand",
        "ReadUsesItsOrderedMarker", "ReadIncludesPreexistingCommits")


def check(name, laws, *, variant="ordered", expected=None, bound=2):
    constants = {"Variant": f'"{variant}"', "MaxCommands": bound}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "OrderedApplication", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
    ))
    source = ROOT / "OrderedApplication.lean"
    check_lean_mutation(ROOT, command, source, "append-without-current-writer",
        (("  state.authority = .active writer ∧\n  lsn = state.history.length ∧",
          "  True ∧\n  lsn = state.history.length ∧"),
         ("(state : State Payload) (writer : Writer) (lsn : Nat) : Prop :=",
          "(state : State Payload) (_writer : Writer) (lsn : Nat) : Prop :="),
         ("⟨admitted.authorized, admitted.ordered, admitted.recoveryRoom, admitted.retainedRoom⟩",
          "⟨True.intro, admitted.ordered, admitted.recoveryRoom, admitted.retainedRoom⟩")),
        "exact allowed.1")
    check_lean_mutation(ROOT, command, source, "append-without-exact-position",
        (("  lsn = state.history.length ∧", "  True ∧"),
         ("(state : State Payload) (writer : Writer) (lsn : Nat) : Prop :=",
          "(state : State Payload) (writer : Writer) (_lsn : Nat) : Prop :="),
         ("⟨admitted.authorized, admitted.ordered, admitted.recoveryRoom, admitted.retainedRoom⟩",
          "⟨admitted.authorized, True.intro, admitted.recoveryRoom, admitted.retainedRoom⟩")),
        "exact allowed.2.1")
    check_lean_mutation(ROOT, command, source, "read-reply-bound-to-another-nonce",
        (("| some cut => .readCut nonce cut", "| some cut => .readCut (nonce + 1) cut"),),
        "exact ⟨rfl, barrier_reports_committed_end known⟩")
    check_lean_theorems(ROOT, command, source, count=15)


def main():
    verify_lean()
    for variant, law in (
        ("reply_on_choice", "ReplyHasExactAppliedAppend"),
        ("reply_on_choice", "ReplyNeverConfirmsRefusedCommand"),
        ("check_on_submit", "AppliedMatchesReference"),
        ("check_on_submit", "FencedWriterCannotAppend"),
        ("ignore_lsn", "AppliedMatchesReference"),
        ("replay_old_marker", "ReadUsesItsOrderedMarker"),
        ("replay_old_marker", "ReadIncludesPreexistingCommits"),
        ("read_lagging_replica", "ReadIncludesPreexistingCommits"),
    ):
        check(f"control-{variant}-{law}", (law,), variant=variant, expected=law)
    for bound in (2, 3):
        check(f"ordered-{bound}", LAWS, bound=bound)
    for law in ("NeverChoosesThenRefusesStaleAppend", "NeverDeliversOriginalReadAfterLaterAppend",
                "NeverDeliversOldAppendAfterRetire"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
