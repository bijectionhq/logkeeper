#!/usr/bin/env python3
"""Check incarnation decisions and recovery of the exact chosen inventory."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ExactApplied", "NoUnchosenApplication", "NoEarlyReceipt", "ResumeAtChosen")


def check(name, laws, *, limit=2, variant="reference", scenario="general", expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    check_tla(ROOT, "InventoryRecovery", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (("reply_after_one_vote", "NoEarlyReceipt"),
                         ("learned_head", "ResumeAtChosen"),
                         ("accepted_is_chosen", "NoUnchosenApplication")):
        check(f"control-{variant}", (law,), limit=1, variant=variant, expected=law)
    check("control-refresh_evidence", ("ExactApplied",), limit=1, scenario="late_evidence",
          variant="refresh_evidence", expected="ExactApplied")
    check("chosen-and-applied", LAWS)
    check("issuance-three-positions", LAWS, limit=3, scenario="issuance")
    for name, law, bound in (
        ("unlearned-issuance", "NeverRecoveredUnlearned", 1),
        ("older-selector", "NeverOldSelectorWithChosenIssue", 2),
    ):
        check(f"witness-{name}", (law,), limit=bound, expected=law)
    refusal = "NeverAcceptedAgainOnLateEvidence"
    check("witness-historical-refusal", (refusal,), limit=1, scenario="late_evidence", expected=refusal)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "26-journal-rotation/JournalRotation.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "51-checkpoint-envelope/EnvelopeCodec.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "55-pool-incarnations/PoolIncarnations.lean",
        "56-finite-inventory/FiniteCounters.lean",
        "56-finite-inventory/InventoryCodec.lean",
    ))
    source = ROOT / "OrderedInventory.lean"
    check_lean_mutation(ROOT, command, source, "reply-before-application",
        (("position < appliedCut ∧ appliedCut ≤ history.length ∧\n      history[position]? = some request then",
          "True ∧ appliedCut ≤ history.length ∧\n      history[position]? = some request then"),),
        "exact ⟨authorized, sent⟩")
    check_lean_mutation(ROOT, command, source, "reply-without-chosen-evidence",
        (("(ledger : PrefixAgreement.Ledger Voter (Command Book LedgerCommand)) (ballot : Nat)\n    (history",
          "(_ledger : PrefixAgreement.Ledger Voter (Command Book LedgerCommand)) (_ballot : Nat)\n    (history"),
         ("if PrefixAgreement.Chosen ledger ballot history ∧", "if True ∧")),
        "exact ⟨authorized, sent⟩")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
