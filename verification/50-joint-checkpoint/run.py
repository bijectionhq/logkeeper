#!/usr/bin/env python3
"""Check bounded joint checkpoint recovery and evidence reclamation."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("EveryBaseCanReplay", "StillOwedHasEvidence", "BorrowsRetainEvidence", "IssuedResultExact")


def check(name, laws, *, policy="certified", variant="reference", scenario="general", expected=None):
    constants = {"Policy": f'"{policy}"', "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law == "Reopens" else "INVARIANT", law) for law in laws)
    check_tla(ROOT, "JointCheckpoint", name, "Fair" if "Reopens" in laws else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("visible_only", "EveryBaseCanReplay"),
        ("drop_result_row", "EveryBaseCanReplay"),
        ("omit_witness", "StillOwedHasEvidence"),
        ("ignore_borrow", "BorrowsRetainEvidence"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-drop-owed-original", ("StillOwedHasEvidence",), policy="original",
          variant="forget_live", expected="StillOwedHasEvidence")
    check("certified-online", (*LAWS, "Reopens"))
    check("certified-offline", (*LAWS, "Reopens"), scenario="offline")
    check("keep-original-offline", (*LAWS, "Reopens"), policy="original", scenario="offline")
    witness = "NeverReissuesAfterTrimAndRestart"
    check("witness-certify-after-trim", (witness,), scenario="offline", expected=witness)
    check("original-excludes-release-before-ack", (witness,), policy="original", scenario="offline")
    witness = "NeverCompactsAcknowledgmentAfterRecovery"
    check("witness-compact-after-ack", (witness,), expected=witness)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "20-registration-recovery/RegistrationRecovery.lean",
        "21-custody-channel-lifecycle/ChannelLifecycle.lean",
        "24-custodian-recovery/CustodianRecovery.lean",
        "26-journal-rotation/JournalRotation.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "28-ordered-application/OrderedApplication.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "39-certified-activation-replay/CopyFence.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "42-recovery-capacity/RecoveryCapacity.lean",
        "44-prepared-capacity/PreparedCapacity.lean",
        "46-funded-source-seal/FundedSeal.lean",
        "47-source-outcomes/SourceOutcomes.lean",
        "48-settlement-composition/SettlementComposition.lean",
        "49-unified-source-history/UnifiedSource.lean",
    ))
    source = ROOT / "JointCheckpoint.lean"
    check_lean_mutation(ROOT, command, source, "only-visible-replay-basis",
        (("  ∀ view, Selectable state view → ¬ state.tail view removed",
          "  ¬ state.tail state.visible removed"),), "exact allowed view selected")
    check_lean_mutation(ROOT, command, source, "drop-borrow-protection",
        (("  NoReplayUse state removed ∧ ¬ state.borrowed removed ∧",
          "  NoReplayUse state removed ∧ True ∧"),), "exact allowed.2.1 borrowed")
    check_lean_mutation(ROOT, command, source, "allow-foreign-claim",
        (("  statement.scope = scope ∧ scope = image.scope ∧ statement.position = image.position ∧",
          "  True ∧ scope = image.scope ∧ statement.position = image.position ∧"),),
        "exact ⟨verified.1, verified.2.1, verified.2.2.1⟩")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
