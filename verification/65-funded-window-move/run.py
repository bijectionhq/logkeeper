#!/usr/bin/env python3
"""Check exact move funding and installation in the shared pool ledger."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("Fits", "SealedHasFullVector", "ExactInstalledWindow", "OldBorrowKeepsBytes", "RecoveredImageDisjoint")


def check(name, laws, *, capacity=2, variant="reference", expected=None):
    check_tla(ROOT, "FundedWindowMove", name, "Spec",
              {"Capacity": capacity, "Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("partial_vector", "SealedHasFullVector"),
        ("foreign_vector", "SealedHasFullVector"),
        ("substitute_window", "ExactInstalledWindow"),
        ("forget_old", "OldBorrowKeepsBytes"),
        ("overwrite_recovery", "RecoveredImageDisjoint"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("two-unit-pools", LAWS)
    check("three-unit-pools", LAWS, capacity=3)
    law = "NoInstallAtCapacity"
    check("witness-install-with-full-pool-and-old-borrow", (law,), expected=law)
    check("exclude-install-when-rebilling", (*LAWS, law), variant="rebill")


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
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "55-pool-incarnations/PoolIncarnations.lean",
        "61-regional-retirement/RegionalRetirement.lean",
        "50-joint-checkpoint/JointCheckpoint.lean",
        "51-checkpoint-envelope/EnvelopeCodec.lean",
        "51-checkpoint-envelope/EnvelopeRecovery.lean",
        "62-funded-appends/FundedAppend.lean",
        "63-staged-votes/StagedVotes.lean",
        "64-chosen-append-recovery/ChosenReplay.lean",
    ))
    source = ROOT / "FundedWindowMove.lean"
    check_lean_mutation(ROOT, command, source, "accept-foreign-capacity",
        (("owners : ∀ version ∈ (rules.plan key).extents, rules.owner version = some key",
          "owners : ∀ version ∈ (rules.plan key).extents, True"),),
        "exact reserved.owners version member")
    check_lean_mutation(ROOT, command, source, "settle-before-terminal-decision",
        (("(terminal : CanSettle state key)", "(terminal : True)"),),
        "exact False.elim (pending (sameKey ▸ terminal))")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
