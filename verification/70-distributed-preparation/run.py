#!/usr/bin/env python3
"""Check a distributed prepare, exact ordered seal, and installed continuation."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("Fits", "LiveReceiptsAreBacked", "FullCommittedVector", "ClosedScopesStayClosed")


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "DistributedPrepare", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    check_tla(ROOT, "DistributedPrepare", "control-unavailable-coordinator", "FairWithoutCoordinatorRecovery",
              {"Variant": '"reference"'}, (("PROPERTY", "Decides"),), expected="liveness")
    for variant, law in (
        ("partial_seal", "FullCommittedVector"),
        ("expire_hold", "LiveReceiptsAreBacked"),
        ("forget_hold", "LiveReceiptsAreBacked"),
        ("forget_fence", "ClosedScopesStayClosed"),
    ):
        check("control-" + variant, (law,), variant=variant, expected=law)
    check("independent-preparations", LAWS)
    check_tla(ROOT, "DistributedPrepare", "fair-decision-and-settlement", "Fair",
              {"Variant": '"reference"'}, tuple(("PROPERTY", law) for law in ("Decides", "Installs", "SettlesAbort")))
    for name, law in (
        ("resume-after-coordinator-loss", "NeverResumeAfterCoordinatorLoss"),
        ("settle-delayed-preparation-after-abort", "NeverClearDelayedPrepareAfterAbort"),
    ):
        check("witness-" + name, (law,), expected=law)


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
        "65-funded-window-move/FundedWindowMove.lean",
        "53-pool-evacuation/PoolEvacuation.lean",
        "54-joint-recovery-protection/JointProtection.lean",
        "66-move-recovery/MoveRecovery.lean",
        "67-full-admission/FullAdmission.lean",
        "68-core-reference/CoreReference.lean",
        "68-core-reference/CorePrograms.lean",
        "69-retained-receipts/ReceiptReplay.lean",
        "69-retained-receipts/MoveProgram.lean",
    ))
    check_lean_theorems(ROOT, command, ROOT / "PrepareLedger.lean", count=6)
    compile_lean_modules(ROOT, ("70-distributed-preparation/PrepareLedger.lean",))
    check_lean_theorems(ROOT, command, ROOT / "ChosenMove.lean", count=4)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
