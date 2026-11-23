#!/usr/bin/env python3
"""Check the shared ordered reference, acceptance programs, and guard countermodels."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_theorems, compile_lean_modules


def main():
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
    ))
    check_lean_theorems(ROOT, command, ROOT / "CoreReference.lean", count=4)
    compile_lean_modules(ROOT, ("68-core-reference/CoreReference.lean",))
    check_lean_theorems(ROOT, command, ROOT / "CorePrograms.lean", count=6)
    compile_lean_modules(ROOT, ("68-core-reference/CorePrograms.lean",))
    check_lean_theorems(ROOT, command, ROOT / "Weakening.lean", count=5)


if __name__ == "__main__":
    main()
