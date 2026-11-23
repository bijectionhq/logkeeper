#!/usr/bin/env python3
"""Check replay of exact choices from each selectable funded checkpoint."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(name, law="ExactRecovery", *, cut=3, variant="reference", counterexample=False):
    check_tla(ROOT, "ChosenReplay", name, "Spec", {"MaxCut": cut, "Variant": f'"{variant}"'},
              (("INVARIANT", law),), expected=law if counterexample else None)


def verify_tla():
    for variant in ("position_only", "foreign_lineage", "latest_window", "overrun_cut"):
        check("control-" + variant, variant=variant, counterexample=True)
    check("through-window-install", cut=2)
    check("through-post-install-append")
    check("witness-both-selectors-with-rivals", "NeverRecoverBothWithRivals", counterexample=True)


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
    ))
    source = ROOT / "ChosenReplay.lean"
    check_lean_mutation(ROOT, command, source, "skip-stream-binding",
        (("fun stream request =>\n    frame.lineage.stream = stream ∧", "fun _stream request =>\n    True ∧"),),
        "exact checked")
    check_lean_mutation(ROOT, command, source, "read-beyond-installed-cut",
        (("then some (physical.take chosen.length) else none", "then some physical else none"),),
        "have clipped : physical.take chosen.length = result")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
