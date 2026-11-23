#!/usr/bin/env python3
"""Check late local prepare, durable closure, and exact physical refund."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "CapacityAndPhysicalWork", "AckMeansClosed", "ClosedRefusesLiveGrant",
    "AbortIsFinal", "CompactedWaitsForCustody", "NoNewTicketsAfterFence",
)


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "LatePrepare", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("ignore_floor", "ClosedRefusesLiveGrant"),
        ("forget_fence", "AckMeansClosed"),
        ("ack_before_fence", "AckMeansClosed"),
        ("seal_aborted", "AbortIsFinal"),
        ("refund_after_fence", "CapacityAndPhysicalWork"),
        ("start_after_fence", "NoNewTicketsAfterFence"),
    ):
        check("control-" + variant, (law,), variant=variant, expected=law)
    check("late-plans-through-terminal-compaction", LAWS)
    for law in ("NeverLateSettleAndReuse", "NeverCompactWithPendingWork"):
        check("witness-" + law, (law,), expected=law)


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
    ))
    check_lean_theorems(ROOT, command, ROOT / "LatePrepare.lean", count=10)
    compile_lean_modules(ROOT, ("71-delayed-pool-prepare/LatePrepare.lean",))
    source = ROOT / "AbortCut.lean"
    check_lean_mutation(ROOT, command, source, "ignore-original-physical-key",
        (("  key = plan.key ∧ binding = plan.binding ∧ aborted", "  True ∧ key = key ∧ binding = plan.binding ∧ aborted"),
         ("⟨rfl, rfl, certified⟩", "⟨trivial, rfl, rfl, certified⟩")),
        "  received.1")
    check_lean_theorems(ROOT, command, source, count=3)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
