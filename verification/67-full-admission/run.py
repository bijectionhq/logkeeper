#!/usr/bin/env python3
"""Check exact full admission and the remaining one-AZ fault allowance."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("SafeAdmission", "HealthyRenewalSound")


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "FullAdmission", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def check_stable_outage(name, variant, expected=None):
    check_tla(ROOT, "FullAdmission", name, "StableDegraded", {"Variant": f'"{variant}"'},
              (("PROPERTY", "EventuallyAdmitDegraded"),), expected=expected)


def verify_tla():
    for variant in ("window_only", "visible_only", "ignore_tail", "stale_scope"):
        check("control-" + variant, ("SafeAdmission",), variant=variant, expected="SafeAdmission")
    check("control-early-healthy", ("HealthyRenewalSound",), variant="early_healthy", expected="HealthyRenewalSound")
    check_stable_outage("control-extra-failure-blocks-progress", "reset_fault_allowance", expected="liveness")
    check("one-az-envelope", LAWS)
    law = "NeverAdmitDuringOutage"
    check("witness-fresh-admission-during-outage", (law,), expected=law)
    check("exclude-outage-admission-when-demanding-another-loss", (*LAWS, law), variant="reset_fault_allowance")
    check_stable_outage("stable-eligible-outage-progress", "reference")


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
    ))
    source = ROOT / "FullAdmission.lean"
    check_lean_mutation(ROOT, command, source, "scope-independent-admission",
        (("def ScopeMatches (observed expected : Stamp slots Payload Ticket Zone) : Prop :=\n  observed = expected",
          "def ScopeMatches (_observed _expected : Stamp slots Payload Ticket Zone) : Prop :=\n  True"),),
        "exact approved.1")
    check_lean_mutation(ROOT, command, source, "count-an-extra-failed-zone",
        (("| .degraded actual, scenario => scenario = some actual", "| .degraded _, _ => True"),),
        "change scenario = some failed at allowed")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
