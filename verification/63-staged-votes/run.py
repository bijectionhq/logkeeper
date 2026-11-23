#!/usr/bin/env python3
"""Check staged vote isolation, exact recovery, and physical headroom."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("HasExactReport", "HasExactPin", "HasPaidWork", "EveryVersionScoped", "OldWriteExcluded")


def check(name, laws, *, capacity=2, limit=2, variant="reference", scenario="ordinary", expected=None):
    check_tla(ROOT, "StagedVotes", name, "Spec", {
        "Capacity": capacity,
        "Limit": limit,
        "Variant": f'"{variant}"',
        "Scenario": f'"{scenario}"',
    }, tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("logical_offset", "HasExactReport"),
        ("skip_bytes", "HasExactReport"),
        ("skip_path", "HasExactReport"),
        ("unpaid_stage", "HasPaidWork"),
        ("late_effect", "EveryVersionScoped"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-drop-pin", ("HasExactPin",), variant="drop_pin", scenario="older_pin",
          expected="HasExactPin")
    check("two-slots", LAWS)
    check("three-slots-with-pin", LAWS, capacity=3, limit=3, scenario="older_pin")
    check("no-replacement-at-one-slot", ("NeverReplace",), capacity=1)
    check("replacement-with-two-slots", ("NeverReplace",), expected="NeverReplace")
    law = "NeverReplaceWhilePinHeld"
    check("pin-blocks-third-stage-at-two-slots", (law,), limit=3, scenario="older_pin")
    check("third-stage-with-pin-at-three-slots", (law,), capacity=3, limit=3, scenario="older_pin", expected=law)
    law = "NeverAcceptAtReusedAddress"
    check("accept-at-new-generation-of-reused-address", (law,), expected=law)


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
    source = ROOT / "StagedVotes.lean"
    check_lean_mutation(ROOT, command, source, "vote-without-durable-bytes",
        (("copy.bytes = true ∧ copy.named = true", "True ∧ copy.named = true"),),
        "have durableBytes : copy.bytes = true := bytes")
    check_lean_mutation(ROOT, command, source, "vote-without-durable-path",
        (("copy.bytes = true ∧ copy.named = true", "copy.bytes = true ∧ True"),),
        "have durablePath : copy.named = true := path")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
