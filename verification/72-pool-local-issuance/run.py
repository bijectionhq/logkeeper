#!/usr/bin/env python3
"""Check local physical allocation and exact ranked recovery of a joint pool cut."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("Capacity", "AllDecisionsKeepDebits", "AllDecisionsKeepIdentities", "EmptyIssuedPlanStaysFenced")


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "LocalIssuance", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("bare_serial", "AllDecisionsKeepIdentities"),
        ("stale_issued", "AllDecisionsKeepIdentities"),
        ("stale_debits", "AllDecisionsKeepDebits"),
        ("stale_fence", "EmptyIssuedPlanStaysFenced"),
    ):
        check("control-" + variant, (law,), variant=variant, expected=law)
    for variant, expected in (("preset_version", "liveness"), ("reference", None)):
        check_tla(ROOT, "LocalIssuance", "fair-" + variant, "Fair", {"Variant": f'"{variant}"'},
                  (("PROPERTY", "ContinuesAfterReorderedDelivery"),), expected=expected)
    check("pointwise-capacity-and-recovery", LAWS)
    law = "NeverPrepareOutOfOrderAfterTakeover"
    check("witness-reordered-delivery-and-takeover", (law,), expected=law)


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
    local = ROOT / "PoolState.lean"
    check_lean_mutation(ROOT, command, local, "namespace-free-identity",
        (("    (⟨left, serial⟩ : Identity) ≠ ⟨right, serial⟩ :=", "    (⟨left, serial⟩ : Identity).serial ≠ (⟨right, serial⟩ : Identity).serial :="),),
        "  fun same => different (congrArg Identity.pool same)")
    check_lean_theorems(ROOT, command, local, count=12)
    compile_lean_modules(ROOT, ("72-pool-local-issuance/PoolState.lean",))
    check_lean_theorems(ROOT, command, ROOT / "PoolTakeover.lean", count=3)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
