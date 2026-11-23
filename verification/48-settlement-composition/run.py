#!/usr/bin/env python3
"""Compose ordered source results with numeric pool and provider obligations."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("PoolBounds", "PhysicalWorkIsCharged", "ReceiptSurvivesRecovery",
        "TargetEvidenceExact", "ForgetKeepsCharge")


def check(name, laws, *, limit=2, variant="reference", scenario="general", expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law == "AbortCanSettle" else "INVARIANT", law) for law in laws)
    spec = "Fair" if "AbortCanSettle" in laws else "Spec"
    check_tla(ROOT, "Settlement", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant in ("target_only", "move_without_cut", "reference"):
        check_tla(ROOT, "InstallBinding", f"install-{variant}", "Spec",
                  {"Variant": f'"{variant}"'}, (("INVARIANT", "ExactInstall"),),
                  expected=None if variant == "reference" else "ExactInstall")
    for variant, law in (
        ("refund_on_abort", "PhysicalWorkIsCharged"),
        ("fence_only", "PhysicalWorkIsCharged"),
        ("wrong_pool", "PhysicalWorkIsCharged"),
        ("lose_debit", "ReceiptSurvivesRecovery"),
        ("target_before_install", "TargetEvidenceExact"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-wait-for-erasure", ("AbortCanSettle",), variant="absence_only",
          scenario="provider_down", expected="liveness")
    check("compared-absence-only", LAWS, variant="absence_only")
    check("composition", (*LAWS, "AbortCanSettle"))
    check("composition-outage", (*LAWS, "AbortCanSettle"), scenario="provider_down")
    check("composition-larger-pool", (*LAWS, "AbortCanSettle"), scenario="provider_down", limit=3)
    for law in ("NeverCompactsWithChargedPendingWrite", "NeverLateEffectAfterCompaction"):
        check(f"witness-{law}", (law,), scenario="provider_down", expected=law)
    witness = "NeverCompactsAnInstalledSealAtCapacity"
    check("witness-compact-installed-seal", (witness,), expected=witness)


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
    ))
    source = ROOT / "SettlementComposition.lean"
    check_lean_mutation(ROOT, command, source, "ignore-physical-location",
        (("(pool : Pool) (required : Nat) : Prop :=\n  ∃ debit,",
          "(_pool : Pool) (required : Nat) : Prop :=\n  ∃ debit,"),
         ("debit.decision = decision ∧ debit.pool = pool ∧ required ≤ debit.bytes\n",
          "debit.decision = decision ∧ True ∧ required ≤ debit.bytes\n")),
        "exact ⟨debit, stored, exactScope, location, enough⟩")
    check_lean_mutation(ROOT, command, source, "install-matches-only-placement",
        (("  attached.decision = decision ∧ attached.history = history\n",
          "  attached.decision.binding.target = decision.binding.target ∧ attached.history = history\n"),),
        "exact ⟨matched.1, matched.2⟩")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
