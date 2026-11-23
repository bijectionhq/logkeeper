#!/usr/bin/env python3
"""Check source decisions and attached evidence in one ranked command history."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, limit=5, variant="reference", expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"'}
    checks = tuple(("PROPERTY" if law == "Installs" else "INVARIANT", law) for law in laws)
    check_tla(ROOT, "UnifiedHistory", name, "Fair" if "Installs" in laws else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("learner_only", "InstalledExact"),
        ("reread_effect", "InstalledExact"),
        ("enrich_refusal", "InstalledExact"),
        ("freeze_only", "AuthorityAndBookTogether"),
        ("data_lsn_only", "InstalledExact"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-remote-replay", ("Installs",), variant="remote_required", expected="liveness")
    for limit in (4, 6):
        check(f"unified-{limit}", ("InstalledExact", "AuthorityAndBookTogether", "Installs"), limit=limit)
    for witness in ("NeverRecoversHiddenRetirementAndCompaction", "NeverPreservesHistoricalRefusal"):
        check(f"witness-{witness}", (witness,), expected=witness)


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
        "48-settlement-composition/SettlementComposition.lean",
    ))
    source = ROOT / "UnifiedSource.lean"
    check_lean_mutation(ROOT, command, source, "substitute-unattached-evidence",
        (("(receipt : Receipt width Pool) (attachment : Option Ticket) : Prop :=",
          "(receipt : Receipt width Pool) (_attachment : Option Ticket) : Prop :="),
         ("  ∃ token, attachment = some token ∧ rules.settledReceipt receipt token",
          "  ∃ token, True ∧ rules.settledReceipt receipt token")),
        "exact ⟨token, attached⟩")
    check_lean_mutation(ROOT, command, source, "omit-seal-position",
        (("  proof.anchor.decision = handoff.decision ∧ proof.anchor.position = handoff.position",
          "  proof.anchor.decision = handoff.decision ∧ True"),),
        "exact matched.2")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
