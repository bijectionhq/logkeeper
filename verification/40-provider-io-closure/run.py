#!/usr/bin/env python3
"""Check late provider writes, durable erasure, and charge handoff."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("ErasureIsStable", "ErasedBytesDoNotReturn", "NoUnchargedPhysicalWork")
TEMPORAL = {"ErasesAfterClose", "CanReleaseAfterClose", "ReclaimsBothCharges"}


def check(name, laws, *, tickets=2, policy="effect_fence", variant="reference",
          scenario="general", expected=None):
    constants = {"Tickets": tickets, "Policy": f'"{policy}"', "Variant": f'"{variant}"',
                 "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    check_tla(ROOT, "ProviderIOClosure", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law, policy in (
        ("timeout_is_stop", "ErasedBytesDoNotReturn", "drain"),
        ("wrong_receipt", "ErasedBytesDoNotReturn", "drain"),
        ("local_close_is_fence", "ErasedBytesDoNotReturn", "effect_fence"),
        ("check_only_at_admission", "ErasedBytesDoNotReturn", "effect_fence"),
        ("replay_writes_again", "ErasedBytesDoNotReturn", "drain"),
        ("lose_provider_fence", "ErasedBytesDoNotReturn", "effect_fence"),
        ("lose_consumption", "ErasedBytesDoNotReturn", "drain"),
        ("charge_visible_only", "NoUnchargedPhysicalWork", "effect_fence"),
        ("release_before_charge", "NoUnchargedPhysicalWork", "effect_fence"),
        ("lose_custody", "NoUnchargedPhysicalWork", "effect_fence"),
    ):
        check(f"control-{variant}", (law,), policy=policy, variant=variant, expected=law)
    for name, policy, scenario, law in (
        ("control-erasure-during-provider-outage", "effect_fence", "provider_down", "ErasesAfterClose"),
        ("control-erase-first-blocks-target-release", "erase_only", "provider_down", "CanReleaseAfterClose"),
        ("control-transfer-without-capacity", "effect_fence", "provider_down_no_room", "CanReleaseAfterClose"),
        ("control-drain-waits-on-stalled-ticket", "drain", "ticket_stalled", "ErasesAfterClose"),
    ):
        check(name, (law,), policy=policy, scenario=scenario, expected="liveness")
    check("control-erasure-never-reclaims-charge", ("ReclaimsBothCharges",),
          variant="retain_custody_forever", expected="liveness")
    for tickets in (2, 3):
        for policy in ("effect_fence", "drain"):
            check(f"{policy}-{tickets}", (*SAFETY, "ErasesAfterClose", "CanReleaseAfterClose", "ReclaimsBothCharges"),
                  policy=policy, tickets=tickets)
    check("charged-handoff-provider-down", (*SAFETY, "CanReleaseAfterClose"), scenario="provider_down")
    check("keeps-charge-without-room", SAFETY, scenario="provider_down_no_room")
    check("fence-closes-stalled-ticket", (*SAFETY, "ErasesAfterClose", "CanReleaseAfterClose", "ReclaimsBothCharges"),
          scenario="ticket_stalled")
    for law, policy, scenario in (
        ("NeverRejectsPendingAfterErasure", "effect_fence", "general"),
        ("NeverRejectsDuplicateAfterErasure", "drain", "general"),
        ("NeverReleasesWhileProviderCannotStop", "effect_fence", "provider_down"),
        ("NeverFreesBothChargesAfterCustody", "effect_fence", "general"),
    ):
        check(f"witness-{law}", (law,), policy=policy, scenario=scenario, expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "06-generations/Reservation.lean",
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
        "32-configuration-closure/ConfigurationClosure.lean",
        "36-intent-retirement/IntentRetirement.lean",
        "37-obligation-home/ObligationHome.lean",
        "38-activation-composition/ActivationComposition.lean",
        "39-certified-activation-replay/CopyFence.lean",
        "39-certified-activation-replay/CertifiedActivationReplay.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
    ))
    source = ROOT / "ProviderIOClosure.lean"
    check_lean_mutation(ROOT, command, source, "check-only-at-local-admission",
        (("  state.providerClosed = false ∧ state.status ticket = .pending",
          "  True ∧ state.status ticket = .pending"),), "exact permission.1")
    check_lean_mutation(ROOT, command, source, "accept-absence-without-observed-absence",
        (("(drained : ClosureKnown state) (absent : state.present = false)",
          "(drained : ClosureKnown state) (absent : True)"),), "exact ⟨drained.1, absent")
    check_lean_mutation(ROOT, command, source, "charge-omits-preexisting-operations",
        (("  ∀ ticket, state.status ticket ≠ .unused → custody.tracks ticket",
          "  ∀ ticket, state.status ticket ≠ .unused → True"),), "exact covers.2.2 ticket issued")
    bridge = ROOT / "DispositionBridge.lean"
    check_lean_mutation(ROOT, command, bridge, "accept-receipt-for-different-copy",
        (("def Scoped (expected : CopyFence.Receipt) (packet : Receipt Ticket) : Prop :=\n"
          "  packet.copy = expected",
          "def Scoped (_expected : CopyFence.Receipt) (_packet : Receipt Ticket) : Prop := True"),),
        "exact matchesCopy")
    check_lean_theorems(ROOT, command, source, count=13)
    check_lean_theorems(ROOT, command, bridge, count=3)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
