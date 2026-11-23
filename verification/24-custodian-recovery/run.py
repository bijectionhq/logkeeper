#!/usr/bin/env python3
"""Check custodian recovery, exact refusal state and irreversible provider effects."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ExactImageCovered", "RetiredHandleCannotReopen", "AcknowledgedGrantRemains",
        "AdmittedBorrowRemains", "SettledCannotReacquire", "EffectsHaveCommittedFence",
        "PinnedBytesRemain", "NoStaleConfigurationDecision")


def check(name, checks, *, variant="complete", expected=None, bound=2, observe=False):
    constants = {"Variant": f'"{variant}"', "MaxNonce": bound,
                 "Observe": "TRUE" if observe else "FALSE"}
    check_tla(ROOT, "Recovery", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "20-registration-recovery/RegistrationRecovery.lean",
        "21-custody-channel-lifecycle/ChannelLifecycle.lean",
    ))
    source = ROOT / "CustodianRecovery.lean"
    check_lean_mutation(ROOT, command, source, "new-membership-without-complete-image",
        (("completeNew : JournalRefinement.CompleteCut {before with members := members}",
          "completeNew : True"),),
        "handoff.completeNew")
    check_lean_mutation(ROOT, command, source, "confirm-disposal-without-observed-absence",
        (("(receipt : view.bytes version = false)", "(receipt : True)"),
         ("(closeAllowed := closeAllowed) safeDelivery fence absent",
          "(closeAllowed := closeAllowed) safeDelivery fence True.intro")),
        "exact same.symm ▸ receipt")
    check_lean_mutation(ROOT, command, source, "execute-provider-effect-without-fence",
        (("(sound : SoundMedia view) (permit : permitsDeletion view.image request) : SoundMedia",
          "(sound : SoundMedia view) (permit : True) : SoundMedia"),
         ("exact ⟨permit, authorized_provider_delete_preserves_every_open_version sound permit⟩",
          "exact ⟨permit, authorized_provider_delete_preserves_every_open_version sound True.intro⟩"),
         ("have safeDelivery := authorized_provider_delete_preserves_every_open_version sound permit",
          "have safeDelivery := authorized_provider_delete_preserves_every_open_version (request := request) sound True.intro")),
        "have fenced : view.image.objects.gates request.version")
    check_lean_theorems(ROOT, command, source, count=16)


def main():
    verify_lean()
    for variant, law in (
        ("switch_without_copy", "ExactImageCovered"),
        ("switch_without_fence", "NoStaleConfigurationDecision"),
        ("forget_grant", "AcknowledgedGrantRemains"),
        ("forget_borrow", "AdmittedBorrowRemains"),
        ("forget_borrow", "PinnedBytesRemain"),
        ("forget_issuance", "RetiredHandleCannotReopen"),
        ("forget_spent", "SettledCannotReacquire"),
        ("forget_floor", "SettledCannotReacquire"),
        ("release_absence_without_fence", "SettledCannotReacquire"),
        ("forget_delete_fence", "EffectsHaveCommittedFence"),
        ("early_provider_effect", "EffectsHaveCommittedFence"),
        ("early_provider_effect", "PinnedBytesRemain"),
    ):
        check(f"control-{variant}-{law}", (("INVARIANT", law),), variant=variant, expected=law)
    check("unavailable-provider", (("PROPERTY", "DisposalSettlesWithoutProvider"),),
          variant="permanent_provider_loss", expected="liveness")
    checks = tuple(("INVARIANT", law) for law in LAWS) + (
        ("PROPERTY", "RestartsWithQuorum"), ("PROPERTY", "DisposalSettlesWithAccess"),
    )
    for bound in (2, 3):
        check(f"baseline-{bound}", checks, bound=bound)
    for law in ("NeverRefusesAfterRecovery", "NeverSettlesPreCrashDisposal", "NeverRecoversLivePinAfterReplacement"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True)


if __name__ == "__main__":
    main()
