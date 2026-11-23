#!/usr/bin/env python3
"""Check exact evidence replay across quorum recovery and custodian release."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("KeepsChosenOutcomes", "ChosenCleanupRequiresOriginalFence",
          "ReleasedPlanCannotRegrow", "PresentBytesRemainCharged",
          "ChosenAckRequiresSourceRecord", "ChosenSuccessHasExactEvidence")


def check(name, laws, *, limit=2, variant="reference", scenario="connected", expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law == "InstallsAfterSeal" else "INVARIANT", law) for law in laws)
    spec = "Fair" if "InstallsAfterSeal" in laws else "Spec"
    check_tla(ROOT, "CertifiedActivationReplay", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("learned_only", "KeepsChosenOutcomes"),
        ("reread_external", "KeepsChosenOutcomes"),
        ("absence_as_fence", "ChosenCleanupRequiresOriginalFence"),
        ("accept_foreign", "ChosenSuccessHasExactEvidence"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-unfenced-copy-regrows", ("ReleasedPlanCannotRegrow",),
          variant="absence_as_fence", expected="ReleasedPlanCannotRegrow")
    check("control-unaccounted-bytes-after-fence", ("PresentBytesRemainCharged",),
          variant="fence_as_disposition", expected="PresentBytesRemainCharged")
    check("control-counterpart-lookup-blocks-recovery", ("InstallsAfterSeal",),
          variant="lookup_required", scenario="disconnected", expected="liveness")
    check("control-offline-as-missing-evidence", ("KeepsChosenOutcomes",),
          variant="unavailable_as_absence", scenario="disconnected", expected="KeepsChosenOutcomes")
    for limit in (2, 3):
        for scenario in ("connected", "disconnected"):
            check(f"certified-{limit}-{scenario}", (*SAFETY, "InstallsAfterSeal"),
                  limit=limit, scenario=scenario)
    for law in ("NeverRecoversHiddenCleanupOffline", "NeverKeepsOldRefusalAfterFactsChange",
                "NeverRejectsQueuedCopyAfterCertifiedCleanup", "NeverTransfersPhysicalCharge"):
        check(f"witness-{law}", (law,), scenario="disconnected", expected=law)


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
    ))
    fence = ROOT / "CopyFence.lean"
    check_lean_mutation(ROOT, command, fence, "receipt-check-ignores-original-binding",
        (("  evidence = original\n", "  evidence.key = original.key\n"),),
        "exact matchesPlan")
    source = ROOT / "CertifiedActivationReplay.lean"
    check_lean_mutation(ROOT, command, source, "accept-source-proof-before-durable-record",
        (("  | some (.source id image) => state.store.recorded id = some image",
          "  | some (.source _ _) => True"),),
        "have recorded : state.store.recorded id = some image := verified")
    check_lean_mutation(ROOT, command, source, "fence-without-physical-accounting",
        (("  physical : disposition.absent (original key image) ∨ disposition.durablyCharged (original key image)",
          "  physical : True"),),
        "exact certificate.physical")
    check_lean_theorems(ROOT, command, fence, count=5)
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
