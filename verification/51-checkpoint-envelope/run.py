#!/usr/bin/env python3
"""Check exact checkpoint envelopes, canonical bytes and dependency closure."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("CorrectSelection", "ExactComponents", "SelectedEvidenceExists", "AllOpenEvidenceExists")


def check(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "CheckpointEnvelope", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("ignore_lineage", "CorrectSelection"),
        ("frontier_only", "CorrectSelection"),
        ("control_by_frontier", "ExactComponents"),
        ("data_by_frontier", "ExactComponents"),
        ("weak_evidence_binding", "ExactComponents"),
        ("manifest_only", "SelectedEvidenceExists"),
        ("lost_pin", "AllOpenEvidenceExists"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("exact-envelope", LAWS)
    witness = "NeverReusesTheDataRootAtANewCut"
    check("witness-reuse-data", (witness,), expected=witness)


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
        "50-joint-checkpoint/JointCheckpoint.lean",
        "51-checkpoint-envelope/EnvelopeCodec.lean",
    ))
    codec = ROOT / "EnvelopeCodec.lean"
    check_lean_mutation(ROOT, command, codec, "allow-trailing-bytes",
        (("def atEnd (wire : Bytes) : Bool :=\n  wire.isEmpty",
          "def atEnd (_wire : Bytes) : Bool :=\n  true"),), "simpa [atEnd] using finished")
    check_lean_theorems(ROOT, command, codec, count=11)
    recovery = ROOT / "EnvelopeRecovery.lean"
    check_lean_mutation(ROOT, command, recovery, "drop-ordered-position",
        (("  header.position = expected.position ∧ header.prefixCommitment = expected.prefixCommitment ∧",
          "  True ∧ header.prefixCommitment = expected.prefixCommitment ∧"),), "exact checked.2.2.1")
    check_lean_mutation(ROOT, command, recovery, "accept-incomplete-physical-coverage",
        (("def DependencyCoverage (catalog : Catalog width Control Data)",
          "def DependencyCoverage (_catalog : Catalog width Control Data)"),
         ("  (∀ object ∈ contents.dependencies, catalog.retained object)\n",
          "  True\n"),), "exact ⟨decoded, verified.1, verified.2, named, complete.1, complete.2⟩")
    check_lean_theorems(ROOT, command, recovery, count=8)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
