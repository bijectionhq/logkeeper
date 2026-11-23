#!/usr/bin/env python3
"""Check exact recovery coverage across fault domains, voters, and selectors."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ExactClosure", "CurrentMajority", "ExactFamilyAtDecision")


def check(name, laws, *, variant="reference", policy="distributed", topology="independent", expected=None):
    constants = {"Variant": f'"{variant}"', "Policy": f'"{policy}"', "Topology": f'"{topology}"'}
    check_tla(ROOT, "JointProtection", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("skip_tail_inputs", "ExactClosure"),
        ("visible_only", "ExactClosure"),
        ("stale_family", "ExactFamilyAtDecision"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-ignore-voter-domains", ("CurrentMajority",), variant="ignore_voter_domains",
          topology="colocated", expected="CurrentMajority")
    check("distributed", LAWS)
    check("distributed-colocated-candidate", LAWS, topology="colocated")
    check("local", LAWS, policy="local")
    comparison = "NeverCertifyTheDistributedLayout"
    check("witness-certify-distributed-layout", (comparison,), expected=comparison)
    check("local-excludes-distributed-layout", (comparison,), policy="local")
    for name, witness in (
        ("mixed-views-after-reconfiguration-and-loss", "NeverMixedViewsOnSuccessorAfterFault"),
        ("collect-old-tail-and-recover", "NeverCollectOldTailAndRecover"),
    ):
        check(f"witness-{name}", (witness,), expected=witness)


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
        "51-checkpoint-envelope/EnvelopeRecovery.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "53-pool-evacuation/PoolEvacuation.lean",
    ))
    source = ROOT / "JointProtection.lean"
    check_lean_mutation(ROOT, command, source, "omit-tail-attachments",
        (("(needed : attachment command object) : Required attachment view object",
          "(needed : False) : Required attachment view object"),), "exact Required.tailInput")
    check_lean_mutation(ROOT, command, source, "reuse-old-family",
        (("(observed current : Scope Command) (ready : Prop) : Prop :=\n  observed = current ∧ ready",
          "(_observed _current : Scope Command) (ready : Prop) : Prop :=\n  True ∧ ready"),),
        "exact accepted.1")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
