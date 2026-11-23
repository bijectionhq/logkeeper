#!/usr/bin/env python3
"""Check scoped retirement, exact read completion, and regional pool reuse."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("EachBorrowRecorded", "NoNewReadsAfterRetirement", "AllPhysicalWorkCharged",
        "PointwiseBound", "ExactSettledScope")


def check(name, laws, *, limit=2, variant="reference", scenario="ordinary",
          temporal=False, expected=None):
    constants = {"Limit": limit, "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("INVARIANT", law) for law in laws)
    if temporal:
        checks += (("PROPERTY", "RetiredDeploymentSettles"),)
    check_tla(ROOT, "RegionalRetirement", name, "FairSettlement" if temporal else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("finish_by_version", "EachBorrowRecorded"),
        ("use_stale_root", "NoNewReadsAfterRetirement"),
        ("refund_after_stream_close", "AllPhysicalWorkCharged"),
        ("detach_means_erased", "ExactSettledScope"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-wait-for-shared-readers", (), variant="wait_for_shared_readers",
          scenario="survivor_stalls", temporal=True, expected="liveness")
    check("two-read-identities", LAWS)
    check("three-read-identities", LAWS, limit=3)
    check("settle-while-survivor-stalls", LAWS, scenario="survivor_stalls", temporal=True)
    law = "NeverSurvivorUsesReturnedCapacity"
    check("witness-survivor-uses-returned-capacity", (law,), scenario="protected_survivor", expected=law)


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
    ))
    source = ROOT / "RegionalRetirement.lean"
    check_lean_mutation(ROOT, command, source, "admit-borrows-after-retirement",
        (("def CanBorrow (rules", "def CanBorrow (_rules"),
         ("¬ Retired state (rules.owner root) ∧", "True ∧")),
        "exact allowed.1 retired")
    check_lean_mutation(ROOT, command, source, "certify-before-original-disposition",
        (("version ≤ state.pools.ledger.issued ∧ (state.pools.ledger.provider version).erased = true",
          "version ≤ state.pools.ledger.issued ∧ True"),),
        "exact (ready.2.2 version original).2")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
