#!/usr/bin/env python3
"""Verify custody issuer handoff without moving physical grant identity."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "EveryPossibleGrantRemainsKnown", "PublishedIsLive", "TerminalDecisionsSurvive",
    "RecordedPlansSurvive", "NoLateSourceDecision", "NoPhysicalRetargeting",
)


def check(name, checks, *, variant="exact", expected=None, old=1, observe=False):
    constants = {"Variant": f'"{variant}"', "OldCount": old, "Observe": "TRUE" if observe else "FALSE"}
    check_tla(ROOT, "Handoff", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "06-generations/Reservation.lean",
        "11-authority-refinement/AuthorityRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "20-registration-recovery/RegistrationRecovery.lean",
        "21-custody-channel-lifecycle/ChannelLifecycle.lean",
    ))
    source = ROOT / "CustodyAuthorityHandoff.lean"
    check_lean_mutation(ROOT, command, source, "settle-without-a-provider-fence",
        (("| .settle binding => fenced command.key binding",
          "| .settle binding => fenced command.key binding ∨ True"),),
        "have exactFence")
    check_lean_mutation(ROOT, command, source, "reopen-a-settled-key",
        (("| .unused, .prepare binding => .prepared binding",
          "| .unused, .prepare binding => .prepared binding\n  | .settled, .prepare binding => .prepared binding"),),
        "cases change <;> exact .inr")
    check_lean_mutation(ROOT, command, source, "reconcile-at-the-issuer-instead-of-the-custodian",
        (("ChannelLifecycle.decideAcquire (custodians key.handle.custodian) key binding",
          "ChannelLifecycle.decideAcquire (custodians key.handle.issuer) key binding"),),
        "(ChannelLifecycle.existing_grant_retries_without_channel_metadata (other := binding) held).1")
    check_lean_theorems(ROOT, command, source, count=15)


def main():
    verify_lean()
    for variant, law in (
        ("observed_only", "EveryPossibleGrantRemainsKnown"),
        ("absence_is_settled", "EveryPossibleGrantRemainsKnown"),
        ("forget_terminal", "TerminalDecisionsSurvive"),
        ("stale_precopy", "RecordedPlansSurvive"),
        ("source_after_seal", "NoLateSourceDecision"),
        ("rebind_old_intent", "NoPhysicalRetargeting"),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law)
    check("control-needs_old_issuer", (("PROPERTY", "StagedEventuallyInstalls"),),
          variant="needs_old_issuer", expected="liveness")
    check("missing-old-provider", (("PROPERTY", "OldCancellationSettlesWithoutAccess"),),
          variant="permanent_old_loss", expected="liveness")
    checks = tuple(("INVARIANT", law) for law in LAWS) + (
        ("PROPERTY", "StagedEventuallyInstalls"), ("PROPERTY", "OldCancellationSettles"),
    )
    for old in (1, 2):
        check(f"baseline-{old}", checks, old=old)
    for law in ("NeverRecoversLateAndSettles", "NeverContinuesWithOldUnavailable",
                "NeverCarriesCancellationAndSettlesOffline"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True)


if __name__ == "__main__":
    main()
