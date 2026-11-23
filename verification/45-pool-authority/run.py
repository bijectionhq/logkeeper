#!/usr/bin/env python3
"""Check exact pool authority transfer and bounded cancellation metadata."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("Bounds", "LimitDoesNotRegress", "ClosedRemainsClosed", "ObservedHoldPreserved", "CommittedPreserved",
        "OldCannotMutate", "InstalledCreditMatches", "CancellationBound")
TEMPORAL = {"SealedOwnerInstalls", "DecisionsReachRows"}


def check(name, laws, *, tickets=3, width=1, variant="reference", expected=None):
    constants = {"Tickets": tickets, "Width": width, "Variant": f'"{variant}"'}
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    check_tla(ROOT, "PoolAuthority", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("ignore_prepared", "Bounds"),
        ("shrink_under_load", "Bounds"),
        ("forget_limit", "LimitDoesNotRegress"),
        ("lose_floor", "ClosedRemainsClosed"),
        ("lose_spent", "ClosedRemainsClosed"),
        ("lose_live", "ObservedHoldPreserved"),
        ("stale_precopy", "ObservedHoldPreserved"),
        ("old_owner_can_act", "OldCannotMutate"),
        ("credit_from_offer", "InstalledCreditMatches"),
        ("retain_markers", "MarkerCountBound"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-needs_old_owner", ("SealedOwnerInstalls",), variant="needs_old_owner", expected="liveness")
    check("pool-temporal", ("SealedOwnerInstalls", "DecisionsReachRows"), tickets=2, width=1)
    for tickets, width in ((3, 1), (3, 2)):
        check(f"pool-{tickets}-{width}", LAWS, tickets=tickets, width=width)
    for law in ("NeverRecoversLiveAndRefusesClosed", "NeverShrinksWithLiveHold"):
        check(f"witness-{law}", (law,), expected=law)


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
    ))
    source = ROOT / "PoolAuthority.lean"
    check_lean_mutation(ROOT, command, source, "serve-without-current-owner",
        (("(localPool : ServingPool) (recipient : Nat)\n",
          "(localPool : ServingPool) (_recipient : Nat)\n"),
         ("  recipient = localPool.owner ∧ key.handle.custodian = localPool.image.pool ∧",
          "  True ∧ key.handle.custodian = localPool.image.pool ∧")), "exact admitted.1")
    check_lean_mutation(ROOT, command, source, "resize-ignores-live-debits",
        (("def ResizeFits (cost : Binding → Nat) (image : Image) (newLimit : Nat) : Prop :=\n"
          "  used cost image ≤ newLimit",
          "def ResizeFits (_cost : Binding → Nat) (image : Image) (newLimit : Nat) : Prop :=\n"
          "  image.ordinary ≤ newLimit"),), "simpa [OrdinaryFits, used, ResizeFits] using admitted")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
