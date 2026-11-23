#!/usr/bin/env python3
"""Check the shared activation, handoff, and external evidence histories."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("ResultProtected", "SourceRecordIsDurable", "ProviderFenceIsDurable",
          "CompletedTargetWritesSurvive", "UnsettledCopyKeepsOriginalKey",
          "RetiredAdmissionStaysClosed", "IssuedFenceSurvives", "OnlyCurrentRevisionWrites",
          "SafeDiscovery")
TEMPORAL = {"StagedCutInstalls", "ExternalFactsAreApplied"}


def check(name, laws, *, owners=2, variant="reference", expected=None):
    constants = {"Owners": owners, "Variant": f'"{variant}"'}
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    check_tla(ROOT, "ActivationComposition", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("send_discharges", "ResultProtected"),
        ("restore_source", "SourceRecordIsDurable"),
        ("restore_provider", "ProviderFenceIsDurable"),
        ("ack_while_sealed", "CompletedTargetWritesSurvive"),
        ("settle_while_sealed", "CompletedTargetWritesSurvive"),
        ("apply_at_stale_revision", "OnlyCurrentRevisionWrites"),
        ("reset_issuance", "RetiredAdmissionStaysClosed"),
        ("duplicate_reopens", "CompletedTargetWritesSurvive"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-stale-is-terminal", ("ExternalFactsAreApplied",),
          variant="suppress_refresh_after_stale", expected="liveness")
    for owners in (2, 3):
        check(f"composed-{owners}", (*SAFETY, "StagedCutInstalls", "ExternalFactsAreApplied"),
              owners=owners)
        witness = "NeverReconcilesStagedExternalFacts"
        check(f"witness-overlap-{owners}", (witness,), owners=owners, expected=witness)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "06-generations/Reservation.lean",
        "36-intent-retirement/IntentRetirement.lean",
        "37-obligation-home/ObligationHome.lean",
    ))
    source = ROOT / "ActivationComposition.lean"
    check_lean_mutation(ROOT, command, source, "restore-source-from-target-cut",
        (("def restore (cut : TargetCut Image) (recorded : Nat → Option Image) : Store Image :=\n"
          "  ⟨cut.gate, cut.chosen, cut.outcomes, recorded, cut.serving, cut.jobs⟩",
          "def restore (cut : TargetCut Image) (_recorded : Nat → Option Image) : Store Image :=\n"
          "  ⟨cut.gate, cut.chosen, cut.outcomes, (fun _ => none), cut.serving, cut.jobs⟩"),),
        "exact Eq.refl store")
    check_lean_mutation(ROOT, command, source, "accept-write-at-stale-owner",
        (("def CanWrite (state : State Image) (owner : Nat) : Prop :=\n"
          "  owner = state.routing.owner ∧ state.routing.sealed = false",
          "def CanWrite (state : State Image) (_owner : Nat) : Prop :=\n"
          "  True ∧ state.routing.sealed = false"),),
        "exact wrongOwner authority.1")
    check_lean_mutation(ROOT, command, source, "authorize-mutation-after-seal",
        (("  owner = state.routing.owner ∧ state.routing.sealed = false",
          "  owner = state.routing.owner ∧ True"),),
        "have openBook : before.routing.sealed = false := authority.2")
    check_lean_mutation(ROOT, command, source, "let-target-drop-plan-without-fence",
        (("def CopyRemovalsCertified (state : State Image) (after : Store Image) : Prop :=\n"
          "  ∀ key image, state.store.jobs key = some image → after.jobs key ≠ some image → state.fences key image",
          "def CopyRemovalsCertified (_state : State Image) (_after : Store Image) : Prop := True"),),
        "exact certifiedCleanup key image planned changed")
    check_lean_theorems(ROOT, command, source, count=14)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
