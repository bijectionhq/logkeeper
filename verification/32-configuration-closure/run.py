#!/usr/bin/env python3
"""Check scoped rank recovery and unique successor selection."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("SealCoversUnlearnedChoices", "SealedScopeCannotExtendRecoveredPrefix", "PreservesInheritedBase",
          "ExactInstalledQuorum", "AllChoicesAgree", "CurrentCanRecover")


def closure(name, laws, *, mode="sealed", variant="reference", scopes=2, records=1,
            failed=0, schedule="general", temporal=False, expected=None):
    constants = {"Mode": f'"{mode}"', "Variant": f'"{variant}"', "LastScope": scopes,
                 "Records": records, "FailedZone": failed, "Schedule": f'"{schedule}"'}
    check_tla(ROOT, "Closure", name, "Fair" if temporal else "Spec", constants,
              tuple(("PROPERTY" if temporal else "INVARIANT", law) for law in laws),
              expected=expected)


def successor(name, law, *, authority="ordered", policy="either", failed=0,
              temporal=False, expected=None):
    constants = {"Authority": f'"{authority}"', "Policy": f'"{policy}"', "FailedZone": failed}
    check_tla(ROOT, "Successor", name, "Fair" if temporal else "Spec", constants,
              (("PROPERTY" if temporal else "INVARIANT", law),), expected=expected)


def recovery(name, laws, *, binding="reselect", choice=1, temporal=False, expected=None):
    constants = {"Binding": f'"{binding}"', "PriorChoice": choice}
    check_tla(ROOT, "Recovery", name, "Fair" if temporal else "Spec", constants,
              tuple(("PROPERTY" if temporal else "INVARIANT", law) for law in laws),
              expected=expected)


def verify_tla():
    for variant, law in (
        ("learned_only", "SealCoversUnlearnedChoices"),
        ("learned_only", "AllChoicesAgree"),
        ("sample_only", "SealedScopeCannotExtendRecoveredPrefix"),
        ("volatile_fence", "SealedScopeCannotExtendRecoveredPrefix"),
        ("wrong_membership", "SealCoversUnlearnedChoices"),
        ("install_by_length", "ExactInstalledQuorum"),
        ("drop_inherited_base", "PreservesInheritedBase"),
    ):
        closure(f"control-{variant}-{law}", (law,), variant=variant,
                scopes=3 if variant == "drop_inherited_base" else 2, expected=law)
    successor("control-fence-chooses-successor", "UniqueSuccessor",
              authority="sticky", expected="UniqueSuccessor")
    successor("control-sticky-contention", "EventuallyActivates", authority="sticky",
              policy="successor", temporal=True, expected="liveness")
    recovery("control-immutably-bind-first-cut", ("EventuallyInstalls",), binding="first_cut",
             temporal=True, expected="liveness")
    recovery("control-activate-two-recovered-seeds", ("SeedsAndCommandsAgree",),
             binding="multiple_seeds", expected="SeedsAndCommandsAgree")
    closure("sealed", SAFETY)
    closure("joint", SAFETY, mode="joint", scopes=3, schedule="joint_focused")
    closure("all-voters-fence", (*SAFETY, "NoChoiceAfterFence"), variant="all_voters")
    closure("all-voters-fence-zone-down", ("Finish",), variant="all_voters", failed=1,
            temporal=True, expected="liveness")
    closure("two-sealed-changes", SAFETY, scopes=3, schedule="hidden")
    for failed in (1, 2, 3):
        closure(f"joint-outage-{failed}", SAFETY, mode="joint", scopes=3,
                failed=failed, schedule="hidden")
        closure(f"joint-outage-progress-{failed}", ("Finish",), mode="joint", scopes=3,
                failed=failed, schedule="hidden", temporal=True)
    law = "NeverRecoversHiddenChoice"
    closure("witness-unlearned-commit-and-delayed-receipt", (law,),
            schedule="late_delivery", expected=law)
    law = "NeverCompletesOldQuorumLate"
    closure("witness-quorum-assembles-after-successor-activation", (law,),
            schedule="late_vote", expected=law)
    law = "NeverCarriesAcrossTwoChanges"
    closure("witness-repeated-unacknowledged-inheritance", (law,), scopes=3,
            schedule="hidden", expected=law)
    law = "NeverChoosesInBothJointAndFinal"
    closure("witness-write-during-joint-with-zone-down", (law,), mode="joint",
            scopes=3, records=2, failed=1, schedule="joint_write", expected=law)
    successor("ordered-intent", "UniqueSuccessor")
    successor("one-side-sticky", "UniqueSuccessor", authority="sticky", policy="successor")
    successor("ordered-progress-with-zone-down", "EventuallyActivates", failed=1, temporal=True)
    recovery_safety = ("PreservesPriorChoice", "OneSeed", "ActiveHasSurvivingCopy",
                       "SeedsAndCommandsAgree")
    for choice in (1, 2):
        recovery(f"reselection-preserves-{choice}", recovery_safety, choice=choice)
        recovery(f"reselection-progress-{choice}", ("EventuallyInstalls",), choice=choice,
                 temporal=True)
    law = "NeverRecoversAfterLosingLargerSpeculation"
    recovery("witness-recoverable-prefix-after-lost-speculation", (law,), expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
    ))
    source = ROOT / "ConfigurationClosure.lean"
    check_lean_mutation(ROOT, command, source, "allow-old-scope-after-fence",
        (("def CanOperate (state : VoterState Command) : Prop := state.closedFor = none",
          "def CanOperate (_state : VoterState Command) : Prop := True"),),
        "exact openScope")
    check_lean_mutation(ROOT, command, source, "forget-already-installed-basis",
        (("def EmptyRecovery (basis : List Command) : List Command := basis",
          "def EmptyRecovery (_basis : List Command) : List Command := []"),),
        "have fallback : Recovered before.basis cut = before.basis := by")
    check_lean_mutation(ROOT, command, source, "accept-unbound-successor-copy",
        (("      generation.installed voter generation.basis\n\nstructure Handoff",
          "      ∃ image, generation.installed voter image\n\nstructure Handoff"),),
        "exact exactCopy voter member held")
    check_lean_theorems(ROOT, command, source, count=12)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
