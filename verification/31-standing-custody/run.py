#!/usr/bin/env python3
"""Check shared snapshot custody and compare terminal closure policies."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("ExactBorrowProtected", "ChargedCoverage", "FreshLiveCut",
          "OriginalSession", "StoppedWorkCannotFinish", "BoundedCustodyCapacity",
          "OnlyOneOpenGate")


def check(name, laws, *, records=1, windows=2, reads=1, restarts=1, capacity=2,
          variant="reference", policy="fresh_cut", rotation="seal_first", link=True, spec="Spec",
          kind="INVARIANT", expected=None):
    constants = {"MaxRecords": records, "MaxWindows": windows, "MaxReads": reads,
                 "MaxRestarts": restarts, "Capacity": capacity, "Variant": f'"{variant}"',
                 "Policy": f'"{policy}"', "Rotation": f'"{rotation}"',
                 "Link": "TRUE" if link else "FALSE"}
    check_tla(ROOT, "StandingCustody", name, spec, constants,
              tuple((kind, law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("cached_gate", "ExactBorrowProtected"),
        ("omit_suffix", "ExactBorrowProtected"),
        ("forget_restart", "ExactBorrowProtected"),
        ("reuse_after_restart", "OriginalSession"),
        ("stream_lsn_floor", "FreshLiveCut"),
        ("late_success", "StoppedWorkCannotFinish"),
        ("count_open_only", "BoundedCustodyCapacity"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law,
              capacity=1 if variant == "count_open_only" else 2)
    check("control-unprotected-stage", ("ChargedCoverage",), variant="unprotected_stage",
          rotation="stage_first", expected="ChargedCoverage")
    check("control-ignore-staged-gate", ("NoAdmissionAfterTerminal",),
          variant="ignore_staged_gate", rotation="stage_first", policy="before_terminal",
          expected="NoAdmissionAfterTerminal")
    check("fresh-cut", SAFETY)
    check("single-charged-window", SAFETY, capacity=1)
    check("before-terminal", (*SAFETY, "NoAdmissionAfterTerminal"), policy="before_terminal")
    check("sharing", SAFETY, records=0, windows=1, reads=2, capacity=1)
    check("replacement", SAFETY, records=2, restarts=0)
    check("prepared-replacement", SAFETY, rotation="stage_first")
    check("prepared-replacement-hard-closure", (*SAFETY, "NoAdmissionAfterTerminal"),
          rotation="stage_first", policy="before_terminal")
    for law in ("NeverAdmitsOverlapAfterTerminal", "NeverSettlesCrashedBorrow"):
        check(f"witness-{law}", (law,), expected=law)
    law = "NeverDeliversPreterminalFinishAfterRelease"
    check(f"witness-{law}", (law,), expected=law, variant="deliver_after_release")
    law = "NeverServesSuccessorWhileOldCharged"
    check(f"witness-{law}", (law,), expected=law, reads=2)
    check("witness-shared-registration", ("NeverSharesWindow",), expected="NeverSharesWindow",
          records=0, windows=1, reads=2, capacity=1)
    check("witness-old-window-after-checkpoint", ("NeverFinishesAfterReplacement",),
          expected="NeverFinishesAfterReplacement", records=2, restarts=0)
    law = "NeverServesBothCutsWithoutGateGap"
    check("witness-prepared-switch", (law,), restarts=0, rotation="stage_first", reads=2, expected=law)
    check("seal-first-excludes-gapless-switch", (law,),
          restarts=0, reads=2)
    check("hard-closure-link-up", ("TerminalEventually",), spec="FairClose", kind="PROPERTY",
          policy="before_terminal")
    check("hard-closure-link-down", ("TerminalEventually",), spec="FairClose", kind="PROPERTY",
          policy="before_terminal", link=False, expected="liveness")
    check("quorum-closure-link-down", ("TerminalEventually",), spec="FairClose", kind="PROPERTY",
          link=False)
    check("settlement-link-up", ("RightsEventuallySettled",), spec="FairSettle", kind="PROPERTY")
    check("settlement-link-down", ("RightsEventuallySettled",), spec="FairSettle", kind="PROPERTY",
          link=False, expected="liveness")


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "28-ordered-application/OrderedApplication.lean",
        "29-read-index/ReadIndexProof.lean",
        "30-reconfigured-reads/ReconfiguredReads.lean",
    ))
    source = ROOT / "StandingCustody.lean"
    check_lean_mutation(ROOT, command, source, "release-before-drain",
        (("state.phase = .sealed ∧ ∀ id, state.status id ≠ .using",
          "state.phase = .sealed"),), "exact ready.2 id")
    check_lean_mutation(ROOT, command, source, "ignore-exact-dependencies",
        (("def CanReclaim (window : Window Extent) (state : State Reader Extent) (extent : Extent) : Prop :=\n"
          "  state.phase = .released ∨ ¬ window.basis.Needs extent",
          "def CanReclaim (_window : Window Extent) (state : State Reader Extent) (_extent : Extent) : Prop :=\n"
          "  state.phase = .released ∨ True"),), "exact allowed.resolve_left charged")
    check_lean_mutation(ROOT, command, source, "ignore-command-floor",
        (("def CoversFloor (observed : Nat) (applied : List (Command Payload)) : Prop :=\n"
          "  observed ≤ applied.length",
          "def CoversFloor (_observed : Nat) (_applied : List (Command Payload)) : Prop := True"),),
        "exact covers")
    check_lean_mutation(ROOT, command, source, "unbound-physical-snapshot",
        (("def PinsSnapshot (window : Window Extent) (resolve : SnapshotAdmission.Basis → Basis Extent)\n"
          "    (view : SnapshotAdmission.View) : Prop :=\n"
          "  window.basis = resolve (SnapshotAdmission.currentBasis view)",
          "def PinsSnapshot (_window : Window Extent) (_resolve : SnapshotAdmission.Basis → Basis Extent)\n"
          "    (_view : SnapshotAdmission.View) : Prop := True"),), "exact registered")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
