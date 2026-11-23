#!/usr/bin/env python3
"""Check intent admission, durable installation results, and physical settlement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("OldHandleStaysClosed", "RetirementHasExactDisposition", "ExactInstall",
          "KeepsUnrecordedOutcome", "TracksPossiblePhysicalCopies", "ServingKeepsCopy",
          "BoundedDebt", "CreditPrecedesSeal")
TEMPORAL = {"RetiresWithEvidence", "SettlesRetiredAbortedCopy", "ReadyInstalls"}


def check(name, laws, *, intents=2, copies=2, receipts=2, policy="detached",
          variant="reference", scenario="general", expected=None):
    constants = {"Intents": intents, "CopyLimit": copies, "ReceiptLimit": receipts,
                 "Policy": f'"{policy}"', "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    check_tla(ROOT, "IntentRetirement", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("forget_issued", "OldHandleStaysClosed"),
        ("guess_terminal", "RetirementHasExactDisposition"),
        ("retire_by_route", "RetirementHasExactDisposition"),
        ("install_by_route", "ExactInstall"),
        ("drop_on_retire", "KeepsUnrecordedOutcome"),
        ("drop_on_move", "KeepsUnrecordedOutcome"),
        ("forget_receipts", "KeepsUnrecordedOutcome"),
        ("send_is_ack", "KeepsUnrecordedOutcome"),
        ("forget_cleanup", "TracksPossiblePhysicalCopies"),
        ("no_missing_fence", "HeldCopyIsTracked"),
        ("late_credit", "CreditPrecedesSeal"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-release-needs-live-intent", ("SettlesRetiredAbortedCopy",),
          variant="needs_gate", expected="liveness")
    check("control-reserve-outcome-after-seal", ("ReadyInstalls",), variant="late_credit",
          scenario="result_link_down", receipts=1, expected="liveness")
    for scenario in ("provider_disconnected", "result_link_down"):
        check(f"control-drain-first-{scenario}", ("RetiresWithEvidence",),
              policy="drain_first", scenario=scenario, expected="liveness")
        check(f"detached-{scenario}", ("RetiresWithEvidence",), scenario=scenario)

    check("detached-small", (*SAFETY, "ReadyInstalls", "SettlesRetiredAbortedCopy"), copies=1, receipts=1)
    check("detached", (*SAFETY, "ReadyInstalls", "SettlesRetiredAbortedCopy"))
    check("single-result-credit-during-outage", (*SAFETY, "RetiresWithEvidence", "ReadyInstalls"),
          receipts=1, scenario="result_link_down")
    check("drain-first", (*SAFETY, "ReadyInstalls"), policy="drain_first")
    check("repeated-handles", SAFETY, intents=3, copies=1, receipts=1)
    for law in ("NeverReusesGateWithOldCleanup", "NeverReconcilesAfterMovingAndReplacing",
                "NeverFencesBeforeDelayedCopy"):
        check(f"witness-{law}", (law,), expected=law)
    recovered = "NeverReconcilesAfterMovingAndReplacing"
    check("witness-new-intent-after-ack", (recovered,), receipts=1, expected=recovered)


def verify_lean():
    command = compile_lean_modules(ROOT, ("06-generations/Reservation.lean",))
    source = ROOT / "IntentRetirement.lean"
    check_lean_mutation(ROOT, command, source, "ack-without-source-record",
        (("def SourceHasRecord (state : Store Image) (id : Nat) (image : Image) : Prop :=\n"
          "  state.recorded id = some image",
          "def SourceHasRecord (_state : Store Image) (_id : Nat) (_image : Image) : Prop := True"),),
        "exact durable")
    gate = "{state with gate := {state.gate with live := none}}"
    check_lean_mutation(ROOT, command, source, "close-discards-outcomes",
        ((gate, "{state with gate := {state.gate with live := none}, outcomes := fun _ => none}"),),
        "exact Eq.refl state.outcomes")
    check_lean_mutation(ROOT, command, source, "close-discards-cleanup",
        ((gate, "{state with gate := {state.gate with live := none}, jobs := fun _ => none}"),),
        "exact Eq.refl state.jobs")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
