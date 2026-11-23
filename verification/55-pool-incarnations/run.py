#!/usr/bin/env python3
"""Check outstanding incarnations, fresh return validation, and exact retirement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "BoundedBook", "AllDebtsRecorded", "FreshValidation", "TerminalClosure", "NoForgottenIssuedScope",
)


def check(name, laws, *, budget=2, scopes=3, epochs=2, variant="reference",
          scenario="general", liveness=False, expected=None):
    constants = {"Budget": budget, "MaxScope": scopes, "MaxEpoch": epochs,
                 "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("INVARIANT", law) for law in laws)
    if liveness:
        checks += (("PROPERTY", "SlotReplenished"),)
    check_tla(ROOT, "PoolIncarnations", name, "FairSettlement" if liveness else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("count_online", "BoundedBook"),
        ("refund_on_fault", "AllDebtsRecorded"),
        ("timeout_forgets", "NoForgottenIssuedScope"),
        ("foreign_scope", "FreshValidation"),
        ("old_probe", "FreshValidation"),
        ("old_book", "FreshValidation"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-settlement-requires-room", (), budget=1, scopes=2, scenario="stable_settlement",
          variant="settlement_needs_room", liveness=True, expected="liveness")
    check("one-slot", LAWS, budget=1, scopes=2)
    check("two-slots", (*LAWS, "NoThirdScopeBeforeDisposition"))
    check("fair-replenishment-at-full", LAWS, budget=1, scopes=2,
          scenario="stable_settlement", liveness=True)
    for name, law in (
        ("fill-with-unsettled-pools", "NeverFillWithUnsettledPools"),
        ("reuse-settled-slot", "NeverReuseSettledSlot"),
    ):
        check(f"witness-{name}", (law,), expected=law)
    reopened = "NeverReopenAtFull"
    check("witness-reopen-at-full", (reopened,), budget=1, scopes=2, expected=reopened)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
    ))
    source = ROOT / "PoolIncarnations.lean"
    check_lean_mutation(ROOT, command, source, "ignore-access-epoch",
        (("proof.epoch = (state.access scope).epoch ∧", "True ∧"),),
        "    accepted.2.2.2.1")
    check_lean_mutation(ROOT, command, source, "discard-charged-namespace",
        (("(terminal : namespaceClosed scope) (clear : Uncharged layout state scope) :\n      Step",
          "(terminal : namespaceClosed scope) (clear : True) :\n      Step"),
         ("(terminal : namespaceClosed scope) (clear : Uncharged layout state scope) :\n    Step",
          "(terminal : namespaceClosed scope) (_clear : Uncharged layout state scope) :\n    Step"),
         (".settle scope enrolled offline terminal clear", ".settle scope enrolled offline terminal trivial")),
        "exact clear used")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
