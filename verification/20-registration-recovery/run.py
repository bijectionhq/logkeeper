#!/usr/bin/env python3
"""Check interrupted registration, prefix compaction and issued credit."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("CustodyWasPlanned", "PublishedHasCustody", "ClosedCannotPublish", "ClosedCannotResurrect",
        "FloorDoesNotCrossUnacquiredPlan", "ReceiverCreditBound", "PhysicalPinBound")


def check(name, checks, *, variant="anchored", expected=None, ids=3, window=2, observe=False):
    constants = {"Variant": f'"{variant}"', "MaxId": ids, "Window": window,
                 "PinCapacity": window, "Observe": "TRUE" if observe else "FALSE"}
    check_tla(ROOT, "Registration", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
    ))
    source = ROOT / "RegistrationRecovery.lean"
    check_lean_mutation(ROOT, command, source, "ignore-receiver-floor",
        (("(fresh : table.floor < serial)", "(fresh : True)"),),
        "have beyond")
    check_lean_mutation(ROOT, command, source, "release-without-issuer-close",
        (("(closed : issuer.terminal serial) :", "(closed : True) :"),
         (".release serial (canceled shard serial recorded)",
          ".release serial (by have _ := canceled shard serial recorded; exact True.intro)")),
        "have other : serial ≠ chosen := fun same")
    check_lean_mutation(ROOT, command, source, "credit-before-durable-ack",
        (("(installed : acknowledged ≤ receiverFloor)", "(_installed : True)"),),
        "omega\n\ndef markerIndex")
    check_lean_theorems(ROOT, command, source, count=15)


def main():
    verify_lean()
    for variant, law in (
        ("forget_intent", "CustodyWasPlanned"),
        ("drop_closed_plan_at_floor", "CustodyWasPlanned"),
        ("publish_after_close", "ClosedCannotPublish"),
        ("promise_without_receipt", "FloorDoesNotCrossUnacquiredPlan"),
        ("forget_held", "PublishedHasCustody"),
        ("ignore_floor", "ClosedCannotResurrect"),
        ("early_credit", "ReceiverCreditBound"),
        ("unbounded_window", "ReceiverCreditBound"),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law)
    check("control-unmetered_pins", (("INVARIANT", "PhysicalPinBound"),),
          variant="unmetered_pins", expected="PhysicalPinBound", ids=2, window=1)
    check("control-release_needs_capacity", (("PROPERTY", "ClosedSettles"),),
          variant="release_needs_capacity", expected="liveness", ids=2, window=1)
    check("inaccessible-custodian", (("PROPERTY", "ClosedSettlesWithoutLink"),),
          variant="permanent_loss", expected="liveness", ids=2, window=1)
    checks = tuple(("INVARIANT", law) for law in LAWS) + (("PROPERTY", "ClosedSettles"),)
    for variant in ("anchored", "terminal_only"):
        for ids, window in ((2, 1), (3, 2)):
            check(f"baseline-{variant}-{ids}-{window}", checks, variant=variant, ids=ids, window=window)
    law = "NeverReusesCreditWhileOldRootLive"
    check("terminal-only-blocks-credit", (("INVARIANT", law),), variant="terminal_only")
    for law in (law, "NeverReplaysHeldBelowFloor", "NeverRejectsAfterCompaction",
                "NeverSettlesInterruptedGrant"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True)


if __name__ == "__main__":
    main()
