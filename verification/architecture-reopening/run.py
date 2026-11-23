#!/usr/bin/env python3
"""Compare physical admission boundaries under the same finite histories."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla


def check(name, ownership, schedule, *, invariants=(), progress=(), weakening="none", expected=None):
    constants = {
        "Ownership": f'"{ownership}"',
        "Schedule": f'"{schedule}"',
        "Weakening": f'"{weakening}"',
    }
    checks = [("INVARIANT", law) for law in ("PointwiseCapacity", "ExactInstall", *invariants)]
    checks.extend(("PROPERTY", law) for law in progress)
    check_tla(ROOT, "CapacityOwnership", name, "Spec", constants, checks, expected=expected)


def check_writer(name, ownership, witness_up, *, weakening="none", progress=False, expected=None):
    constants = {
        "Ownership": f'"{ownership}"',
        "WitnessUp": "TRUE" if witness_up else "FALSE",
        "Weakening": f'"{weakening}"',
    }
    checks = [("INVARIANT", "ExactResult")]
    if progress:
        checks.append(("PROPERTY", "Service"))
    check_tla(ROOT, "WriterOwnership", name, "Spec", constants, checks, expected=expected)


def verify():
    for owner in ("local", "vector"):
        check(f"{owner}-ignore-pin", owner, "pin-holds",
              weakening="ignore-pin", expected="PointwiseCapacity")
        check(f"{owner}-activate-from-holds", owner, "lost-before-certificate",
              weakening="use-holds", expected="ExactInstall")
        check(f"{owner}-recontact-after-certificate", owner, "lost-after-certificate",
              progress=("OutEventuallyActive",), weakening="recontact", expected="liveness")

    for owner in ("local", "vector"):
        check(f"{owner}-release", owner, "pin-releases", progress=("BothEventuallyActive",))
        check(f"{owner}-pinned", owner, "pin-holds", invariants=("CannotActivateBothWhilePinned",),
              progress=("SomeEventuallyActive",))
        check(f"{owner}-lost-before-evidence", owner, "lost-before-certificate",
              invariants=("CannotActivateOut",))
        check(f"{owner}-lost-after-evidence", owner, "lost-after-certificate",
              progress=("OutEventuallyActive",))
    check("local-coordinator-lost-first", "local", "coordinator-lost-first",
          progress=("SomeEventuallyActive",))
    check("vector-coordinator-lost-first", "vector", "coordinator-lost-first",
          progress=("SomeEventuallyActive",), expected="liveness")

    for owner in ("group", "witness"):
        check_writer(f"{owner}-stage-is-choice", owner, True,
                     weakening="stage-is-choice", expected="ExactResult")
    check_writer("group-witness-present", "group", True, progress=True)
    check_writer("witness-present", "witness", True, progress=True)
    check_writer("group-witness-isolated", "group", False, progress=True)
    check_writer("witness-isolated", "witness", False, progress=True, expected="liveness")


def verify_read_identities():
    def run(name, width, mode, scenario, progress=None, expected=None):
        constants = {"Width": width, "Mode": f'"{mode}"', "Scenario": f'"{scenario}"'}
        laws = ("ExactConsumption", "FitsWindow", "NoRepeat", "RefusesBeyondGap")
        checks = [("INVARIANT", law) for law in laws]
        if progress:
            checks.append(("PROPERTY", progress))
        check_tla(ROOT, "ReadIdentityChoices", name, "Fair" if progress else "Spec",
                  constants, checks, expected=expected)

    run("read-maximum-implicitly-discards", 2, "maximum", "gap", expected="ExactConsumption")
    run("read-volatile-window-forgets", 2, "lose-sparse", "gap", expected="ExactConsumption")
    run("read-next-nonce-blocks", 1, "reference", "gap", "LaterCompletes", "liveness")
    run("read-bounded-window-progresses", 2, "reference", "gap", "LaterCompletes")
    run("read-late-first-still-eligible", 2, "reference", "delayed", "BothComplete")
    run("read-gap-blocks-window-edge", 2, "reference", "window-edge", "LaterCompletes")
    run("read-ordered-abandon-unblocks", 1, "reference", "abandon", "AbandonThenProceed")


if __name__ == "__main__":
    if not sys.argv[1:]:
        verify()
    if not sys.argv[1:] or sys.argv[1:] == ["read-identities"]:
        verify_read_identities()
