#!/usr/bin/env python3
"""Compare disposal of a withdrawn worker's holds against its still-serving readers."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def disposal(name, policy, laws, *, progress=False, expected=None):
    constants = {"Policy": f'"{policy}"', "Lease": "2", "Drift": "1", "MaxTime": "6"}
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallyTrims"))
    check_tla(ROOT, "WorkerDisposal", name, "Fair" if progress else "Spec", constants, checks,
              expected=expected)


def verify_tla():
    disposal("dispose-on-operator-evidence", "operator-evidence", ["ReadersKeepTheirBytes"],
             expected="ReadersKeepTheirBytes")
    disposal("lease-with-an-unbounded-slow-clock", "unchecked-clock", ["ReadersKeepTheirBytes"],
             expected="ReadersKeepTheirBytes")
    disposal("fence-asynchronously-instead-of-at-each-read", "async-fence", ["ReadersKeepTheirBytes"],
             expected="ReadersKeepTheirBytes")
    disposal("never-dispose-without-evidence", "never", ["ReadersKeepTheirBytes"], progress=True,
             expected="liveness")
    disposal("lease-timed", "lease-timed", ["ReadersKeepTheirBytes"], progress=True)
    disposal("lease-timed-trim-witness", "lease-timed", ["TrimWitness"], expected="TrimWitness")


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "DisposalLease.lean"
    check_lean_mutation(ROOT, command, source, "dispose-at-the-lease-end",
                        [("def MayDispose (leaseEnd drift now : Nat) : Prop := leaseEnd + drift ≤ now",
                          "def MayDispose (leaseEnd drift now : Nat) : Prop := leaseEnd + 0 * drift ≤ now")],
                        "  omega\n\ntheorem without")
    check_lean_theorems(ROOT, command, source, count=2)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
