#!/usr/bin/env python3
"""Check delayed admission, selective close and multi-reader handoff."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ClosedStaysClosed", "PromisesPreserved", "EveryHoldCovered", "ReservationsTransfer")


def check(name, laws, *, mutation="none", expected=None, bound=2):
    constants = {"Mutation": f'"{mutation}"', "MaxPermit": bound}
    check_tla(ROOT, "Permits", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "14-read-custody/ReadCustody.lean",
    ))
    source = ROOT / "ReplayComposition.lean"
    check_lean_mutation(ROOT, command, source, "wrong-extent-contents",
        (("""first ≤ lsn ∧
    stream.history[lsn]? = some entry ∧ image.bytes = entry.bytes""",
          """first ≤ lsn ∧
    stream.history[lsn]? = some entry ∧ True"""),
         ("(permit : Nat) (image : ReadCustody.Image", "(permit : Nat) (_image : ReadCustody.Image")),
        "exact ⟨lsn, entry, chosen, same⟩")
    check_lean_mutation(ROOT, command, source, "close-with-open-gate",
        (("before.stream.replays permit = .holding first → stream.replays permit = .holding first)",
          "before.stream.replays permit = .holding first → True)"),
         ("(by intro _ _ same; exact same)", "(by intro _ _ _; exact True.intro)")),
        "exact preserves openAfter firstLsn (prior openAfter)")
    check_lean_theorems(ROOT, command, source, count=5)


def main():
    verify_lean()
    for mutation, law in (
        ("trust_old_envelope", "ClosedStaysClosed"),
        ("close_range", "PromisesPreserved"),
        ("check_latest_only", "EveryHoldCovered"),
        ("forget_issued", "ClosedStaysClosed"),
        ("forget_pending", "ReservationsTransfer"),
    ):
        check(f"control-{mutation}", (law,), mutation=mutation, expected=law)
    for bound in (2, 3):
        check(f"baseline-{bound}", LAWS, bound=bound)
    law = "NeverClosesOneAndContinuesAnotherAfterMove"
    check("witness-selective-close", (law,), expected=law)
    law = "NeverRefusesOnePendingAndKeepsAnother"
    check("witness-delayed-closed-permit-refused", (law,), expected=law)


if __name__ == "__main__":
    main()
