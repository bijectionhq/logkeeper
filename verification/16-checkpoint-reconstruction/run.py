#!/usr/bin/env python3
"""Check checkpoint certification, fork genesis and captured replay cuts."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "PublishedOwnScope", "PublishedExactHistory", "PublishedReconstructs",
    "ReaderInsulated", "ResponseAtRequestedCut",
)


def check(name, laws, *, mutation="none", expected=None, bound=3):
    constants = {"Mutation": f'"{mutation}"', "MaxLsn": bound}
    check_tla(ROOT, "CheckpointCut", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, ("07-reference/Kernel.lean",))
    source = ROOT / "CheckpointReconstruction.lean"
    check_lean_mutation(ROOT, command, source, "foreign-scope",
        (("scope : image.cut.stream = engine.stream", "scope : True"),
         ("⟨rfl, rfl, Nat.zero_le _, rfl, childCustody, childReads, origin.symm⟩",
          "⟨True.intro, rfl, Nat.zero_le _, rfl, childCustody, childReads, origin.symm⟩")),
        "fun signed => foreign signed.scope")
    check_lean_mutation(ROOT, command, source, "unchecked-replay",
        (("orderedExact : records = (stream.history.take target.next).drop image.cut.next",
          "orderedExact : True"),
         ("⟨live, scope, floor, fromCheckpoint, committed, rfl⟩",
          "⟨live, scope, floor, fromCheckpoint, committed, True.intro⟩")),
        "admitted.orderedExact")
    check_lean_mutation(ROOT, command, source, "uncertified-publication",
        (("samePublishedCut : stream.checkpointEnd = catalog.stream.checkpointEnd",
          "samePublishedCut : True"),),
        "have unchanged")
    check_lean_theorems(ROOT, command, source, count=12)


def main():
    verify_lean()
    for mutation, law in (
        ("numeric_scope", "PublishedOwnScope"),
        ("by_state", "PublishedExactHistory"),
        ("loose_root", "PublishedReconstructs"),
        ("manifest_only", "PublishedReconstructs"),
        ("ignore_format", "PublishedReconstructs"),
        ("newer_root", "ResponseAtRequestedCut"),
        ("follow_head", "ResponseAtRequestedCut"),
        ("omit_tail", "ResponseAtRequestedCut"),
    ):
        check(f"control-{mutation}", (law,), mutation=mutation, expected=law)
    for bound in (2, 3):
        check(f"baseline-{bound}", LAWS, bound=bound)
    for law in ("NeverReadsForkGenesis", "NeverRecoversFromTrimWhileWritesContinue"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
