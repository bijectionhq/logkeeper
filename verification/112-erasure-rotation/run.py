#!/usr/bin/env python3
"""Compare erasure commit rules for journal key-generation rotation."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ["NoResurrection", "AlwaysRecoverable", "HeldViewKeptUntilDeadline"]


def rotation(name, policy, laws, *, progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallyErased"))
    check_tla(ROOT, "ErasureRotation", name, "Fair" if progress else "Spec", {"Policy": f'"{policy}"'},
              checks, expected=expected)


def verify_tla():
    rotation("commit-while-the-old-root-is-selectable", "commit-at-publication", ["NoResurrection"],
             expected="NoResurrection")
    rotation("revoke-with-the-old-root-selectable", "commit-at-publication", ["AlwaysRecoverable"],
             expected="AlwaysRecoverable")
    rotation("append-old-generation-after-the-cut", "unfenced-generation", ["AlwaysRecoverable"],
             expected="AlwaysRecoverable")
    rotation("revoke-the-held-view-at-commit", "revoke-holds", ["HeldViewKeptUntilDeadline"],
             expected="HeldViewKeptUntilDeadline")
    rotation("reference", "reference", SAFETY, progress=True)
    rotation("clean-recovery-witness", "reference", ["CleanRecoveryWitness"], expected="CleanRecoveryWitness")
    rotation("erased-view-witness", "reference", ["ErasedViewWitness"], expected="ErasedViewWitness")


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "ErasureCommit.lean"
    check_lean_mutation(ROOT, command, source, "accept-an-unfenced-suffix",
                        [("∀ generation ∈ image.suffix, image.root ≤ generation",
                          "∀ generation ∈ image.suffix, 0 ≤ generation")],
                        "  omega")
    check_lean_theorems(ROOT, command, source, count=3)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
