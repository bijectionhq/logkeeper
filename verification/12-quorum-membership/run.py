#!/usr/bin/env python3
"""Compare journal reconfiguration boundaries under faults and stale votes."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_theorems, check_tla, command_in, compile_lean_modules

LAWS = ("NoStaleCommit", "QuorumCanRecover", "SurvivingCopy")


def check(name, laws, *, design="joint", mutation="none", expected=None, bound=2):
    constants = {"Design": f'"{design}"', "Mutation": f'"{mutation}"', "MaxLsn": bound}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "Membership", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, ("07-reference/Kernel.lean",))
    source = ROOT / "JournalRefinement.lean"
    proof = source.read_text(encoding="utf-8")
    for name, edits, failure in (
        ("no-new-copy",
         (("(certified : CompleteCut {journal with members := members}) :", "(certified : True) :"),
          (".finalizeMembership newMembers certified, rfl", ".finalizeMembership newMembers True.intro, rfl")),
         "exact certified"),
        ("append-vote-without-bytes",
         (("(persisted : Covered journal journal.logical.history.length ⟨writer.epoch, payload⟩) :",
           "(persisted : True) :"),),
         "exact persisted"),
        ("reclaim-active-copy",
         (("""      (keeps : ∀ replica ∈ journal.members, ∀ lsn entry, journal.logical.firstRetained ≤ lsn →
        journal.copies replica lsn entry → copies replica lsn entry) :""",
           "      (keeps : True) :"),),
         "exact keeps replica member lsn entry retained (confirms replica member yes)"),
        ("volatile-fence",
         (("(refuses : ∀ replica ∈ members, promised replica = true → accepts replica = false) :",
           "(refuses : True) :"),),
         "exact Bool.false_ne_true ((refuses replica enrolled promisedHere).symm.trans acceptedHere)"),
    ):
        mutated = proof
        for original, replacement in edits:
            if mutated.count(original) != 1:
                raise SystemExit(f"Lean control {name}: ambiguous mutation")
            mutated = mutated.replace(original, replacement)
        case = ROOT / ".results" / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        path = case / source.name
        path.write_text(mutated, encoding="utf-8")
        line = mutated[:mutated.index(failure)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [*command, str(path)])
        errors = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(errors) != 1 or f"{source.name}:{line}:" not in errors[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: intended durability law failed at line {line}", flush=True)

    check_lean_theorems(ROOT, command, source, count=9)


def main():
    verify_lean()
    for name, design, mutation, law in (
        ("direct-stale", "direct", "none", "NoStaleCommit"),
        ("direct-recovery", "direct", "none", "QuorumCanRecover"),
        ("metadata-only", "joint", "metadata_only", "SurvivingCopy"),
        ("length-only", "joint", "length_only", "SurvivingCopy"),
        ("reused-address", "joint", "reuse_address", "SurvivingCopy"),
        ("early-discard", "joint", "early_discard", "SurvivingCopy"),
        ("new-only-joint", "joint", "joint_old_optional", "QuorumCanRecover"),
        ("new-below-quorum", "sealed", "new_below_quorum", "SurvivingCopy"),
    ):
        check(f"control-{name}", (law,), design=design, mutation=mutation, expected=law)
    for design in ("joint", "sealed"):
        for bound in (2, 3):
            check(f"baseline-{design}-{bound}", LAWS, design=design, bound=bound)
    law = "NeverWritesJointAfterLoss"
    check("witness-joint-replacement-after-loss", (law,), expected=law)


if __name__ == "__main__":
    main()
