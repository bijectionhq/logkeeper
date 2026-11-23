#!/usr/bin/env python3
"""Check handoff durability across target membership changes."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_theorems, check_tla, command_in, compile_lean_modules

LAWS = ("AnyTargetQuorumCanRecover", "RetainedByServingSide")


def check(name, laws, *, design="stamped", mutation="none", expected=None):
    constants = {"Design": f'"{design}"', "Mutation": f'"{mutation}"'}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "Install", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "06-generations/Reservation.lean",
        "11-authority-refinement/AuthorityRefinement.lean",
        "12-quorum-membership/JournalRefinement.lean",
    ))
    source = ROOT / "DurableInstall.lean"
    proof = source.read_text(encoding="utf-8")
    for name, edits, failure in (
        ("missing-current-quorum", (
            ("(copiesAtActivation : CompleteCut target)", "(copiesAtActivation : True)"),
            ("ready.exactImage ready.dataQuorum", "ready.exactImage True.intro"),
        ), "exact ⟨equal ▸ logicalStep, activeRow, copiesAtActivation, adoptedMembers⟩"),
        ("different-membership", (
            ("(adoptedMembers : target.members = currentMembership certificate.target.group)",
             "(adoptedMembers : True)"),
            ("ready.dataQuorum adopted", "ready.dataQuorum True.intro"),
            ("(adopted : target.members", "(_adopted : target.members"),
        ), "exact ⟨equal ▸ logicalStep, activeRow, copiesAtActivation, adoptedMembers⟩"),
        ("different-image", (
            ("(matchesImage : target.logical = installed certificate)", "(matchesImage : True)"),
            ("ready.exactImage ready.dataQuorum", "True.intro ready.dataQuorum"),
        ), "have certifiedImage : target.logical = installed certificate := matchesImage"),
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
        code, log, output = command_in(ROOT, case, [*command, str(path)])
        line = mutated[:mutated.index(failure)].count("\n") + 1
        errors = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(errors) != 1 or f"{source.name}:{line}:" not in errors[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: composition failed at line {line}", flush=True)

    check_lean_theorems(ROOT, command, source, count=4)


def main():
    verify_lean()
    for mutation, law in (
        ("stale_proof", "AnyTargetQuorumCanRecover"),
        ("stale_proof", "RetainedByServingSide"),
        ("reclaim_without_invalidation", "AnyTargetQuorumCanRecover"),
        ("ack_preparation", "StillHasPayload"),
    ):
        check(f"control-{mutation}-{law}", (law,), mutation=mutation, expected=law)
    for design, witness in (
        ("stamped", "NeverRecertifiesAndReleases"),
        ("registered", "NeverCarriesAndReleases"),
    ):
        check(f"baseline-{design}", LAWS, design=design)
        check(f"witness-{design}", (witness,), design=design, expected=witness)


if __name__ == "__main__":
    main()
