#!/usr/bin/env python3
"""Compare writer authorization across a placement move."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla, command_in

LEAN = os.environ.get("LEAN_BIN", "lean")
LAWS = ("NoWriterSubstitution", "BoundAppend", "ExactPrefix")


def check(name, checks, *, design="carry", mutation="none", expected=None, bound=2):
    constants = {"Design": f'"{design}"', "Mutation": f'"{mutation}"', "MaxLsn": bound}
    check_tla(ROOT, "WriterTransfer", name, "FairSpec", constants, checks, expected=expected)


def compile_dependencies():
    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    directory = ROOT / ".results" / "build"
    directory.mkdir(parents=True, exist_ok=True)
    for relative in ("07-reference/Kernel.lean", "06-generations/Reservation.lean"):
        source = ROOT.parent / relative
        code, log, _ = command_in(ROOT, directory / source.stem, [
            LEAN, f"--root={source.parent}", "-o", str(directory / f"{source.stem}.olean"), str(source),
        ])
        if code:
            raise SystemExit(f"Failed to build {source}; see {log}")
    return ["env", f"LEAN_PATH={directory}", LEAN]


def verify_lean():
    source = ROOT / "AuthorityRefinement.lean"
    command = compile_dependencies()
    baseline = source.read_text(encoding="utf-8")
    for name, original, replacement, failure, diagnostic in (
        ("uncleared-source",
         "rows := replace world.rows certificate.source.placement.group none,",
         "rows := world.rows,",
         "exact clear_active_row (after := frozen issued) grant (by intro writer; simp [frozen])", "Type mismatch"),
        ("changed-holder",
         "{certificate.source with placement := certificate.target}",
         "{certificate.source with placement := certificate.target, holder := certificate.source.holder + 1}",
         "exact .activate certificate.cut.history rfl rfl", "Application type mismatch"),
    ):
        if baseline.count(original) != 1:
            raise SystemExit(f"Lean control {name}: ambiguous mutation")
        mutated = baseline.replace(original, replacement)
        case = ROOT / ".results" / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        path = case / source.name
        path.write_text(mutated, encoding="utf-8")
        line = mutated[:mutated.index(failure)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [*command, str(path)])
        errors = [found for found in output.splitlines() if ": error:" in found]
        if (code != 1 or len(errors) != 1 or f"{source.name}:{line}:" not in errors[0]
                or diagnostic not in errors[0]):
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: refinement law failed at line {line}", flush=True)

    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [*command, str(source)])
    reports = [line for line in output.splitlines() if "depend" in line and "axioms" in line]
    allowed = ("[propext]", "[propext, Classical.choice, Quot.sound]", "does not depend on any axioms")
    if code != 0 or len(reports) != 9 or any(not line.endswith(allowed) for line in reports):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print("lean: nine refinement theorems checked with standard axioms only", flush=True)


def main():
    verify_lean()
    for mutation, law in (
        ("stale_prepare", "NoWriterSubstitution"),
        ("replace_holder", "NoWriterSubstitution"),
        ("ignore_holder", "BoundAppend"),
        ("ignore_placement", "BoundAppend"),
        ("ignore_lsn", "BoundAppend"),
    ):
        check(f"control-{mutation}", (("INVARIANT", law),), mutation=mutation, expected=law)
    safety = tuple(("INVARIANT", law) for law in LAWS)
    for design in ("fresh", "carry"):
        for bound in (2, 3):
            progress = (("PROPERTY", "PreparedMoveCompletes"),) if design == "carry" else ()
            check(f"baseline-{design}-{bound}", safety + progress, design=design, bound=bound)
    check("fresh-directory-failure", (("PROPERTY", "PreparedMoveCompletes"),),
          design="fresh", expected="liveness")
    law = "NeverMovesAndAppendsOffline"
    check("witness-offline-continuation", (("INVARIANT", law),), expected=law)


if __name__ == "__main__":
    main()
