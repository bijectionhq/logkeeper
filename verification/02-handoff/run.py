#!/usr/bin/env python3
"""Reproduce the handoff comparisons and Lean proofs."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla, command_in

RESULTS = ROOT / ".results"
LEAN = os.environ.get("LEAN_BIN", "lean")
SAFETY = ("SingleAuthority", "NoFork", "ExactCut")


def check(name, design, checks, *, mutation="none", expected=None, fair=True, bound=2):
    specification = "FairSpec" if fair else "Spec"
    constants = {"Design": f'"{design}"', "Mutation": f'"{mutation}"', "MaxLsn": bound}
    check_tla(ROOT, "Handoff", name, specification, constants, checks, expected=expected)


def check_lean():
    case = RESULTS / "lean"
    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    code, log, output = command_in(ROOT, case, [LEAN, str(ROOT / "Handoff.lean")])
    reports = [line for line in output.splitlines() if "depend" in line and "axioms" in line]
    if (code != 0 or len(reports) != 5 or
            any(not line.endswith(("does not depend on any axioms", "[propext, Quot.sound]"))
                for line in reports)):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: five theorems checked with standard axioms only ({version.stdout.strip()})",
          flush=True)


def lean_controls():
    source = (ROOT / "Handoff.lean").read_text(encoding="utf-8")
    for name, edits, failing_line in (
        ("activation", (
            ("(installed : ∃ cut, state.installed = some cut)", "(installed : True)"),
            (".activate ⟨source, rfl⟩", ".activate True.intro"),
        ), "exact ⟨fun _ => installed, installedExact⟩"),
        ("seal", (
            ("(sealed : state.sourceSealed = true)", "(sealed : True)"),
            (".install rfl rfl", ".install True.intro rfl"),
        ), "exact ⟨sealed, rfl, ⟨[], by simp⟩⟩"),
    ):
        mutated = source
        for original, replacement in edits:
            if mutated.count(original) != 1:
                raise SystemExit(f"Lean control {name}: ambiguous mutation {original}")
            mutated = mutated.replace(original, replacement)
        case = RESULTS / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        file = case / "Handoff.lean"
        file.write_text(mutated, encoding="utf-8")
        line = mutated[:mutated.index(failing_line)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [LEAN, str(file)])
        diagnostics = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(diagnostics) != 1 or f"Handoff.lean:{line}:" not in diagnostics[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: validity proof failed at line {line}", flush=True)


def invariants(laws):
    return tuple(("INVARIANT", law) for law in laws)


def main():
    lean_controls()
    for name, mutation, law in (
        ("control-unfenced", "skip_seal", "SingleAuthority"),
        ("control-fork", "skip_seal", "NoFork"),
        ("control-stale", "trust_precopy", "ExactCut"),
        ("control-reopen", "reopen_source", "SingleAuthority"),
    ):
        check(name, "portable", invariants((law,)), mutation=mutation, expected=law)
    check("control-no-fairness", "portable", (("PROPERTY", "LinkOnlyProgress"),),
              expected="liveness", fair=False)

    for design, properties in (
        ("directory", ("WithDirectoryProgress",)),
        ("portable", ("WithDirectoryProgress", "LinkOnlyProgress", "InstalledProgress")),
    ):
        for bound in (2, 3):
            check(f"baseline-{design}-{bound}", design,
                      invariants(SAFETY) + tuple(("PROPERTY", law) for law in properties), bound=bound)
    check("directory-partition", "directory", (("PROPERTY", "LinkOnlyProgress"),),
              expected="liveness")
    check("directory-permanent-loss", "directory", (("PROPERTY", "LinkOnlyProgress"),),
              mutation="permanent_directory_loss", expected="liveness")
    check("directory-installed-partition", "directory", (("PROPERTY", "InstalledProgress"),),
              expected="liveness")
    for law in ("NeverAppendsAfterDirectoryLoss", "NeverActivatesWithLinkDown"):
        check(f"witness-{law}", "portable", invariants((law,)), expected=law)
    check_lean()


if __name__ == "__main__":
    main()
