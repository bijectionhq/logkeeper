#!/usr/bin/env python3
"""Reproduce the trim races, admission bounds, and capacity proofs."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla, command_in

LEAN = os.environ.get("LEAN_BIN", "lean")
LAWS = ("PublishedBeforeTrim", "ReplayProtected", "RecoveryBound", "RetainedBound")


def check(name, invariants, *, mutation="none", expected=None, bound=5):
    constants = {"Mutation": f'"{mutation}"', "MaxLsn": bound, "ReplayBudget": 2, "RetainedBudget": 3}
    check_tla(ROOT, "Retention", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in invariants), expected=expected)


def check_lean():
    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    source = ROOT / "Retention.lean"
    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [LEAN, str(source)])
    reports = [line for line in output.splitlines() if "depends on axioms" in line]
    if code != 0 or len(reports) != 5 or any(not line.endswith("[propext, Quot.sound]") for line in reports):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: five theorems checked with standard axioms only ({version.stdout.strip()})", flush=True)


def lean_controls():
    proof = (ROOT / "Retention.lean").read_text(encoding="utf-8")
    for name, theorem, edits in (
        ("checkpoint-cap", "checkpoint_stall_forces_backpressure", (
            ("    (boundedRecovery : DebtBound possibleHead covered cap) :", "    :"),
            ("  have bounded := boundedRecovery head reachable\n", ""),
        )),
        ("cursor", "exact_cursor_caps_head", (
            ("(retainedBound : head - floor ≤ cap) (exactResume : floor ≤ cursor) :", "(retainedBound : head - floor ≤ cap) :"),
            ("exact_cursor_caps_head head floor cursor cap retainedBound exactResume", "exact_cursor_caps_head head floor cursor cap retainedBound"),
        )),
        ("reserve", "reserved_capacity_admits_control", (
            ("(ordinaryAdmission : used + reserve ≤ hard) (fitsReserve : charge ≤ reserve) :", "(fitsReserve : charge ≤ reserve) :"),
        )),
    ):
        mutated = proof
        for original, replacement in edits:
            if mutated.count(original) != 1:
                raise SystemExit(f"Lean control {name}: ambiguous mutation {original}")
            mutated = mutated.replace(original, replacement)
        case = ROOT / ".results" / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        file = case / "Retention.lean"
        file.write_text(mutated, encoding="utf-8")
        line = mutated[:mutated.index("  omega", mutated.index(f"theorem {theorem}"))].count("\n") + 1
        code, log, output = command_in(ROOT, case, [LEAN, str(file)])
        diagnostics = [found for found in output.splitlines() if ": error:" in found]
        if (code != 1 or len(diagnostics) != 1 or
                f"Retention.lean:{line}:" not in diagnostics[0] or "omega could not prove" not in diagnostics[0]):
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: {theorem} failed at line {line}", flush=True)


def main():
    lean_controls()
    for mutation, law in (
        ("use_uploaded", "PublishedBeforeTrim"),
        ("stale_replay", "ReplayProtected"),
        ("stale_trim", "ReplayProtected"),
        ("no_recovery_cap", "RecoveryBound"),
        ("no_retained_cap", "RetainedBound"),
    ):
        check(f"control-{mutation}", (law,), mutation=mutation, expected=law)
    for bound in (5, 8):
        check(f"baseline-{bound}", LAWS, bound=bound)
    for law in ("NeverPausedByHold", "NeverReclaimsAfterClose"):
        check(f"witness-{law}", (law,), expected=law)
    check_lean()


if __name__ == "__main__":
    main()
