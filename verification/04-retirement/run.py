#!/usr/bin/env python3
"""Check terminal fencing, custody, and erasure under delayed delivery."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla, command_in

LAWS = ("CustodyKnown", "ErasureStable", "AllAcknowledged")
LEAN = os.environ.get("LEAN_BIN", "lean")


def check(name, invariants=(), *, mutation="none", expected=None, bound=3, property_=None):
    constants = {"Mutation": f'"{mutation}"', "Locations": "{" + ",".join(
        str(location) for location in range(1, bound + 1)) + "}"}
    checks = tuple(("INVARIANT", law) for law in invariants)
    if property_:
        checks += (("PROPERTY", property_),)
    check_tla(ROOT, "Retirement", name, "FairSpec", constants, checks, expected=expected)


def lean_controls():
    source = (ROOT / "Retirement.lean").read_text(encoding="utf-8")
    for name, original, replacement, failure in (
        ("unfenced-delivery", "(unfenced : ¬ state.fenced location)", "(unfenced : True)",
         "exact False.elim (unfenced"),
        ("absence-only", "state.fenced location ∧ ¬ state.resident location) :",
         "¬ state.resident location) :", "exact ⟨known, fun _ => ⟨closed, proofFor⟩⟩"),
    ):
        if source.count(original) != 1:
            raise SystemExit(f"Lean control {name}: ambiguous mutation")
        mutated = source.replace(original, replacement)
        case = ROOT / ".results" / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        file = case / "Retirement.lean"
        file.write_text(mutated, encoding="utf-8")
        line = mutated[:mutated.index(failure)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [LEAN, str(file)])
        diagnostics = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(diagnostics) != 1 or f"Retirement.lean:{line}:" not in diagnostics[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: validity proof failed at line {line}", flush=True)


def check_lean():
    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    source = ROOT / "Retirement.lean"
    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [LEAN, str(source)])
    reports = [line for line in output.splitlines() if "depends on axioms" in line]
    if code != 0 or len(reports) != 2 or any(not line.endswith("[propext, Quot.sound]") for line in reports):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: two theorems checked with standard axioms only ({version.stdout.strip()})", flush=True)


def main():
    lean_controls()
    for name, mutation, law in (
        ("unknown-custody", "unrecorded_copy", "CustodyKnown"),
        ("unrecorded-erasure", "unrecorded_copy", "ErasureStable"),
        ("absence-only", "absence_only", "ErasureStable"),
        ("forget-fence", "forget_fence", "ErasureStable"),
        ("majority-erasure", "only_majority", "AllAcknowledged"),
    ):
        check(f"control-{name}", (law,), mutation=mutation, expected=law)
    for bound in (3, 4):
        check(f"baseline-{bound}", LAWS, property_="ProgressWithAccess", bound=bound)
    check("majority-progress", property_="ProgressWithMajority", expected="liveness")
    law = "NeverFinishesWithLatePacket"
    check("witness-late-packet", (law,), expected=law)
    check_lean()


if __name__ == "__main__":
    main()
