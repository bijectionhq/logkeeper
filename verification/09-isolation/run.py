#!/usr/bin/env python3
"""Check projection isolation and capacity trade-offs with pinned Lean."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import command_in

LEAN = os.environ.get("LEAN_BIN", "lean")


def main():
    source = ROOT / "Isolation.lean"
    proof = source.read_text(encoding="utf-8")
    for name, edits, failure in (
        ("broadcast-write", (
            ("if queried = target then records queried ++ [entry] else records queried",
             "records queried ++ [entry]"),
            ("(target : Stream)", "(_target : Stream)"),
            ("simpa [append, different] using prior", "simpa [append] using prior"),
        ), "simpa [append] using prior"),
        ("borrowed-reservation", (
            (" (highLimited : high ≤ cap - reserved)", ""),
        ), "omega"),
    ):
        mutated = proof
        for original, replacement in edits:
            if mutated.count(original) != 1:
                raise SystemExit(f"Lean control {name}: ambiguous mutation")
            mutated = mutated.replace(original, replacement)
        case = ROOT / ".results" / f"lean-control-{name}"
        case.mkdir(parents=True, exist_ok=True)
        file = case / source.name
        file.write_text(mutated, encoding="utf-8")
        start = mutated.index("theorem reservation_protects_eligible_admission") if failure == "omega" else 0
        line = mutated[:mutated.index(failure, start)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [LEAN, str(file)])
        errors = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(errors) != 1 or f"Isolation.lean:{line}:" not in errors[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: law failed at line {line}", flush=True)

    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [LEAN, str(source)])
    reports = [line for line in output.splitlines() if "depend" in line and "axioms" in line]
    allowed = ("[propext]", "[propext, Quot.sound]", "[propext, Classical.choice, Quot.sound]")
    if code != 0 or len(reports) != 4 or any(not line.endswith(allowed) for line in reports):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: four theorems checked with standard axioms only ({version.stdout.strip()})", flush=True)


if __name__ == "__main__":
    main()
