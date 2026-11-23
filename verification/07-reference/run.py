#!/usr/bin/env python3
"""Check the consolidated logical-stream model and weakened decision rules."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import command_in

LEAN = os.environ.get("LEAN_BIN", "lean")


def check_controls(source):
    proof = source.read_text(encoding="utf-8")
    for name, edits, failure in (
        ("wrong-lsn", (
            ("ordered : lsn = state.history.length", "ordered : True"),
            ("⟨authorized, rfl, recoveryRoom, retainedRoom⟩",
             "⟨authorized, True.intro, recoveryRoom, retainedRoom⟩"),
        ), "stale admitted.ordered"),
        ("stale-writer", (
            ("  authorized : state.authority = .active writer\n  ordered",
             "  authorized : True\n  ordered"),
            ("⟨authorized, rfl, recoveryRoom, retainedRoom⟩",
             "⟨True.intro, rfl, recoveryRoom, retainedRoom⟩"),
            ("(valid : Valid limits state)\n    (authorized",
             "(valid : Valid limits state)\n    (_authorized"),
        ), "stale admitted.authorized"),
        ("reopen-spent-permit", (
            ("(reserved : state.replays id = .prepared lsn)", "(reserved : True)"),
            ("authorized (by simp [reservation, replaceReplay]) available", "authorized True.intro available"),
        ), "have matching : before.replays admitted = .prepared lsn := reserved"),
        ("uncertified-trim", (
            ("(published : cut ≤ state.checkpointEnd)", "(published : True)"),
        ), "refine ⟨published, checkpointCommitted, protects, recoveryBound, ?_⟩"),
        ("unprotected-trim", (
            ("(protects : ∀ id lsn, state.replays id = .holding lsn → cut ≤ lsn)", "(protects : True)"),
        ), "refine ⟨published, checkpointCommitted, protects, recoveryBound, ?_⟩"),
        ("speculative-cut", (
            ("then some state.history.length else none", "then some (state.history.length + 1) else none"),
        ), "next authorized => exact ⟨authorized, (Option.some.inj response).symm⟩"),
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
        line = mutated[:mutated.index(failure)].count("\n") + 1
        code, log, output = command_in(ROOT, case, [LEAN, str(file)])
        diagnostics = [found for found in output.splitlines() if ": error:" in found]
        if code != 1 or len(diagnostics) != 1 or f"Kernel.lean:{line}:" not in diagnostics[0]:
            raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
        print(f"lean-control-{name}: law failed at line {line}", flush=True)


def check_baseline(source):
    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [LEAN, str(source)])
    reports = [line for line in output.splitlines() if "depend" in line and "axioms" in line]
    allowed = ("does not depend on any axioms", "[propext]", "[propext, Quot.sound]",
               "[propext, Classical.choice, Quot.sound]")
    if code != 0 or len(reports) != 16 or any(not line.endswith(allowed) for line in reports):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: sixteen theorems checked with standard axioms only ({version.stdout.strip()})", flush=True)


def main():
    source = ROOT / "Kernel.lean"
    check_controls(source)
    check_baseline(source)


if __name__ == "__main__":
    main()
