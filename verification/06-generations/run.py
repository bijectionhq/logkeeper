#!/usr/bin/env python3
"""Explore repeated moves and immutable stale certificate delivery."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla, command_in

LEAN = os.environ.get("LEAN_BIN", "lean")
LAWS = ("OneAuthority", "ReceiptsPreserved", "RetirementIsTerminal", "NoStrandedTransfer")


def check(name, invariants, *, mutation="none", expected=None, groups=2, generations=3, design="floor"):
    constants = {
        "Design": f'"{design}"',
        "Mutation": f'"{mutation}"',
        "Groups": "{" + ",".join(str(group) for group in range(1, groups + 1)) + "}",
        "MaxGeneration": generations,
        "MaxLsn": 2,
    }
    check_tla(ROOT, "Generations", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in invariants), expected=expected)


def verify_lean():
    source = ROOT / "Reservation.lean"
    proof = source.read_text(encoding="utf-8")
    edits = (
        ("some (slot.issuedThrough + 1)⟩", "some slot.issuedThrough⟩"),
        ("before.issuedThrough + 1 = nonce", "before.issuedThrough = nonce"),
        ("exact Nat.le_of_eq (Option.some.inj present).symm",
         "exact Nat.le_succ_of_le (Nat.le_of_eq (Option.some.inj present).symm)"),
        ("slot.live = some (issuedThrough + 1)", "slot.live = some issuedThrough"),
    )
    mutated = proof
    for original, replacement in edits:
        if mutated.count(original) != 1:
            raise SystemExit(f"Lean control: ambiguous mutation {original}")
        mutated = mutated.replace(original, replacement)
    case = ROOT / ".results" / "lean-control-reuse"
    case.mkdir(parents=True, exist_ok=True)
    file = case / source.name
    file.write_text(mutated, encoding="utf-8")
    line = mutated[:mutated.index("        omega", mutated.index("have sameNonce :"))].count("\n") + 1
    code, log, output = command_in(ROOT, case, [LEAN, str(file)])
    errors = [found for found in output.splitlines() if ": error:" in found]
    if code != 1 or len(errors) != 1 or f"Reservation.lean:{line}:" not in errors[0] or "omega could not prove" not in errors[0]:
        raise SystemExit(f"Lean control: unexpected diagnostic; see {log}")
    print(f"lean-control-reuse: stale nonce preservation failed at line {line}", flush=True)

    version = subprocess.run([LEAN, "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")
    code, log, output = command_in(ROOT, ROOT / ".results" / "lean", [LEAN, str(source)])
    reports = [line for line in output.splitlines() if "depend" in line and "axioms" in line]
    if (code != 0 or len(reports) != 3 or
            any(not line.endswith(("does not depend on any axioms", "[propext]", "[propext, Quot.sound]"))
                for line in reports)):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: three theorems checked with standard axioms only ({version.stdout.strip()})", flush=True)


def main():
    verify_lean()
    for mutation, law, groups in (
        ("accept_equal", "OneAuthority", 2),
        ("forget_generation", "OneAuthority", 2),
        ("accept_equal", "ReceiptsPreserved", 2),
        ("forget_generation", "RetirementIsTerminal", 2),
        ("wrong_target", "OneAuthority", 3),
    ):
        check(f"control-{mutation}-{law}", (law,), mutation=mutation, expected=law, groups=groups)
    for mutation, law in (
        ("reuse_nonce", "OneAuthority"),
        ("expire_slot", "NoStrandedTransfer"),
    ):
        check(f"control-{mutation}-{law}", (law,), mutation=mutation, expected=law, design="reservation")
    check("control-reservation-wrong-target", ("OneAuthority",), mutation="wrong_target",
          expected="OneAuthority", design="reservation", groups=3)
    for design in ("floor", "reservation"):
        check(f"baseline-{design}-2-groups-3-generations", LAWS, design=design)
        check(f"baseline-{design}-3-groups-4-generations", LAWS, groups=3, generations=4, design=design)
        law = "NeverReturnsAndCommits"
        check(f"witness-{design}-return", (law,), expected=law, design=design)


if __name__ == "__main__":
    main()
