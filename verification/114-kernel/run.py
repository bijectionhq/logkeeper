#!/usr/bin/env python3
"""Run the unbounded Lean proofs and finite ordered-decision controls."""

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

STUDY = Path(__file__).resolve().parent
sys.path.insert(0, str(STUDY.parent))
from study_tools import check_lean_theorems, check_tla, command_in

LAKE = Path(os.environ.get("LAKE_BIN", Path.home() / ".elan" / "bin" / "lake"))
REFERENCE = STUDY.parent / "lean"
JAVA = Path.home() / "cycle3" / "jdk" / "Contents" / "Home" / "bin" / "java"
TLA_JAR = Path.home() / "cycle3" / "tools" / "formal" / "tla-1.7.4" / "tla2tools.jar"

CONTROLS = {
    "stale-writer": "WriterSafe",
    "rewrite-prefix": "HistoryStable",
    "new-receipt": "ReceiptExact",
    "replay-read": "ReadFresh",
    "stale-cut": "CaptureExact",
    "shorten-lease": "LeaseRenewal",
    "renew-erased": "LeaseBasisOpen",
    "live-roots-only": "TrimSafe",
    "unchecked-budget": "Funded",
    "sweep-name": "FenceSafe",
    "ignore-opaque": "FenceSafe",
    "late-reference": "FenceSafe",
    "no-drift": "DisposalSafe",
    "wrong-rotation": "RotationGuard",
    "no-key-rotation": "ErasureAtomic",
    "sweep-root": "SettlementSafe",
    "no-disposition": "SettlementSafe",
}

WITNESSES = {
    "maintenance-witness": "NoMaintenanceWitness",
    "disposal-witness": "NoDisposalWitness",
    "settlement-witness": "NoSettlementWitness",
    "unleased-hold-witness": "NoUnleasedHoldWitness",
    "drift-window-witness": "NoDriftWindowWitness",
}


def verify_tla():
    if JAVA.is_file():
        os.environ.setdefault("JAVA_BIN", str(JAVA))
    pinned = Path(os.environ.get("TLA_JAR", TLA_JAR))
    if pinned.is_file():
        jar = STUDY / ".tools" / "tla2tools.jar"
        jar.parent.mkdir(exist_ok=True)
        if pinned.resolve() != jar.resolve():
            shutil.copyfile(pinned, jar)

    def check(case, mutation, invariants, expected=None):
        bounds = {"Mutation": f'"{mutation}"', "MaxSteps": "8", "MaxTime": "4", "Capacity": "2"}
        check_tla(STUDY, "KernelCuts", case, "Spec", bounds,
                  [("INVARIANT", law) for law in invariants], expected=expected)

    check("baseline", "none", dict.fromkeys(CONTROLS.values()))
    for mutation, law in CONTROLS.items():
        check(mutation, mutation, (law,), expected=law)
    for case, law in WITNESSES.items():
        check(case, "none", (law,), expected=law)


def verify_lean():
    version = subprocess.run([str(LAKE), "env", "lean", "--version"], cwd=REFERENCE,
                             text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0, found {version.stdout.strip()}")

    results = STUDY / ".results"
    code, log, _ = command_in(REFERENCE, results / "reference-build",
                              [str(LAKE), "build", "Logkeeper.Reducer"])
    if code:
        raise SystemExit(f"Reducer build failed. See {log}")
    build = results / "build"
    build.mkdir(parents=True, exist_ok=True)
    lean_path = os.pathsep.join(map(str, (build, REFERENCE / ".lake/build/lib/lean")))
    lean = [str(LAKE), "env", "env", f"LEAN_PATH={lean_path}", "lean"]

    for name in ("DecisionKernel", "Refinement", "Safety", "Collection", "Deletion", "Witness", "Footprint"):
        source = STUDY / f"{name}.lean"
        code, log, _ = command_in(STUDY, results / f"lean-{name}", [
            *lean, f"--root={STUDY}", "-o", str(build / f"{name}.olean"), str(source),
        ])
        if code:
            raise SystemExit(f"{name} failed. See {log}")
    audit = STUDY / "Audit.lean"
    theorem_count = len(re.findall(r"^#print axioms ", audit.read_text(), re.MULTILINE))
    check_lean_theorems(STUDY, lean, audit, theorem_count)

    lean_control(lean, "wrong-funding-image", "Refinement.lean",
                 "| .fundWindow window => .fund window",
                 "| .fundWindow _ => .fence 1 7",
                 "effect_refines")
    lean_control(lean, "wrong-protection-cut", "Deletion.lean",
                 ".protectRange s.checkpoints.selected.cut.nextLsn through.nextLsn",
                 ".protectRange (s.checkpoints.selected.cut.nextLsn + 1) through.nextLsn",
                 "protect_effect_as_range")
    lean_control(lean, "funding-in-original-five", "Footprint.lean",
                 "| .fund _ | .fence _ _ | .dispose _ _ => False",
                 "| .fence _ _ | .dispose _ _ => False",
                 "original_effect_keeps_window_and_fences")


def lean_control(lean, name, source_name, original, mutation, theorem):
    source = (STUDY / source_name).read_text()
    if source.count(original) != 1:
        raise SystemExit(f"{name} has no unique mutation")
    source = source.replace(original, mutation)
    case = STUDY / ".results" / f"lean-control-{name}"
    case.mkdir(parents=True, exist_ok=True)
    mutated = case / source_name
    mutated.write_text(source)
    code, log, output = command_in(STUDY, case, [*lean, str(mutated)])
    declaration = re.compile(r"^(?:private )?(?:theorem|def|inductive|structure) (\w+)")
    lines = source.splitlines()
    declarations = [(number, match[1]) for number, line in enumerate(lines, 1)
                    if (match := declaration.match(line))]
    start = next(number for number, declared in declarations if declared == theorem)
    stop = next((number for number, _ in declarations if number > start), len(lines) + 1)
    diagnostics = [line for line in output.splitlines() if ": error" in line]
    primary = [line for line in diagnostics if "declaration uses `sorry`" not in line]
    match = re.search(rf"{re.escape(source_name)}:(\d+):\d+: error", primary[0]) if primary else None
    if code != 1 or len(primary) != 1 or not match or not start <= int(match[1]) < stop:
        raise SystemExit(f"{name} did not fail at {theorem}. See {log}")
    print(f"lean-control-{name}: expected proof failed at {theorem}", flush=True)


if __name__ == "__main__":
    modes = sys.argv[1:]
    if modes not in ([], ["lean"], ["tla"]):
        raise SystemExit("Usage: run.py [lean|tla]")
    if not modes or modes == ["lean"]:
        verify_lean()
    if not modes or modes == ["tla"]:
        verify_tla()
