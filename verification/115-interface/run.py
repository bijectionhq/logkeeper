#!/usr/bin/env python3
"""Check the five verbs, independent lifecycle authority, and negative controls."""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import TLA_SHA256, check_lean_theorems, command_in


def run_lean(results):
    lake = os.environ.get("LAKE_BIN", str(Path.home() / ".elan/bin/lake"))
    lean = [lake, "env", "lean"]
    version = subprocess.check_output([*lean, "--version"], cwd=ROOT, text=True)
    if "version 4.35.0," not in version:
        raise SystemExit(f"Expected Lean 4.35.0, found {version.strip()}")

    model_path = ROOT / "Interface.lean"
    checks_path = ROOT / "Checks.lean"
    model = model_path.read_text()
    checks = checks_path.read_text()
    baseline = results / "lean"
    code, log, _ = command_in(ROOT, baseline, [
        *lean, "-o", str(baseline / "Interface.olean"), str(model_path),
    ])
    if code:
        raise SystemExit(f"Lean model failed, see {log}")
    command = ["env", f"LEAN_PATH={baseline}", *lean]
    check_lean_theorems(ROOT, command, checks_path, count=30)

    # Recompile the actual operational definitions in each variant. Exercise only
    # the named law so an unrelated failure cannot count as evidence.
    definitions = re.sub(r"^theorem .*?\n\n", "", model, flags=re.M | re.S)
    fixtures = re.sub(r"^theorem .*?\n\n", "", checks, flags=re.M | re.S)
    fixtures = re.sub(r"^#print axioms .*\n", "", fixtures, flags=re.M)
    fixtures = fixtures.removesuffix("end Interface\n")
    controls = [
        ("exactTemporalRead", "| .exact cut => cut", "| .exact _ => head store"),
        ("projectedRange", "query.endBefore - query.first", "1"),
        ("validateAtDecision", "request.checks.all (satisfies store.history)",
         "request.checks.all (satisfies (snapshot store request.basis))"),
        ("retryUsesOriginal", "then .ok receipt else .error .changedRequest",
         "then .ok ⟨head store, true⟩ else .error .changedRequest"),
        ("retryRejectsChanged", "if original == request then .ok receipt else .error .changedRequest",
         "(.ok receipt)"),
        ("exactHold", "∀ pair ∈ store.leases, pair.2.expiresAt ≤ store.now ∨ floor ≤ pair.2.cut",
         "True"),
        ("freshReadRetry", "nextLease := handle + 1", "nextLease := handle"),
        ("watchResets", "cursor < store.floor || suffix.any", "false || suffix.any"),
        ("watchOrdered", "if receipt.accepted then some (receipt.cut, request.writes) else none",
         "some (receipt.cut, request.writes)"),
        ("effectiveOverlay", "overlay.getLast?.getD parent",
         "(overlay.getLast?.getD none).orElse (fun _ => parent)"),
        ("forgetAtDecision", "if forgotten view key.subject then none", "if false then none"),
        ("forgetAtDeadline", "decide (deadline ≤ store.now)", "decide (deadline < store.now)"),
    ]
    for name, old, new in controls:
        if definitions.count(old) != 1:
            raise SystemExit(f"{name}: mutation must match one definition")
        case = results / f"lean-{name}"
        case.mkdir(exist_ok=True)
        mutated = case / "Interface.lean"
        mutated.write_text(definitions.replace(old, new))
        code, log, _ = command_in(ROOT, case / "compile", [
            *lean, f"--root={case}", "-o", str(case / "Interface.olean"), str(mutated),
        ])
        if code:
            raise SystemExit(f"{name}: variant failed to compile, see {log}")

        law = re.search(rf"^theorem {name} :\n(.*?) := by\n  decide", checks, re.M | re.S)
        if not law:
            raise SystemExit(f"{name}: missing named theorem")
        goal = law[1]
        trial = case / "Control.lean"
        trial.write_text(fixtures + f"theorem {name} :\n{goal} := by\n  decide\nend Interface\n")
        command = ["env", f"LEAN_PATH={case}", *lean, str(trial)]
        code, log, output = command_in(ROOT, case / "expected-failure", command)
        errors = [line for line in output.splitlines() if ": error:" in line]
        if code != 1 or len(errors) != 1 or "Tactic `decide` proved that the proposition" not in output:
            raise SystemExit(f"{name}: expected exactly one false theorem, see {log}")

        trial.write_text(fixtures + f"theorem {name}Counterexample : ¬ (\n{goal}) := by\n  decide\n"
                         f"#print axioms {name}Counterexample\nend Interface\n")
        code, log, output = command_in(ROOT, case / "counterexample", command)
        if code or "does not depend on any axioms" not in output:
            raise SystemExit(f"{name}: negated theorem failed, see {log}")
        print(f"lean {name}: expected failure and verified negation", flush=True)


def run_tlc(results):
    java = os.environ.get("JAVA_BIN", str(Path.home() / "cycle3/jdk/Contents/Home/bin/java"))
    jar = os.environ.get("TLC_JAR", str(Path.home() / "cycle3/tools/formal/tla-1.7.4/tla2tools.jar"))
    if hashlib.sha256(Path(jar).read_bytes()).hexdigest() != TLA_SHA256:
        raise SystemExit("Expected the pinned TLC 1.7.4 jar")
    invariants = ["Typed", "InstallRequiresAuthority", "ArchiveRequiresAuthority", "RestoreRequiresEvidence",
                  "RetireRequiresAuthority", "RetireClosesAdmission", "DisposalDrains"]
    cases = [
        ("baseline", "strict", None),
        ("self-install", "self-install", "InstallRequiresAuthority"),
        ("row-archive", "row-archive", "ArchiveRequiresAuthority"),
        ("replace-with-row", "replace-with-row", "RestoreRequiresEvidence"),
        ("subject-retire", "subject-retire", "RetireRequiresAuthority"),
        ("late-hold", "late-hold", "RetireClosesAdmission"),
        ("undrained-disposal", "undrained-disposal", "DisposalDrains"),
        ("witness", "strict", "TerminalWitness"),
    ]
    for name, policy, expected in cases:
        case = results / f"tlc-{name}"
        case.mkdir(exist_ok=True)
        config = case / "Authority.cfg"
        checks = [*invariants, "TerminalWitness"] if name == "witness" else invariants
        config.write_text(f'SPECIFICATION Spec\nCONSTANT Policy = "{policy}"\n'
                          + "".join(f"INVARIANT {law}\n" for law in checks))
        with TemporaryDirectory(dir=case) as scratch:
            code, log, output = command_in(ROOT, case, [
                java, "-Xmx512m", f"-Djava.io.tmpdir={scratch}", "-jar", jar, "-workers", "1",
                "-fp", "0", "-deadlock", "-metadir", f"{scratch}/states",
                "-config", str(config), "Authority.tla",
            ])
        errors = [line for line in output.splitlines() if line.startswith("Error:")]
        if expected:
            if code != 12 or errors != [f"Error: Invariant {expected} is violated.",
                                         "Error: The behavior up to this point is:"]:
                raise SystemExit(f"TLC {name}: wrong counterexample, see {log}")
            steps = len(re.findall(r"^State \d+:", output, re.M)) - 1
            summary = f"reached {expected} in {steps} transitions"
        else:
            counts = re.search(r"(\d+) states generated, (\d+) distinct states found, 0 states left", output)
            if code or errors or not counts or "No error has been found" not in output:
                raise SystemExit(f"TLC {name}: baseline failed, see {log}")
            summary = f"{counts[2]} distinct states ({counts[1]} generated)"
        print(f"tlc {name}: {summary}", flush=True)


if __name__ == "__main__":
    results = ROOT / ".results"
    results.mkdir(exist_ok=True)
    run_lean(results)
    run_tlc(results)
