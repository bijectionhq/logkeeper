"""Pinned tools and strict result checks shared by the verification studies."""

import hashlib
import os
from pathlib import Path
import re
import shlex
import subprocess
from tempfile import TemporaryDirectory
import urllib.request

TLA_URL = "https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar"
TLA_SHA256 = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"


def command_in(root, case, command):
    case.mkdir(parents=True, exist_ok=True)
    (case / "command.txt").write_text(shlex.join(command) + "\n", encoding="utf-8")
    log = case / "run.log"
    with log.open("w", encoding="utf-8") as output:
        result = subprocess.run(
            command, cwd=root, stdout=output, stderr=subprocess.STDOUT,
            timeout=60, check=False,
        )
    return result.returncode, log, log.read_text(encoding="utf-8")


def checker_jar(root):
    jar = root / ".tools" / "tla2tools.jar"
    jar.parent.mkdir(exist_ok=True)
    if not jar.exists():
        with urllib.request.urlopen(TLA_URL, timeout=30) as response:
            contents = response.read()
        if hashlib.sha256(contents).hexdigest() != TLA_SHA256:
            raise SystemExit("TLA+ tool checksum mismatch on download")
        jar.write_bytes(contents)
    if hashlib.sha256(jar.read_bytes()).hexdigest() != TLA_SHA256:
        raise SystemExit("TLA+ tool checksum mismatch on disk")
    return jar


def check_tla(root, module, name, specification, constants, checks, *, expected=None):
    case = root / ".results" / name
    case.mkdir(parents=True, exist_ok=True)
    config = case / f"{module}.cfg"
    config.write_text(
        f"SPECIFICATION {specification}\n"
        + "".join(f"CONSTANT {key} = {value}\n" for key, value in constants.items())
        + "".join(f"{kind} {law}\n" for kind, law in checks), encoding="utf-8"
    )
    scratch = os.environ.get("LOGKEEPER_TLC_SCRATCH", case)
    with TemporaryDirectory(prefix="tlc-", dir=scratch) as scratch_dir:
        states = Path(scratch_dir) / "states"
        java_tmp = Path(scratch_dir) / "java"
        states.mkdir()
        java_tmp.mkdir()
        code, log, output = command_in(root, case, [
            os.environ.get("JAVA_BIN", "java"), "-Xmx512m", "-XX:+UseParallelGC",
            f"-Djava.io.tmpdir={java_tmp}",
            "-jar", str(checker_jar(root)), "-workers", "1", "-fp", "0", "-deadlock",
            "-metadir", str(states), "-config", str(config), f"{module}.tla",
        ])
    errors = [line for line in output.splitlines() if line.startswith("Error:")]
    if expected == "liveness":
        ok = code == 13 and errors == [
            "Error: Temporal properties were violated.", "Error: The following behavior constitutes a counter-example:",
        ]
        summary = "found temporal counterexample"
    elif expected:
        ok = code == 12 and errors == [
            f"Error: Invariant {expected} is violated.", "Error: The behavior up to this point is:",
        ]
        steps = len(re.findall(r"^State \d+:", output, re.MULTILINE)) - 1
        summary = f"reached {expected} in {steps} transitions"
    else:
        counts = re.search(r"(\d+) states generated, (\d+) distinct states found, 0 states left", output)
        ok = code == 0 and not errors and counts and "No error has been found" in output
        summary = f"{counts[2]} distinct states" if counts else "missing completion counts"
    if not ok:
        raise SystemExit(f"{name}: unexpected result (exit {code}); see {log}")
    print(f"{name}: {summary}", flush=True)


def compile_lean_modules(root, sources):
    lean = os.environ.get("LEAN_BIN", "lean")
    version = subprocess.run([lean, "--version"], cwd=root, text=True, capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0; found {version.stdout.strip()}")

    build = root / ".results" / "build"
    build.mkdir(parents=True, exist_ok=True)
    command = ["env", f"LEAN_PATH={build}", lean]
    for relative in sources:
        source = root.parent / relative
        code, log, _ = command_in(root, build / source.stem, [
            *command, f"--root={source.parent}", "-o", str(build / f"{source.stem}.olean"), str(source),
        ])
        if code:
            raise SystemExit(f"Failed to build {source}; see {log}")
    return command


def check_lean_theorems(root, command, source, count, *, case="lean"):
    code, log, output = command_in(root, root / ".results" / case, [*command, str(source)])
    reports = re.findall(
        r"^'[^']+' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
        output, re.MULTILINE,
    )
    standard = {"propext", "Classical.choice", "Quot.sound"}
    if code or len(reports) != count or any(
        report and not {axiom.strip() for axiom in report.split(",")} <= standard for report in reports
    ):
        raise SystemExit(f"Unexpected Lean result; see {log}")
    print(f"lean: {count} theorems checked with standard axioms only", flush=True)

def check_lean_mutation(root, command, source, name, edits, failure):
    mutated = source.read_text(encoding="utf-8")
    for old, new in edits:
        if mutated.count(old) != 1:
            raise SystemExit(f"Lean control {name}: ambiguous mutation")
        mutated = mutated.replace(old, new)
    case = root / ".results" / f"lean-control-{name}"
    case.mkdir(parents=True, exist_ok=True)
    file = case / source.name
    file.write_text(mutated, encoding="utf-8")
    code, log, output = command_in(root, case, [*command, str(file)])
    line = mutated[:mutated.index(failure)].count("\n") + 1
    errors = [entry for entry in output.splitlines() if ": error:" in entry]
    if code != 1 or len(errors) != 1 or f"{source.name}:{line}:" not in errors[0]:
        raise SystemExit(f"Lean control {name}: unexpected diagnostic; see {log}")
    print(f"lean-control-{name}: expected proof failed at line {line}", flush=True)
