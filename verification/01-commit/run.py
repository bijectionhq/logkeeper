#!/usr/bin/env python3
"""Run controls, baseline checks, and reachability witnesses with pinned TLC."""

import hashlib
import os
from pathlib import Path
import re
import shlex
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parent
TLC_VERSION = "1.7.4"
TLC_SHA256 = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
TLC_URL = f"https://github.com/tlaplus/tlaplus/releases/download/v{TLC_VERSION}/tla2tools.jar"
JAVA = os.environ.get("JAVA_BIN", "java")
DESIGNS = ("quorum", "object")
INVARIANTS = (
    "DenseHistory", "ReceiptMatchesCommit", "Recoverable",
    "Fenced", "ExactFenceCut", "ExactBarrier",
)
CONTROLS = (
    ("ignore_position", "DenseHistory", DESIGNS),
    ("ignore_fence", "Fenced", DESIGNS),
    ("fence_omits_tail", "ExactFenceCut", DESIGNS),
    ("single_vote", "Recoverable", ("quorum",)),
    ("publish_before_data", "Recoverable", ("object",)),
    ("reply_before_commit", "ReceiptMatchesCommit", DESIGNS),
    ("retry_by_lsn", "ReceiptMatchesCommit", DESIGNS),
    ("barrier_by_held", "ExactBarrier", DESIGNS),
)
WITNESSES = (
    "NeverOrdinaryAppend",
    "NeverReconciles",
    "NeverResumesAfterLoss",
    "NeverRefusesStagedOldWriter",
    "NeverReadsWhileStaged",
)


def checker_jar():
    jar = ROOT / ".tools" / "tla2tools.jar"
    jar.parent.mkdir(exist_ok=True)
    if not jar.exists():
        with urllib.request.urlopen(TLC_URL, timeout=30) as response:
            contents = response.read()
        if hashlib.sha256(contents).hexdigest() != TLC_SHA256:
            raise SystemExit(f"Checksum mismatch for {TLC_URL}")
        jar.write_bytes(contents)
    if hashlib.sha256(jar.read_bytes()).hexdigest() != TLC_SHA256:
        raise SystemExit(f"Checksum mismatch for {jar}")
    return jar


def check(name, design, mutation, max_lsn, *, expected=None):
    case = ROOT / ".results" / name
    case.mkdir(parents=True, exist_ok=True)
    config = case / "Commit.cfg"
    laws = (expected,) if expected else INVARIANTS
    trace_acceptance = "TRUE" if name.startswith("witness-") else "FALSE"
    invariants = "".join(f"INVARIANT {law}\n" for law in laws)
    config.write_text(
        "INIT Init\nNEXT Next\n"
        f'CONSTANT Design = "{design}"\nCONSTANT Mutation = "{mutation}"\n'
        f"CONSTANT MaxLsn = {max_lsn}\n"
        f"CONSTANT TraceAcceptance = {trace_acceptance}\n{invariants}", encoding="utf-8"
    )
    command = [
        JAVA, "-Xmx512m", "-XX:+UseParallelGC", "-jar", str(checker_jar()),
        "-workers", "1", "-fp", "0", "-deadlock",
        "-metadir", str(case / "states"), "-config", str(config), "Commit.tla",
    ]
    (case / "command.txt").write_text(shlex.join(command) + "\n", encoding="utf-8")
    log = case / "tlc.log"
    try:
        with log.open("w", encoding="utf-8") as output:
            result = subprocess.run(
                command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                timeout=60, check=False,
            )
    except subprocess.TimeoutExpired:
        raise SystemExit(f"{name}: exceeded 60 seconds; see {log}") from None
    output = log.read_text(encoding="utf-8")
    errors = [line for line in output.splitlines() if line.startswith("Error:")]
    if expected:
        predicted = [
            f"Error: Invariant {expected} is violated.",
            "Error: The behavior up to this point is:",
        ]
        if result.returncode != 12 or errors != predicted:
            raise SystemExit(f"{name}: expected only {expected}, exit {result.returncode}; see {log}")
        steps = len(re.findall(r"^State \d+:", output, re.MULTILINE)) - 1
        print(f"{name}: reached {expected} in {steps} transitions", flush=True)
    else:
        counts = re.search(r"(\d+) states generated, (\d+) distinct states found, 0 states left", output)
        if result.returncode != 0 or errors or not counts or "No error has been found" not in output:
            raise SystemExit(f"{name}: expected complete clean exploration; see {log}")
        print(f"{name}: {counts[2]} distinct states", flush=True)


def main():
    java_version = subprocess.run([JAVA, "-version"], check=True, capture_output=True, text=True)
    print(java_version.stderr.splitlines()[0], flush=True)
    print(f"TLC {TLC_VERSION}, SHA-256 {TLC_SHA256}", flush=True)
    for mutation, law, designs in CONTROLS:
        for design in designs:
            check(f"control-{design}-{mutation}", design, mutation, 2, expected=law)
    for bound in (2, 3):
        for design in DESIGNS:
            check(f"baseline-{design}-{bound}", design, "none", bound)
    for design in DESIGNS:
        for witness in WITNESSES:
            check(f"witness-{design}-{witness}", design, "none", 2, expected=witness)


if __name__ == "__main__":
    main()
