#!/usr/bin/env python3
"""Capture the ordered-group executions and check every trace in Lean."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


LEAN = Path(__file__).resolve().parent
ROOT = LEAN.parents[1]
TRACES = {
    "ordered-leadership.trace",
    "ordered-restart.trace",
    "surviving-group-repair.trace",
    "withdrawal-compaction-repair.trace",
    "withdrawn-hold-owners.trace",
}


def lean_check(lake, trace, expected=None):
    result = subprocess.run(
        [lake, "env", "lean", "--run", "check_prefix_trace.lean", str(trace)],
        cwd=LEAN,
        capture_output=True,
        text=True,
    )
    if expected is None:
        if result.returncode != 0:
            raise RuntimeError(f"{trace.name}: {result.stderr.strip() or result.stdout.strip()}")
        print(f"{trace.name}: {result.stdout.strip()}", flush=True)
    elif result.returncode != 1 or result.stderr.strip() != expected:
        raise RuntimeError(f"{trace.name}: expected {expected!r}, got {result}")
    else:
        print(f"{trace.name}: rejected at {expected}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=str(Path.home() / ".elan/bin/lake"))
    parser.add_argument(
        "--cargo-wrapper",
        default=str(ROOT.parent / "codesign-agents" / "guarded-cargo.py"),
    )
    args = parser.parse_args()
    subprocess.run([args.lake, "build"], cwd=LEAN, check=True)
    results = LEAN / ".results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="prefix-traces-", dir=results))
    print(f"Evidence: {evidence}", flush=True)
    subprocess.run(
        [args.cargo_wrapper, "logkeeper", "test", "--locked", "--all-features",
         "--test", "ordered_group", "--test", "leadership", "--test", "faults"],
        cwd=ROOT,
        env={**os.environ, "LOGKEEPER_PREFIX_TRACE_DIR": str(evidence)},
        check=True,
    )

    traces = sorted(evidence.glob("*.trace"))
    if {trace.name for trace in traces} != TRACES:
        raise RuntimeError(f"expected five ordered traces, got {traces}")
    for trace in traces:
        lean_check(args.lake, trace)

    stale = evidence / "ordered-restart.reject"
    stale_line = len(stale.read_text().splitlines())
    lean_check(args.lake, stale, f"line {stale_line}: accept floor")

    repair = (evidence / "surviving-group-repair.trace").read_text().splitlines()
    install = next(i for i, event in enumerate(repair) if event.startswith("install "))
    fields = repair[install].split()
    fields[5] = str(int(fields[5]) + 1)
    repair[install] = " ".join(fields)
    substituted = evidence / "substituted-predecessor-image.reject"
    substituted.write_text("\n".join(repair) + "\n")
    lean_check(args.lake, substituted, f"line {install + 1}: installation changed predecessor image")


if __name__ == "__main__":
    main()
