#!/usr/bin/env python3
"""Check the asynchronous prefix laws against three weakened Lean definitions."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "Logkeeper/AsyncPrefix.lean"

CONTROLS = {
    "skip-exact-promise": (
        "  AcceptAtPromise floor ballot\n",
        "  floor ≠ 0 ∧ floor ≤ ballot\n",
        "native_accept_requires_exact_promise",
    ),
    "count-a-voter-twice": (
        "  majorityCheck members voters = true\n",
        "  members.length < 2 * voters.length ∧ ∀ voter ∈ voters, voter ∈ members\n",
        "certificate_requires_distinct_voters",
    ),
    "keep-the-lower-ballot": (
        "if known.ballot < next.ballot then .ok (some next)",
        "if known.ballot < next.ballot then .ok (some known)",
        "recovery_pair_keeps_rank",
    ),
}


def lean(lake, path):
    return subprocess.run([lake, "env", "lean", str(path)], cwd=HERE, text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=str(Path.home() / ".elan/bin/lake"))
    args = parser.parse_args()
    subprocess.run([args.lake, "build"], cwd=HERE, check=True)
    directory = HERE / ".results"
    directory.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="async-group-controls-", dir=directory))
    print(f"Evidence: {evidence}", flush=True)
    original = SOURCE.read_text()
    for name, (old, new, law) in CONTROLS.items():
        if original.count(old) != 1:
            raise RuntimeError(f"{name}: mutation site changed")
        mutated = original.replace(old, new)
        path = evidence / f"{name}.lean"
        path.write_text(mutated)
        lines = mutated.splitlines()
        start = next(i for i, line in enumerate(lines, 1) if line.startswith(f"theorem {law} "))
        end = next(
            i for i, line in enumerate(lines, 1) if i > start and not line
        )
        result = lean(args.lake, path)
        output = result.stdout + result.stderr
        path.with_suffix(".log").write_text(output)
        errors = re.findall(r":(\d+):\d+: error(?:\([^\n]*?\))?:", output)
        if result.returncode != 1 or not errors or not start <= int(errors[0]) < end:
            raise RuntimeError(f"{name}: expected first error in {law}, see {path.with_suffix('.log')}")
        print(f"{name}: rejected at {law}", flush=True)


if __name__ == "__main__":
    main()
