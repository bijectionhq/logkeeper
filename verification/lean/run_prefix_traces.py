#!/usr/bin/env python3
"""Capture the ordered-group executions and check every trace in Lean."""

import argparse
import os
import random
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

FAULTS = ("prepare-loss", "accept-loss", "reply-loss", "duplicate", "cancel", "late")


def generate_schedules(seed, repetitions, path):
    randomizer = random.Random(seed)
    rows = []
    for index in range(repetitions):
        faults = list(FAULTS)
        randomizer.shuffle(faults)
        for fault in faults:
            name = f"generated-{index:02d}-{fault}"
            peers = randomizer.sample(range(3), 3)
            delay = randomizer.randint(1, 5)
            restart = index % 2 == 0
            rows.append((name, fault, *peers, delay, int(restart)))
    path.write_text("".join(" ".join(map(str, row)) + "\n" for row in rows))
    return {row[0] + ".trace" for row in rows}


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
        return len(trace.read_text().splitlines())
    elif result.returncode != 1 or result.stderr.strip() != expected:
        raise RuntimeError(f"{trace.name}: expected {expected!r}, got {result}")
    else:
        print(f"{trace.name}: rejected at {expected}", flush=True)


def checker_controls(lake, evidence):
    stale = evidence / "ordered-restart.reject"
    stale_line = len(stale.read_text().splitlines())
    lean_check(lake, stale, f"line {stale_line}: accept floor")

    def mutate(events, index, fields, name, reason):
        changed = events.copy()
        changed[index] = " ".join(fields)
        path = evidence / f"{name}.reject"
        path.write_text("\n".join(changed) + "\n")
        lean_check(lake, path, f"line {index + 1}: {reason}")

    events = (evidence / "ordered-restart.trace").read_text().splitlines()
    choice = next(i for i, event in enumerate(events) if event.startswith("choice "))
    fields = events[choice].split()
    fields[5:] = [fields[5]] * len(fields[5:])
    mutate(events, choice, fields, "duplicate-certificate-voter", "chosen majority")

    reports = {}
    for index, event in enumerate(events):
        fields = event.split()
        if fields[0] == "promise" and len(fields) == 8:
            _, group, voter, rnd, nonce, *reported = fields
            reports[group, rnd, nonce, voter] = reported
        if fields[0] == "prepared":
            _, group, rnd, nonce, wr, wn, _, *voters = fields
            lower = next((
                reports[group, rnd, nonce, voter]
                for voter in voters
                if (group, rnd, nonce, voter) in reports
                and tuple(map(int, reports[group, rnd, nonce, voter][:2])) < (int(wr), int(wn))
            ), None)
            if lower is not None:
                fields[4:7] = lower
                mutate(events, index, fields, "lower-recovery-winner", "recovery rank")
                break
    else:
        raise RuntimeError("ordered-restart did not record competing recovery ranks")

    repair = (evidence / "surviving-group-repair.trace").read_text().splitlines()
    install = next(i for i, event in enumerate(repair) if event.startswith("install "))
    fields = repair[install].split()
    fields[5] = str(int(fields[5]) + 1)
    mutate(repair, install, fields, "substituted-predecessor-image",
           "installation changed predecessor image")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=str(Path.home() / ".elan/bin/lake"))
    parser.add_argument(
        "--cargo-wrapper",
        default=str(ROOT.parent / "codesign-agents" / "guarded-cargo.py"),
    )
    parser.add_argument("--seed", type=int, default=20261124)
    parser.add_argument("--repetitions", type=int, default=4)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    subprocess.run([args.lake, "build"], cwd=LEAN, check=True)
    results = LEAN / ".results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="prefix-traces-", dir=results))
    print(f"Evidence: {evidence} (seed {args.seed})", flush=True)
    schedules = evidence / "schedules.txt"
    generated = generate_schedules(args.seed, args.repetitions, schedules)
    subprocess.run(
        [args.cargo_wrapper, "logkeeper", "test", "--locked", "--all-features",
         "--test", "ordered_group", "--test", "leadership", "--test", "faults"],
        cwd=ROOT,
        env={
            **os.environ,
            "LOGKEEPER_PREFIX_TRACE_DIR": str(evidence),
            "LOGKEEPER_PREFIX_SCHEDULES": str(schedules),
        },
        check=True,
    )

    traces = sorted(evidence.glob("*.trace"))
    if {trace.name for trace in traces} != TRACES | generated:
        raise RuntimeError(f"unexpected trace set: {traces}")
    generated_events = 0
    fixed_events = 0
    for trace in traces:
        count = lean_check(args.lake, trace)
        if trace.name in generated:
            generated_events += count
        else:
            fixed_events += count
    print(f"Generated: {len(generated)} traces, {generated_events} events; "
          f"fixed: {len(TRACES)} traces, {fixed_events} events", flush=True)

    checker_controls(args.lake, evidence)


if __name__ == "__main__":
    main()
