#!/usr/bin/env python3
"""Check the stream simulator's publication and incomplete Sync effects in Lean."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


LEAN = Path(__file__).resolve().parent
ROOT = LEAN.parents[1]
LAKE = Path.home() / ".elan/bin/lake"
CARGO = ROOT.parent / "codesign-agents/guarded-cargo.py"

# Common fields are followed by request fields, then publication epoch runs.
EPOCH, PROMISED, OWNER, LEARNER = range(3, 7)
SYNCED, TAIL, HEAD = 7, 9, 10
NEXT_SYNCED, NEXT_TAIL, NEXT_HEAD = 11, 13, 14
POSITION, PUBLISHED_HEAD, FIRST_RUN = 15, 16, 17
SYNC_FLOOR, SYNC_HEAD = 16, 17


def check_trace(path, *, require_reference=False, error=None):
    command = [LAKE, "env", "lean", "--run", "check_stream_trace.lean"]
    if require_reference:
        command.append("--require-reference")
    result = subprocess.run([*command, path], cwd=LEAN, capture_output=True, text=True)
    if error is not None:
        if result.returncode != 1 or result.stderr.strip() != f"line 2: {error}":
            raise RuntimeError(f"{path.name}: expected {error!r}, got {result}")
        print(f"{path.name}: rejected at {error}", flush=True)
    else:
        if result.returncode:
            raise RuntimeError(f"{path.name}: {result.stderr.strip() or result.stdout.strip()}")
        print(result.stdout.strip(), flush=True)
    return result.stdout


def witnesses(path):
    publication = sync = None
    with path.open() as trace:
        for row in trace:
            fields = row.split()
            if fields[0] == "seed":
                seed = fields[1]
            elif fields[0] == "publish" and publication is None:
                if (int(fields[HEAD]) < int(fields[PUBLISHED_HEAD])
                        and fields[EPOCH] not in fields[FIRST_RUN::3]):
                    publication = seed, fields
            elif fields[0] == "sync-part" and sync is None:
                if int(fields[SYNCED]) != int(fields[EPOCH]) + 1 and fields[TAIL] != fields[NEXT_TAIL]:
                    sync = seed, fields
            if publication and sync:
                return publication, sync
    raise RuntimeError("the corpus did not reach both projection witnesses")


def controls(trace, evidence):
    publication, sync = witnesses(trace)

    def fixture(name, witness, substitutions=()):
        seed, fields = witness
        fields = fields.copy()
        for index, value in substitutions:
            original = fields[index]
            fields[index] = str(value)
            if fields[index] == original:
                raise RuntimeError(f"{name}: no mutation in field {index}")
        path = evidence / f"{name}.trace"
        path.write_text(f"seed {seed}\n" + " ".join(fields) + "\n")
        return path

    _, publish = publication
    _, partial = sync
    for name, changes, error in (
        ("stale-promise", [(PROMISED, int(publish[EPOCH]) + 1)], "promise"),
        ("other-identity", [(OWNER, 0)], "authenticated identity"),
        ("unsynced-publication", [(SYNCED, 0), (NEXT_SYNCED, 0)], "publication requires a complete sync"),
        ("learner-publication", [(LEARNER, 1)], "publication requires a voter"),
        ("wrong-publication-position", [(POSITION, int(publish[POSITION]) + 1)], "publication position"),
        ("publication-beyond-tail", [(POSITION, int(publish[TAIL]) + 2),
                                     (PUBLISHED_HEAD, int(publish[TAIL]) + 1)],
         "publication beyond tail"),
        ("missing-epoch-run-start", [(FIRST_RUN + 1, int(publish[FIRST_RUN + 1]) + 1)], "epoch run coverage"),
        ("unpublished-head", [(NEXT_HEAD, publish[HEAD])], "publication effect"),
    ):
        check_trace(fixture(name, publication, changes), error=error)

    check_trace(fixture("bad-sync-floor", sync, [(SYNC_FLOOR, 0)]), error="incomplete sync floor")
    check_trace(fixture("bad-sync-head", sync, [(SYNC_HEAD, int(partial[NEXT_TAIL]) + 1)]),
                error="incomplete sync head")
    check_trace(fixture("bad-sync-tail", sync, [(NEXT_TAIL, int(partial[NEXT_TAIL]) + 1)]),
                error="incomplete sync effect")
    check_trace(fixture("inherited-publication", publication), require_reference=True,
                error="Study 119 inherited publication")
    check_trace(fixture("observable-incomplete-sync", sync), require_reference=True,
                error="Study 119 incomplete Sync tail")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seeds", type=int, default=10_000)
    parser.add_argument("--trace", type=Path, help="replay an existing trace")
    args = parser.parse_args()
    if args.seeds < 1:
        parser.error("--seeds must be positive")

    results = LEAN / ".results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="stream-trace-", dir=results))
    print(f"Evidence: {evidence}", flush=True)
    subprocess.run([LAKE, "build", "Logkeeper.StreamTrace"], cwd=LEAN, check=True)
    if args.trace is None:
        trace = evidence / "stream.trace"
        subprocess.run(
            [CARGO, "logkeeper", "test", "--locked", "--all-features", "--lib",
             "seeded_stream_journal", "--", "--nocapture"],
            cwd=ROOT, check=True, env={**os.environ, "LOGKEEPER_SIM_FIRST_SEED": "0",
                                      "LOGKEEPER_SIM_SEEDS": str(args.seeds),
                                      "LOGKEEPER_SIM_PUBLICATION_TRACE": str(trace)},
        )
    else:
        trace = args.trace.resolve()
    output = check_trace(trace)
    if args.trace is None and not output.splitlines()[-1].startswith(f"{args.seeds} seeds,"):
        raise RuntimeError(f"expected {args.seeds} seeds in {trace}")
    controls(trace, evidence)


if __name__ == "__main__":
    main()
