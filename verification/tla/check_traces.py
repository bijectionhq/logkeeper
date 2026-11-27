#!/usr/bin/env python3
"""Replay NDJSON keeper traces through the pinned TLC model."""

import argparse
from collections import Counter
from copy import deepcopy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def java():
    candidates = [
        os.environ.get("JAVA_BIN"),
        shutil.which("java"),
        *sorted(Path.home().glob(".local/share/mise/installs/java/*/bin/java")),
    ]
    for exe in candidates:
        if exe and subprocess.run([exe, "-version"], capture_output=True).returncode == 0:
            return exe
    raise SystemExit("Install Java 17+ or set JAVA_BIN")


def tla(value):
    if isinstance(value, bool):
        return "TRUE" if value else "FALSE"
    if isinstance(value, int) and 0 <= value < 2**31:
        return str(value)
    if isinstance(value, str) and value.isascii():
        return json.dumps(value)
    if isinstance(value, list):
        return "<<" + ", ".join(map(tla, value)) + ">>"
    if isinstance(value, dict) and all(re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", k) for k in value):
        if not value:
            return "[x \\in {} |-> x]"
        return "[" + ", ".join(f"{k} |-> {tla(v)}" for k, v in value.items()) + "]"
    raise ValueError(f"cannot represent trace value in TLC: {value!r}")


def tla_set(values):
    return "{" + ", ".join(map(tla, sorted(values))) + "}"


def read(path):
    events = []
    with path.open() as source:
        for line in source:
            event = json.loads(line)
            if (set(event) != {"node", "stream", "kind", "data"}
                    or not re.fullmatch(r"[0-9a-f-]{36}", event["node"])
                    or not re.fullmatch(r"[0-9a-f]{32}", event["stream"])):
                raise ValueError(f"{path}:{len(events) + 1}: malformed trace event")
            events.append(event)
    if not events:
        raise ValueError(f"{path}: empty trace")
    return events


def check(exe, jar, label, events):
    """Return zero on acceptance, the rejected event number, or None on TLC failure."""
    with tempfile.TemporaryDirectory(prefix="lk-trace-tlc-",
                                     dir=os.environ.get("LOGKEEPER_TLC_SCRATCH")) as temp:
        temp = Path(temp)
        for filename in ["KeeperTrace.tla", "KeeperSafety.tla"]:
            shutil.copyfile(ROOT / filename, temp / filename)
        with (temp / "TraceInput.tla").open("w") as module:
            module.write("---- MODULE TraceInput ----\nEXTENDS Integers\n")
            module.write(f"TraceNodes == {tla_set({e['node'] for e in events})}\n")
            module.write(f"TraceStreams == {tla_set({e['stream'] for e in events})}\n")
            # TLC may evaluate an overridden tuple again on each access.
            # Limit each access to one block rather than the complete input.
            width = 64
            branches = []
            for start in range(0, len(events), width):
                block = f"Block{start // width}"
                module.write(f"{block} == <<\n")
                module.write(",\n".join(map(tla, events[start:start + width])))
                module.write("\n>>\n")
                branches.append(f"i \\in {start + 1}..{start + width} -> {block}[i - {start}]")
            module.write(f"EventCount == {len(events)}\n")
            module.write("TraceEvent(i) == CASE " + "\n [] ".join(branches) + "\n====\n")
        (temp / "Replay.tla").write_text(
            "---- MODULE Replay ----\nEXTENDS TraceInput, KeeperTrace\n====\n"
        )
        (temp / "Replay.cfg").write_text(
            "INIT Init\nNEXT Next\n"
            "CONSTANTS\n TraceLength <- EventCount\n EventAt <- TraceEvent\n Nodes <- TraceNodes\n Streams <- TraceStreams\n"
        )
        log = temp / "tlc.log"
        with log.open("w") as output:
            result = subprocess.run(
                [exe, "-Xmx768m", "-Xss8m", "-XX:+UseParallelGC", "-jar", jar,
                 "-workers", "1", "-metadir", temp / "states", "Replay.tla"],
                cwd=temp, stdout=output, stderr=subprocess.STDOUT,
            )
        if result.returncode == 0:
            with log.open() as output:
                if any(re.search(rf"\b{len(events) + 1} distinct states found, 0 states left on queue", line)
                       for line in output):
                    print(f"{label}: accepted {len(events)} events", flush=True)
                    return 0
            print(f"{label}: TLC did not report visiting all {len(events) + 1} states",
                  flush=True)
            return None

        position = None
        with log.open() as output:
            for line in output:
                match = re.search(r"^/\\ position = (\d+)\s*$", line)
                if match:
                    position = int(match[1])
            if result.returncode == 11 and position is not None and position < len(events):
                print(f"{label}:{position + 1}: rejected {json.dumps(events[position])}",
                      flush=True)
                return position + 1
            else:
                output.seek(0)
                print(f"{label}: TLC failed with exit {result.returncode}", flush=True)
                print(output.read(8_000), flush=True)
        return None


def negative_controls(exe, jar, traces):
    """Require rejection at the edit, rather than at a later dependent event."""
    # A minority vote can give way to a different candidate's quorum vote
    # in the same term. A second quorum vote at that term must be rejected.
    a = "00000000-0000-0000-0000-000000000001"
    b = "00000000-0000-0000-0000-000000000002"
    stream = "0" * 31 + "1"
    def vote(candidate, committed):
        return dict(kind="Vote", node=a, stream=stream,
                    data=dict(votedFor=candidate, committed=committed, term=[0, 0, 0, 1]))
    split_vote = [dict(kind="Register", node=a, stream=stream, data={}),
                  vote(a, False), vote(b, True)]
    ok = check(exe, jar, "control-split-vote-reconciles", split_vote) == 0
    ok = (check(exe, jar, "control-two-committed-leaders", [*split_vote, vote(a, True)])
          == len(split_vote) + 1) and ok

    controls = {
        "BuildSnapshot": lambda d: d.update(index=d["index"] + 1),
        "Append": lambda d: d["entries"][0]["cut"].update(index=0),
        "Apply": lambda d: d["previous"].update(index=d["entry"]["cut"]["index"]),
        "AcceptPark": lambda d: d.update(lastIndex=d["lastIndex"] + 1),
        "LeaseGate": lambda d: d.update(permitted=not d["permitted"]),
        "LeaseGrant": lambda d: d.update(asked=d["epoch"] + 1),
        "RecoveryReady": lambda d: d.update(elapsed=d["wait"] - 1),
        "Upload": lambda d: d.update(head=d["last"] - 1),
    }
    for kind, mutate in controls.items():
        sample = next(((events, i) for events in traces for i, event in enumerate(events)
                       if event["kind"] == kind
                       and (kind != "RecoveryReady" or event["data"]["wait"] > 0)
                       and (kind != "LeaseGrant" or event["data"]["enforced"])), None)
        if sample is None:
            print(f"No {kind} event for negative control")
            ok = False
            continue
        events, index = sample
        changed = deepcopy(events[index])
        mutate(changed["data"])
        if check(exe, jar, f"control-{kind}", [*events[:index], changed]) != index + 1:
            print(f"Negative control {kind} failed to reject the altered event")
            ok = False
    return ok


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require", default="", help="comma-separated event kinds required across inputs")
    parser.add_argument("--controls", action="store_true", help="reject altered events from passing traces")
    parser.add_argument("traces", nargs="+", type=Path)
    args = parser.parse_args()
    exe = java()
    jar = subprocess.check_output([ROOT / "fetch-tla.sh"], text=True).strip()
    coverage = Counter()
    passed = True
    traces = []
    for path in args.traces:
        events = read(path)
        coverage.update(e["kind"] for e in events)
        if check(exe, jar, path.name, events) == 0:
            traces.append(events)
        else:
            passed = False
    if passed and args.controls:
        passed = negative_controls(exe, jar, traces)
    print("Trace coverage " + ", ".join(f"{k}={v}" for k, v in sorted(coverage.items())))
    missing = set(filter(None, args.require.split(","))) - coverage.keys()
    if missing:
        print("Missing required events: " + ", ".join(sorted(missing)))
    return 0 if passed and not missing else 1


if __name__ == "__main__":
    raise SystemExit(main())
