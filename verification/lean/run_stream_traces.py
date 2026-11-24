#!/usr/bin/env python3
"""Replay every keeper effect of the stream simulator against Study 119 in Lean.

The runner records the seeded simulator corpus, replays it with the Lean checker, then
mutates real rows so that each keeper guard and effect check rejects exactly one control.
"""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


LEAN = Path(__file__).resolve().parent
ROOT = LEAN.parents[1]
LAKE = Path.home() / ".elan/bin/lake"
CARGO = ROOT.parent / "codesign-agents/guarded-cargo.py"

FIXED = {"create": 3, "delete": 3, "seal": 4, "sync": 6, "append": 4, "trim": 2,
         "check": 1, "read": 2, "recover": 3, "replace": 7}
VIEW = ["promised", "owner", "synced", "floor", "tail", "head", "learner", "e0", "e1", "e2"]


class Tokens:
    def __init__(self, values):
        self.values, self.index = values, 0

    def next(self):
        self.index += 1
        return int(self.values[self.index - 1])

    def runs(self):
        return [[self.next() for _ in range(3)] for _ in range(self.next())]


def view(tokens):
    fields = {name: tokens.next() for name in VIEW}
    fields["runs"] = tokens.runs()
    return fields


def image(tokens):
    result = {"present": tokens.next(), "deleted": tokens.next(), "view": view(tokens)}
    result["staged"] = ({"floor": tokens.next(), "start": tokens.next(), "tail": tokens.next(),
                         "runs": tokens.runs()} if tokens.next() else None)
    return result


REPLIES = {0: 0, 1: 0, 3: 1, 4: 1, 5: 1, 8: 0, 9: 0, 10: 0, 11: 0, 12: 3}


def parse(line):
    verb, *values = line.split()
    tokens = Tokens(values)
    row = {"verb": verb, "serial": tokens.next(), "keeper": tokens.next(),
           "caller": tokens.next(), "before": image(tokens), "after": image(tokens)}
    if verb not in FIXED:
        return row
    row["fields"] = [tokens.next() for _ in range(FIXED[verb])]
    row["runs"] = tokens.runs() if verb == "sync" else []
    tag = tokens.next()
    row["reply"] = [tag]
    if tag in (2, 6):
        row["view"] = view(tokens)
    elif tag == 7:
        row["reply"] += [tokens.next(), tokens.next()]
        row["positions"] = [tokens.next() for _ in range(tokens.next())]
    else:
        row["reply"] += [tokens.next() for _ in range(REPLIES[tag])]
    assert tokens.index == len(values), line
    return row


def runs_text(runs):
    return [str(len(runs))] + [str(value) for run in runs for value in run]


def view_text(fields):
    return [str(fields[name]) for name in VIEW] + runs_text(fields["runs"])


def image_text(fields):
    words = [str(fields["present"]), str(fields["deleted"])] + view_text(fields["view"])
    staged = fields["staged"]
    if staged is None:
        return words + ["0"]
    return words + ["1", str(staged["floor"]), str(staged["start"]), str(staged["tail"])] \
        + runs_text(staged["runs"])


def text(row):
    words = [row["verb"], str(row["serial"]), str(row["keeper"]), str(row["caller"])]
    words += image_text(row["before"]) + image_text(row["after"])
    if row["verb"] in FIXED:
        words += [str(value) for value in row["fields"]]
        if row["verb"] == "sync":
            words += runs_text(row["runs"])
        words += [str(value) for value in row["reply"]]
        if "view" in row:
            words += view_text(row["view"])
        if "positions" in row:
            words += [str(len(row["positions"]))] + [str(p) for p in row["positions"]]
    return " ".join(words)


def check_trace(path, *, error=None, line=2):
    command = [LAKE, "env", "lean", "--run", "check_stream_trace.lean", path]
    result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True)
    if error is not None:
        if result.returncode != 1 or result.stderr.strip() != f"line {line}: {error}":
            raise RuntimeError(f"{path.name}: expected {error!r}, got {result}")
        print(f"{path.name}: rejected at {error}", flush=True)
    elif result.returncode:
        raise RuntimeError(f"{path.name}: {result.stderr.strip() or result.stdout.strip()}")
    else:
        print(result.stdout.strip(), flush=True)
    return result.stdout


def first(trace, predicate):
    seed = None
    with trace.open() as rows:
        for line in rows:
            if line.startswith("seed "):
                seed = line.split()[1]
                continue
            row = parse(line)
            if predicate(row):
                return seed, row
    raise RuntimeError("the corpus has no row for a control")


def accepted(row):
    return row["verb"] not in FIXED or row["reply"][0] not in (0, 11, 12)


def kind(verb, test=lambda row: True):
    return lambda row: row["verb"] == verb and accepted(row) and test(row)


def staged_sync(row):
    return row["fields"][5] == 0 and row["before"]["view"]["synced"] != row["fields"][0] + 1


def complete_sync(row):
    return row["fields"][5] == 1 and row["before"]["view"]["synced"] != row["fields"][0] + 1


def new_record(row):
    return row["fields"][2] > 0 and row["fields"][1] == row["before"]["view"]["tail"] + 1


def publication(row):
    return row["fields"][2] == 0 and row["after"]["view"]["head"] > row["before"]["view"]["head"]


def inherited(row):
    epoch = row["fields"][0]
    return publication(row) and all(run[0] != epoch for run in row["before"]["view"]["runs"])


def clip(runs, first, last):
    return [[epoch, max(a, first), min(b, last)] for epoch, a, b in runs if max(a, first) <= min(b, last)]


def expose(row):
    """The former keeper: an incomplete Sync replaces the visible history in place."""
    after, staged = row["after"], row["after"]["staged"]
    view = after["view"]
    runs = clip(view["runs"], view["floor"], staged["start"] - 1)
    for run in staged["runs"]:
        if runs and runs[-1][0] == run[0] and runs[-1][2] + 1 == run[1]:
            runs[-1][2] = run[2]
        else:
            runs.append(list(run))
    floor = max(view["floor"], staged["floor"])
    view.update(floor=floor, tail=staged["tail"], runs=clip(runs, floor, staged["tail"]))
    after["staged"] = None


def stage(image):
    """Give an image an incomplete Sync of one record after its tail."""
    tail = image["view"]["tail"] + 1
    image["staged"] = {"floor": image["view"]["floor"], "start": tail, "tail": tail,
                       "runs": [[image["view"]["promised"], tail, tail]]}


def edit(change):
    def apply(row):
        change(row)
        return row
    return apply


def both(field, value):
    def change(row):
        row["before"]["view"][field] = value(row)
        row["after"]["view"][field] = value(row)
    return change


CONTROLS = [
    # name, row selector, mutation, expected rejection
    ("image-bounds", kind("check"), lambda r: both("head", lambda r: r["before"]["view"]["tail"] + 1)(r),
     "keeper image bounds"),
    ("reopen-loses-state", kind("reopen", lambda r: r["before"]["view"]["tail"] > 0),
     lambda r: r["after"]["view"].update(head=0, tail=0, runs=[], floor=1), "reopen restores the durable image"),
    ("refusal-mutates", lambda r: r["verb"] == "append" and r["reply"][0] == 0,
     lambda r: r["after"]["view"].update(promised=r["after"]["view"]["promised"] + 1),
     "stutter changed the image"),
    ("create-wrong-ensemble", kind("create", lambda r: not r["before"]["present"]),
     lambda r: r["after"]["view"].update(e0=99), "create effect"),
    ("delete-no-tombstone", kind("delete", lambda r: not r["before"]["deleted"]),
     lambda r: r["after"].update(deleted=0), "delete installs a tombstone"),
    ("read-after-delete", kind("read"),
     lambda r: (r["before"].update(deleted=1), r["after"].update(deleted=1)), "request on an absent or deleted stream"),
    ("seal-lower-epoch", kind("seal", lambda r: r["before"]["view"]["promised"] < r["fields"][0] + 1),
     lambda r: r["fields"].__setitem__(0, r["before"]["view"]["promised"] - 2 if r["before"]["view"]["promised"] >= 2 else 0)
     if r["before"]["view"]["promised"] >= 2 else (both("promised", lambda r: r["fields"][0] + 2)(r)), "seal fence"),
    ("seal-other-identity", kind("seal", lambda r: r["before"]["view"]["promised"] == r["fields"][0] + 1),
     lambda r: both("owner", lambda r: r["caller"] + 7)(r), "seal fence"),
    ("seal-wrong-ensemble", kind("seal"), lambda r: r["fields"].__setitem__(1, 99), "seal ensemble"),
    ("seal-keeps-staging", kind("seal", lambda r: r["before"]["view"]["promised"] != r["fields"][0] + 1),
     lambda r: (stage(r["before"]), r.__setitem__("after", {**r["after"], "staged": r["before"]["staged"]})),
     "seal effect"),
    ("seal-reports-staging", kind("seal", lambda r: r["before"]["view"]["promised"] == r["fields"][0] + 1
                                  and r["reply"][0] == 2),
     lambda r: (stage(r["before"]), stage(r["after"]), r["view"].update(tail=r["before"]["staged"]["tail"])),
     "seal reply reports the vote"),
    ("sync-other-identity", kind("sync"), lambda r: both("owner", lambda r: r["caller"] + 7)(r), "sync promise"),
    ("sync-floor-above-start", kind("sync", staged_sync),
     lambda r: r["fields"].__setitem__(1, r["fields"][2] + 1), "sync floor"),
    ("sync-gap", kind("sync", lambda r: staged_sync(r) and r["fields"][1] < r["fields"][2]),
     lambda r: r["fields"].__setitem__(2, r["fields"][2] + 5), "sync gap"),
    ("sync-runs", kind("sync", lambda r: staged_sync(r) and r["runs"]),
     lambda r: r["runs"][0].__setitem__(1, r["runs"][0][1] + 1), "sync epoch runs"),
    ("sync-head-beyond-tail", kind("sync", complete_sync),
     lambda r: r["fields"].__setitem__(4, r["after"]["view"]["tail"] + 1), "sync head"),
    ("observable-incomplete-sync", kind("sync", lambda r: staged_sync(r) and r["after"]["staged"]),
     expose, "staged sync changed the view"),
    ("staged-wrong-record-epoch", kind("sync", lambda r: staged_sync(r) and r["after"]["staged"]["runs"]),
     lambda r: r["after"]["staged"]["runs"][-1].__setitem__(0, r["after"]["staged"]["runs"][-1][0] + 9),
     "staged sync effect"),
    ("complete-sync-unsynced", kind("sync", complete_sync),
     lambda r: r["after"]["view"].update(synced=r["before"]["view"]["synced"]), "complete sync effect"),
    ("complete-sync-keeps-staging", kind("sync", lambda r: complete_sync(r) and r["before"]["staged"]),
     lambda r: r.__setitem__("after", {**r["after"], "staged": r["before"]["staged"]}), "complete sync effect"),
    ("sync-reply-tail", kind("sync", complete_sync),
     lambda r: r["reply"].__setitem__(1, r["reply"][1] + 1), "sync reply tail"),
    ("synced-sync-with-records", kind("sync", lambda r: r["fields"][5] == 0
                                      and r["before"]["view"]["synced"] == r["fields"][0] + 1),
     lambda r: r["fields"].__setitem__(3, 1), "synced sync form"),
    ("floor-installation-lost", kind("sync", lambda r: r["fields"][5] == 0
                                     and r["before"]["view"]["synced"] == r["fields"][0] + 1
                                     and r["after"] != r["before"]),
     lambda r: r.__setitem__("after", r["before"]), "floor installation effect"),
    ("replace-unsynced", kind("replace", lambda r: r["reply"][0] == 9),
     lambda r: both("synced", lambda r: 0)(r), "replace requires a synced promise"),
    ("replace-two-members", kind("replace", lambda r: r["before"]["view"]["e0"] != r["fields"][4]
                                 or r["before"]["view"]["e1"] != r["fields"][5]),
     lambda r: (r["fields"].__setitem__(4, 97), r["fields"].__setitem__(5, 98)), "replace ensemble"),
    ("replace-keeps-learner", kind("replace", lambda r: r["after"] != r["before"]),
     lambda r: r["after"]["view"].update(learner=1), "replace effect"),
    ("wrong-ensemble-reports-stale-route", lambda r: r.get("reply", [0])[0] == 12,
     lambda r: r["reply"].__setitem__(1, 97), "WrongEnsemble reports current ensemble"),
    ("disk-loss-keeps-image", kind("lose"), lambda r: r.__setitem__("after", r["before"]),
     "disk loss clears the image"),
    ("append-stale-promise", kind("append"), lambda r: both("promised", lambda r: r["fields"][0] + 2)(r),
     "append promise"),
    ("append-unsynced", kind("append"), lambda r: both("synced", lambda r: 0)(r), "append requires a synced voter"),
    ("append-learner", kind("append"), lambda r: both("learner", lambda r: 1)(r), "append requires a synced voter"),
    ("append-gap", kind("append", new_record), lambda r: r["fields"].__setitem__(1, r["fields"][1] + 1),
     "append position"),
    ("append-head-beyond-tail", kind("append", new_record),
     lambda r: r["fields"].__setitem__(3, r["after"]["view"]["tail"] + 1), "append head beyond tail"),
    ("append-wrong-epoch", kind("append", new_record),
     lambda r: r["after"]["view"]["runs"][-1].__setitem__(0, r["fields"][0] + 9), "append effect"),
    ("publication-beyond-tail", kind("append", publication),
     lambda r: (r["fields"].__setitem__(3, r["before"]["view"]["tail"] + 1),
                r["fields"].__setitem__(1, r["before"]["view"]["tail"] + 1)), "publication beyond tail"),
    ("unpublished-head", kind("append", publication),
     lambda r: r["after"]["view"].update(head=r["before"]["view"]["head"]), "publication effect"),
    ("append-reply-tail", kind("append", lambda r: r["reply"][0] == 4),
     lambda r: r["reply"].__setitem__(1, r["reply"][1] + 1), "append reply tail"),
    ("trim-stale-promise", kind("trim"), lambda r: both("promised", lambda r: r["fields"][0] + 2)(r), "trim promise"),
    ("trim-learner", kind("trim"), lambda r: both("learner", lambda r: 1)(r), "trim requires a synced voter"),
    ("trim-above-head", kind("trim"), lambda r: r["fields"].__setitem__(1, r["before"]["view"]["head"] + 1),
     "trim beyond head"),
    ("trim-keeps-floor", kind("trim", lambda r: r["after"]["view"]["floor"] > r["before"]["view"]["floor"]),
     lambda r: r.__setitem__("after", r["before"]), "trim effect"),
    ("check-misreports", kind("check"), lambda r: r["view"].update(synced=r["view"]["synced"] + 1),
     "check reports the view"),
    ("read-uncommitted", kind("read", lambda r: r["before"]["view"]["head"] < r["before"]["view"]["tail"]
                              and r["positions"]),
     lambda r: r["positions"].extend(range(r["positions"][-1] + 1, r["before"]["view"]["tail"] + 1)),
     "read returns committed records"),
    ("recover-without-promise", kind("recover"), lambda r: both("owner", lambda r: r["caller"] + 7)(r),
     "recover returns accepted records"),
]


def controls(trace, evidence):
    for name, select, mutate, error in CONTROLS:
        seed, row = first(trace, select)
        original = text(row)
        mutate(row)
        mutated = text(row)
        if mutated == original:
            raise RuntimeError(f"{name}: the mutation changed nothing")
        path = evidence / f"{name}.trace"
        path.write_text(f"seed {seed}\n{mutated}\n")
        check_trace(path, error=error)
    seed, row = first(trace, kind("replace", lambda r: r["before"]["view"]["learner"] and
                                 not r["after"]["view"]["learner"]))
    path = evidence / "learner-without-survivor-installs.trace"
    path.write_text(f"seed {seed}\n{text(row)}\n")
    check_trace(path, error="learner installs after both survivors")
    seed, row = first(trace, kind("lose"))
    reopened = {**row, "verb": "reopen", "before": row["after"]}
    path = evidence / "lost-identity-returns.trace"
    path.write_text(f"seed {seed}\n{text(row)}\n{text(reopened)}\n")
    check_trace(path, error="lost keeper identity cannot return", line=3)
    seed, row = first(trace, kind("replace", lambda r: r["after"] != r["before"]))
    before = row["after"]
    _, *rosters = row["fields"]
    reinstalled = {**row, "before": before, "reply": [12] + rosters[3:]}
    path = evidence / "wrong-ensemble-rejects-replace-retry.trace"
    path.write_text(f"seed {seed}\n{text(reinstalled)}\n")
    check_trace(path, error="WrongEnsemble follows Replace promise and retry checks")
    seed, row = first(trace, kind("append", inherited))
    print(f"inherited publication: seed {seed}, RPC {row['serial']}, keeper {row['keeper']} "
          "is a Study 119 publication step", flush=True)


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
