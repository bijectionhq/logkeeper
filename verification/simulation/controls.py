#!/usr/bin/env python3
"""Disable one shipped guard per test build and require its named simulation failure."""

import argparse
import json
from pathlib import Path
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GUARD = Path.home() / "code/codesign-agents/guarded-cargo.py"
SIM = "stream::keeper::simulation::"
WIRE = SIM + "guards::wire_guards"
SEEDED = SIM + "seeded_stream_journal"
RULES = "src/stream/keeper/rules.rs"
STATE = "src/stream/keeper/state.rs"
WRITER = "src/stream/writer/"
ENGINE = "src/stream/keeper/mod.rs"


def verified_controls(area):
    manifest = ROOT / "verification/verus" / area / "area.json"
    return json.loads(manifest.read_text())["controls"]


def edit(file, find, replace):
    return dict(file=file, find=find, replace=replace)


def controls():
    keeper = verified_controls("stream_keeper")
    writer = verified_controls("stream_writer")
    for name, check in {
        "reuse-deleted-stream": "delete permitted stream reuse after restart",
        "seal-equal-other-identity": "equal epoch changed identities",
        "sync-overwrite-head": "sync replaced a committed record",
        "sync-regress-head": "sync regressed the head",
        "append-before-sync": "incomplete sync enabled an append",
        "append-conflicting-retry": "conflicting append counted as a retry",
        "trim-uncommitted": "trim crossed the head",
        "check-invent-tail": "check misreported the durable view",
        "read-accepted-tail": "read exposed an uncommitted record",
        "read-below-floor": "read admitted a position below floor",
    }.items():
        yield name, [keeper[name]["mutate"][0]], WIRE, check, 0

    yield (
        "one-keeper", writer["one-keeper"]["mutate"],
        SIM + "guards::one_acceptance_cannot_publish_a_head",
        "writer published a head without two acceptances", 0,
    )
    yield (
        "prefer-longer-over-newer", writer["prefer-longer-over-newer"]["mutate"],
        SIM + "guards::recovery_prefers_newer_synced_history",
        "recovery must prefer the newer synced history", 0,
    )

    yield (
        "ignore-tie-break", writer["ignore-tie-break"]["mutate"],
        SIM + "guards::head_covers_acknowledged_appends_with_a_lagging_keeper",
        "recovery must prefer the longer history at the same synced epoch", 0,
    )

    for name, file, old, new, check in [
        ("seal-lower", RULES, "    !has_promise || current < epoch || (current == epoch && same_identity)\n",
         "    !has_promise || current != epoch || same_identity\n", "lower epoch acquired a promise"),
        ("sync-promise", RULES, "if !promised(*epoch) {\n                    return fenced(state);\n                }\n                // A synced",
         "if !promised(*epoch) && false {\n                    return fenced(state);\n                }\n                // A synced",
         "sync ignored the promised identity"),
        ("sync-incomplete", STATE, "if complete {\n                    self.view.synced",
         "if complete || !complete {\n                    self.view.synced",
         "incomplete sync enabled an append"),
        ("append-promise", RULES, "    promised && synced\n", "    let _ = promised;\n    synced\n",
         "stale epoch admitted an append"),
        ("append-gap", RULES, "if *at > next {\n                    return refuse(Refusal::Gap",
         "if *at > next && false {\n                    return refuse(Refusal::Gap",
         "append admitted a gap"),
        ("append-no-retry", RULES, "    nonempty && last <= tail && identical\n",
         "    let _ = (nonempty, last, tail, identical);\n    false\n",
         "identical append retry was refused"),
        ("head-above-tail", RULES, "if *head > tail {\n                    return refuse(Refusal::AboveHead",
         "if *head > tail && false {\n                    return refuse(Refusal::AboveHead",
         "head publication exceeded the tail"),
        ("trim-epoch", RULES, "Request::Trim { epoch, through, .. } => {\n                if !promised(*epoch)",
         "Request::Trim { epoch, through, .. } => {\n                if !promised(*epoch) && false",
         "stale epoch trimmed a record"),
        ("delete-forgets", RULES, "    deleted || deleting\n", "    let _ = deleting;\n    deleted\n",
         "delete permitted stream reuse after restart"),
        ("learner-votes", RULES, "state.synced == Some(*epoch) && !state.learner,",
         "state.synced == Some(*epoch),", "synced learner voted before replacement"),
        ("replace-without-sync", RULES,
         "if state.synced != Some(*epoch) {\n                    return refuse(Refusal::NotSynced);\n                }\n                if state.ensemble == *to",
         "if false {\n                    return refuse(Refusal::NotSynced);\n                }\n                if state.ensemble == *to",
         "unsynced keeper installed a replacement"),
        ("replace-multiple-slots", RULES, "current && synced && member && changed == 1\n",
         "current && synced && member && changed > 0\n",
         "replacement changed multiple slots"),
    ]:
        edits = [edit(file, old, new)]
        if name == "replace-without-sync":
            edits.append(keeper[name]["mutate"][0])
        yield name, edits, WIRE, check, 0

    yield (
        "early-wal-reply",
        [edit(ENGINE,
              "        self.wal.write_round(&buffer)?;\n        for id in changed {",
              "        let sync = self.wal.write_round(&buffer);\n        for id in changed {"),
         edit(ENGINE, "            let _ = done.send(reply);\n        }\n        Ok(())",
              "            let _ = done.send(reply);\n        }\n        sync")],
        SIM + "guards::failed_sync_never_replies",
        "durability: a success reply escaped a failed WAL sync", 0,
    )
    yield (
        "append-reply-before-publication",
        [edit(WRITER + "append.rs", """                self.published(at)
                    .await
                    .map_err(|_| JournalError::Unavailable)?;
""", "")],
        SEEDED, "durability: successful append must cover two disks", 0,
    )
    yield (
        "seal-short", [edit(WRITER + "mod.rs", "        Ok(head)\n    }\n\n    fn active(",
                            "        Ok(Lsn(0))\n    }\n\n    fn active(")],
        SEEDED, "seal head missed an acknowledged append", 0,
    )
    yield (
        "observer-no-head-quorum",
        [edit(WRITER + "head.rs", ".count()\n                >= QUORUM)",
              ".count()\n                >= 1)")],
        SIM + "guards::head_covers_acknowledged_appends_with_a_lagging_keeper",
        "observer head missed an acknowledged append", 0,
    )
    yield (
        "writer-uses-local-head",
        [edit(WRITER + "head.rs", "    let opened = active.open_round();",
              "    if active.epoch.0 < u64::MAX { return Ok(active.head()); }\n"
              "    let opened = active.open_round();")],
        SIM + "guards::head_covers_acknowledged_appends_with_a_lagging_keeper",
        "writer head used a stale epoch", 0,
    )
    yield (
        "replacement-stale-route",
        [edit(RULES, "if *ensemble != state.ensemble {\n                    return wrong_ensemble(state);\n                }\n                let current",
              "if *ensemble != state.ensemble && false {\n                    return wrong_ensemble(state);\n                }\n                let current")],
        SEEDED, "replacement: a keeper promised an epoch on the stale ensemble", 9,
    )
    sweep = ROOT / "src/stream/keeper/sweep.rs"
    line = sweep.read_text()
    start = line.index("        self.copy(")
    end = line.index("        if history.synced", start)
    yield (
        "skip-survivor-repair", [edit(str(sweep.relative_to(ROOT)), line[start:end], "")],
        SEEDED, "replacement did not repair both survivors", 9,
    )
    append = ROOT / (WRITER + "append.rs")
    line = append.read_text()
    start = line.index("        let accepted = {", line.index("    async fn retry_committed("))
    end = line.index("        quorum(", start)
    yield (
        "retry-fills-gaps", [edit(str(append.relative_to(ROOT)), line[start:end],
                                 "        let accepted = self.ensemble.map(Some);\n")],
        SEEDED, "journal contract violated in seed 70", 70,
    )


def run(case, evidence):
    name, edits, test, check, seed = case
    originals = {}
    try:
        for change in edits:
            path = ROOT / change["file"]
            source = path.read_bytes()
            originals.setdefault(path, source)
            old = change["find"].encode()
            new = change["replace"].encode()
            if not old or old == new or source.count(old) != 1:
                raise ValueError(f"{name}: ambiguous mutation in {change['file']}")
            path.write_bytes(source.replace(old, new, 1))
        command = [str(GUARD), "logkeeper", "test", "--locked", "--all-features", "--lib",
                   test, "--", "--exact", "--nocapture"]
        env = dict(os.environ, LOGKEEPER_SIM_FIRST_SEED=str(seed), LOGKEEPER_SIM_SEEDS="1")
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, check=False)
    finally:
        for path, source in originals.items():
            path.write_bytes(source)
    (evidence / f"{name}.log").write_text(result.stdout)
    if result.returncode == 0 or f"test {test} ... FAILED" not in result.stdout or check not in result.stdout:
        raise ValueError(f"{name}: expected {check!r} from {test}, see {evidence}")
    print(f"{name}: {check}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*", help="control names (default: all)")
    args = parser.parse_args()
    cases = {case[0]: case for case in controls()}
    if unknown := set(args.names) - cases.keys():
        parser.error(f"unknown controls: {', '.join(sorted(unknown))}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "src/stream"],
                      cwd=ROOT).returncode:
        parser.error("commit stream sources before running these worktree-local mutations")
    results = HERE / ".results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="controls-", dir=results))
    print(f"Evidence: {evidence}", flush=True)
    selected = args.names or cases.keys()
    failures = []
    for name in selected:
        try:
            run(cases[name], evidence)
        except ValueError as error:
            failures.append(str(error))
            print(error, flush=True)
    print(f"{len(selected) - len(failures)} of {len(selected)} controls rejected at their named checks",
          flush=True)
    if failures:
        raise ValueError("simulation controls failed")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
