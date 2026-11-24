#!/usr/bin/env python3
"""Disable one shipped guard per test build and require its named simulation failure."""

import argparse
import json
from pathlib import Path
import os
import re
import shutil
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
PROPOSER = "src/stream/proposer/"
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
        "reuse-sweep-proposal",
        [edit("src/stream/keeper/sweep.rs", "proposal: uuid::Uuid::new_v4().as_u128(),", "proposal: 1,")],
        "stream::keeper::tests::sweeper_uses_two_survivors_and_activates_the_trimmed_learner",
        "another sweep plan re-elected the same epoch", 0,
    )
    yield (
        "expect-staged-tail-in-sweep",
        [edit(PROPOSER + "sweep.rs", "let visible_tail = if complete {",
              "let visible_tail = if complete || !complete {")],
        "stream::keeper::tests::sweeper_transfers_multiple_pages_across_successive_replacements",
        "sweep rejected its incomplete Sync reply", 0,
    )
    yield (
        "count-stale-roster-head",
        [edit(PROPOSER + "head.rs", "                && view.ensemble == ensemble\n", "")],
        "stream::keeper::tests::sweeper_transfers_multiple_pages_across_successive_replacements",
        "stale roster supplied a fresh head", 0,
    )
    yield (
        "send-unassigned-retry",
        [edit(WRITER + "append.rs", "                let retained =\n",
              "                if keeper.0 != 0 {\n"
              "                    return self.send_append(keeper, at, vec![payload.clone()], at).await;\n"
              "                }\n"
              "                let retained =\n")],
        "stream::writer::tests::committed_retry_does_not_send_unassigned_bytes",
        "committed retry sent unassigned bytes", 0,
    )
    yield (
        "count-one-keeper-twice-for-trim",
        [edit(PROPOSER + "mutation.rs", "Send::new(slot, ensemble[slot as usize], request)",
              "Send::new(slot, if matches!(request, Request::Trim { .. }) { ensemble[0] } else { ensemble[slot as usize] }, request)")],
        "stream::writer::tests::trim_and_delete_wait_for_a_distinct_durable_reply",
        "Trim returned without the second keeper reply", 0,
    )
    yield (
        "count-one-keeper-twice-for-delete",
        [edit(PROPOSER + "mutation.rs", "Send::new(slot, ensemble[slot as usize], request)",
              "Send::new(slot, if matches!(request, Request::Delete { .. }) { ensemble[0] } else { ensemble[slot as usize] }, request)")],
        "stream::writer::tests::trim_and_delete_wait_for_a_distinct_durable_reply",
        "Delete returned without the second keeper reply", 0,
    )
    yield (
        "poll-past-read-deadline",
        [edit(PROPOSER + "driver.rs", "timeout_at(started + deadline, call)",
              "timeout_at(started + deadline + RPC_TIMEOUT, call)")],
        "stream::writer::tests::a_delayed_poll_reply_cannot_extend_the_read_wait",
        "the first poll exhausted the wait budget", 0,
    )
    yield (
        "return-abandoned-read-page",
        [edit(PROPOSER + "read.rs", "let result = chunk(response, at).and_then(|next| {",
              """let response = match response {
                    Ok(Reply::Records { .. }) => response,
                    _ => return Effects::Complete(Ok(page)),
                };
                let result = chunk(response, at).and_then(|next| {""")],
        "stream::writer::tests::a_lost_read_chunk_discards_the_partial_page_before_fallback",
        "fallback must use its own first reply", 0,
    )
    yield (
        "ignore-seal-proposal",
        [edit(RULES, "seal_matches(current == epoch && owner == view.identity, *id, *proposal)",
              "current == epoch && owner == view.identity")],
        "stream::keeper::tests::a_checkpoint_retains_the_seal_proposal",
        "reopened keeper accepted a different proposal", 0,
    )
    yield (
        "discard-uncertain-append",
        [edit(PROPOSER + "append.rs", "if failed_at_first && first > self.uncertain_through {",
              "if failed_at_first {")],
        "stream::writer::tests::capacity_refusals_do_not_release_a_timed_out_append",
        "capacity refusals released a position with an unanswered append", 0,
    )
    yield (
        "decode-missing-seal-proposal",
        [edit("src/stream/codec.rs", "decode::<RequestFrame>(body)?.try_into()", """{
            let mut frame = decode::<RequestFrame>(body)?;
            if let Some(RequestBody::Seal(seal)) = &mut frame.body
                && seal.proposal.is_empty()
            {
                seal.proposal = encode_id(0);
            }
            frame.try_into()
        }""")],
        "stream::codec::tests::requires_a_proposal_id_on_seal_and_in_a_promise",
        "decoded a Seal without a valid proposal ID", 0,
    )
    yield (
        "decode-missing-promise-proposal",
        [edit("src/stream/codec.rs", "decode_id(&promise.proposal)", "if promise.proposal.is_empty() { Ok(0) } else { decode_id(&promise.proposal) }")],
        "stream::codec::tests::requires_a_proposal_id_on_seal_and_in_a_promise",
        "decoded a reply promise without a valid proposal ID", 0,
    )
    yield (
        "charge-append-duplicate",
        [edit(RULES, "                if *at < next || records.is_empty() {",
              """                if *at < next && !records.is_empty() && *head == state.head
                    && let Some(error) = capacity(records, view.retained_bytes, state.floor, limits)
                {
                    return error;
                }
                if *at < next || records.is_empty() {""")],
        "stream::keeper::tests::append_requires_current_sync_next_position_or_an_identical_retry",
        "a retained identical retry charged quota", 0,
    )
    yield (
        "reply-before-capacity-redelivery",
        [edit("src/stream/keeper/simulation/network.rs", "(duplicate && capacity)",
              "(duplicate && capacity && false)")],
        SIM + "guards::capacity_reply_is_uncertain_while_a_duplicate_can_arrive",
        "a duplicated capacity refusal escaped while redelivery was pending", 0,
    )
    yield (
        "sync-past-seed",
        [edit(PROPOSER + "recovery.rs", "            .min(Lsn(self.recovery.tail().0 + 1))\n", "")],
        "stream::writer::tests::unsynced_keeper_installs_the_seed_before_advancing_past_it",
        "lagging keeper must join after the floor passes the seed", 0,
    )
    yield (
        "reuse-seal-proposal",
        [edit(WRITER + "mod.rs", "proposal: uuid::Uuid::new_v4().as_u128(),", "proposal: 1,")],
        "stream::writer::tests::a_new_writer_with_the_same_identity_cannot_reseal",
        "independent writer re-elected an existing epoch", 0,
    )
    yield (
        "one-keeper", writer["one-keeper"]["mutate"],
        SIM + "guards::one_acceptance_cannot_publish_a_head",
        "writer published a head without two acceptances", 0,
    )
    yield (
        "ignore-tail", writer["ignore-tail"]["mutate"],
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
        ("sync-incomplete", STATE, "if complete {\n                    self.install(staging, head);",
         "if complete || !complete {\n                    self.install(staging, head);",
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
         "    } else if !synced {\n        ReplaceDecision::NotSynced",
         "    } else if false {\n        ReplaceDecision::NotSynced",
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
        [edit(PROPOSER + "append.rs", "let Some(result) = self.publication(at) else {",
              "let Some(result) = Some(Ok(())) else {")],
        SEEDED, "durability: successful append must cover two disks", 0,
    )
    yield (
        "seal-short", [edit(WRITER + "mod.rs", "        Ok(head)\n", "        Ok(Lsn(0))\n")],
        SEEDED, "journal contract violated in seed 0", 0,
    )
    yield (
        "observer-no-head-quorum",
        [edit(PROPOSER + "head.rs", """        head_quorum(
            eligible(views, candidate)
                .filter(|view| view.head >= index)
                .count(),
        )""", """        eligible(views, candidate).any(|view| view.head >= index)""")],
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
        SEEDED, "replacement: split install admitted a stale seal", 9,
    )
    yield (
        "skip-survivor-repair",
        [edit(PROPOSER + "sweep.rs", "        self.copy(other, target, head)",
              "        self.copied(other)")],
        SEEDED, "replacement did not repair both survivors", 9,
    )
    yield (
        "retry-fills-gaps",
        [edit(WRITER + "append.rs", """        let accepted = {
            let state = self.state.lock();
            std::array::from_fn::<_, 3, _>(|index| {
                state
                    .proposer
                    .accepted(index, at)
                    .then_some(self.ensemble[index])
            })
        };""", "        let accepted = self.ensemble.map(Some);"),
         edit(WRITER + "append.rs", """                let retained =
                    recovery::fetch(&self.io, keeper, self.stream, self.epoch, at).await?;
                if retained != *payload {
                    return Err(JournalError::Conflict { head: self.head() });
                }
                self.io.publish(keeper, self.stream, self.epoch, at).await""",
              "                    self.send_append(keeper, at, vec![payload.clone()], at).await")],
        SIM + "guards::conflicting_retry_cannot_publish_on_a_lagging_keeper",
        "conflicting retry installed bytes on a lagging keeper", 0,
    )


# The control sites are in rustfmt-formatted named functions. Their closing
# braces share the declaration's indentation.
FUNCTION = re.compile(r"^([ ]*)(?:pub(?:\([^)]*\))? )?(?:async )?fn \w+\(", re.M)
CONTROL_ENV = "LOGKEEPER_SIM_CONTROL"


def instrument(source, edits):
    """Give each affected body one isolated alternative per control."""
    bodies = {}
    functions = list(FUNCTION.finditer(source))
    for name, changes in edits.items():
        for change in changes:
            old, new = change["find"], change["replace"]
            if not old or old == new or source.count(old) != 1:
                raise ValueError(f"{name}: ambiguous mutation in {change['file']}")
            position = source.index(old)
            function = next((f for f in reversed(functions) if f.end() < position), None)
            if function is None:
                raise ValueError(f"{name}: mutation has no containing function")
            start = source.index("{", function.end()) + 1
            closing = re.compile(r"^" + function[1] + r"\}", re.M).search(source, start)
            if closing is None or not start <= position < position + len(old) <= closing.end():
                raise ValueError(f"{name}: mutation crosses a function boundary")
            bodies.setdefault((start, closing.end()), {}).setdefault(name, []).append((old, new))
    for (start, stop), variants in sorted(bodies.items(), reverse=True):
        original = source[start:stop]
        alternatives = []
        for name, changes in variants.items():
            altered = original
            for old, new in changes:
                altered = altered.replace(old, new, 1)
            if not altered.endswith("}"):
                raise ValueError(f"{name}: mutation removes the function's closing brace")
            altered = altered[:-1]
            alternatives.append(
                f'\n    #[cfg(test)]\n    if std::env::var_os("{CONTROL_ENV}").as_deref()'
                f' == Some(std::ffi::OsStr::new("{name}")) {{\n'
                f'        return {{{altered}}};\n    }}\n'
            )
        source = source[:start] + "".join(alternatives) + source[start:]
    return source


def build(cases, evidence, workspace):
    shutil.copytree(ROOT / "src", workspace / "src")
    shutil.copytree(ROOT / "contract", workspace / "contract")
    manifest = (ROOT / "Cargo.toml").read_text()
    package = "logkeeper-simulation-controls"
    (workspace / "Cargo.toml").write_text(manifest.replace('name = "logkeeper"', f'name = "{package}"', 1))
    shutil.copyfile(ROOT / "Cargo.lock", workspace / "Cargo.lock")
    by_file = {}
    for name, edits, *_ in cases:
        for change in edits:
            by_file.setdefault(change["file"], {}).setdefault(name, []).append(change)
    for file, edits in by_file.items():
        path = workspace / file
        path.write_text(instrument(path.read_text(), edits))
    command = [str(GUARD), "logkeeper", "test", "--offline", "--all-features",
               "--package", package, "--lib", "--no-run", "--message-format=json",
               "--manifest-path", str(workspace / "Cargo.toml")]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, check=False)
    (evidence / "build.log").write_text(result.stdout)
    if result.returncode != 0:
        raise ValueError(f"control build failed, see {evidence / 'build.log'}")
    executables = []
    for line in result.stdout.splitlines():
        if line.startswith("{"):
            message = json.loads(line)
            if message.get("reason") == "compiler-artifact" and message.get("executable"):
                executables.append(message["executable"])
    if len(executables) != 1:
        raise ValueError(f"expected one test executable, found {executables}")
    return executables[0]


def run(case, executable, evidence):
    name, _, test, check, seed = case
    env = dict(os.environ, LOGKEEPER_SIM_FIRST_SEED=str(seed), LOGKEEPER_SIM_SEEDS="1")
    env[CONTROL_ENV] = name
    result = subprocess.run([executable, test, "--exact", "--nocapture"], cwd=ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
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
    results = HERE / ".results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="controls-", dir=results))
    print(f"Evidence: {evidence}", flush=True)
    selected = [cases[name] for name in dict.fromkeys(args.names or cases)]
    failures = []
    with tempfile.TemporaryDirectory(prefix="sources-", dir=evidence) as directory:
        executable = build(selected, evidence, Path(directory))
        for case in selected:
            try:
                run(case, executable, evidence)
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
