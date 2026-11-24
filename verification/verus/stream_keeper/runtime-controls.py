#!/usr/bin/env python3
"""Run isolated Rust mutations against the keeper's I/O tests."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
GUARD = Path.home() / "code/codesign-agents/guarded-cargo.py"
KEEPER_TEST = "stream::keeper::tests::"
TLS_TEST = "stream::transport::tests::loopback_mtls_checks_certificate_authority_uri_and_route"

# name, source, existing text, substituted text, exact test, expected panic text
CONTROLS = [
    (
        "one-sync-per-request", "keeper/mod.rs",
        "            let identity = work.seal_identity().cloned();",
        "            self.wal.write_round(&buffer)?;\n            buffer.clear();\n"
        "            let identity = work.seal_identity().cloned();",
        KEEPER_TEST + "group_commit_covers_multiple_streams_in_one_sync", "two streams must share one covering sync",
    ),
    (
        "ignore-failed-sync", "keeper/mod.rs",
        "        self.wal.write_round(&buffer)?;\n        for id in changed {",
        "        let covering_sync = self.wal.write_round(&buffer);\n        for id in changed {",
        KEEPER_TEST + "sync_failure_publishes_neither_the_ack_nor_a_read_of_staged_data",
        "reply escaped a failed sync",
    ),
    (
        "uncapped-stream", "keeper/mod.rs",
        "self.limits.round_bytes_per_stream - *charge",
        "codec::MAX_FRAME_BYTES",
        KEEPER_TEST + "round_cap_is_enforced_even_for_a_record_larger_than_the_cap", "a stream exceeded its byte cap",
    ),
    (
        "stop-at-first-trimmed", "writer/read.rs",
        "            Err(error @ JournalError::Deleted) => return Err(error),",
        "            Err(error @ (JournalError::Deleted | JournalError::Trimmed { .. })) => return Err(error),",
        "stream::writer::tests::single_keeper_read_serves_committed_records_below_a_remote_floor",
        "a reachable keeper still retains the committed record",
    ),
    (
        "skip-read-wait", "keeper/mod.rs",
        "(wait && max != 0 && from > through)", "(wait && false && max != 0 && from > through)",
        KEEPER_TEST + "read_waits_for_commit_and_times_out_at_the_end", "read completed before commit",
    ),
    (
        "skip-read-wakeup", "keeper/mod.rs",
        "self.streams[&id].changed.send_replace(());", "let _ = id;",
        KEEPER_TEST + "read_waits_for_commit_and_times_out_at_the_end", "read did not recheck after commit",
    ),
    (
        "shorten-read-wait", "keeper/mod.rs",
        "let deadline = tokio::time::Instant::now() + wait;",
        "let deadline = tokio::time::Instant::now() + wait.min(Duration::from_millis(1));",
        KEEPER_TEST + "read_waits_for_commit_and_times_out_at_the_end", "read resampled before deadline",
    ),
    (
        "ignore-authenticated-identity", "keeper/rules.rs",
        ".is_some_and(|(current, owner)| *current == epoch && owner == identity)",
        ".is_some_and(|(current, _)| *current == epoch)",
        "stream::transport::tests::writer_round_trips_through_three_tls_keepers",
        "a different certificate identity must be fenced at the same epoch",
    ),
    (
        "drop-wal-identity", "keeper/wal.rs",
        "Ok(Some(Identity::from(uri)))",
        'Ok(Some(Identity::from("urn:logkeeper:client:wrong")))',
        KEEPER_TEST + "replacement_ensemble_survives_wal_recovery",
        "replay must preserve the authenticated certificate identity",
    ),
    (
        "drop-wal-replacement", "keeper/wal.rs",
        "        states\n            .entry(id)",
        "        if matches!(request, Request::Replace { .. }) { continue; }\n        states\n            .entry(id)",
        KEEPER_TEST + "replacement_ensemble_survives_wal_recovery",
        "replay must preserve the new ensemble",
    ),
    (
        "ignore-wal-crc", "keeper/wal.rs",
        "Ok((crc32fast::hash(&bytes) == crc).then(|| Bytes::from(bytes)))",
        "let _ = crc;\n    Ok(Some(Bytes::from(bytes)))",
        KEEPER_TEST + "recovery_cuts_interleaved_torn_tail_and_keeps_the_other_stream", "torn record was replayed",
    ),
    (
        "cut-middle-segment", "keeper/wal.rs", "if !tail {", "if !tail && false {",
        KEEPER_TEST + "recovery_refuses_damage_before_the_last_segment", "middle segment damage was accepted",
    ),
    (
        "replay-checkpointed-stream", "keeper/wal.rs", "sequence <= last", "sequence < last",
        KEEPER_TEST + "recovery_resumes_rotation_after_only_one_stream_checkpointed", "checkpointed stream was rewritten",
    ),
    (
        "ignore-extent-crc", "keeper/state.rs",
        "if crc32fast::hash(&bytes) != *crc {", "if crc32fast::hash(&bytes) != *crc && false {",
        KEEPER_TEST + "corrupt_extent_cannot_supply_a_read", "called `Result::unwrap_err()` on an `Ok` value",
    ),
    (
        "delete-without-rotation", "keeper/mod.rs",
        "if !deletions.is_empty() || self.wal.bytes >= wal::SEGMENT_BYTES {",
        "if self.wal.bytes >= wal::SEGMENT_BYTES {",
        KEEPER_TEST + "delete_rotates_and_removes_only_its_payloads", "delete must rotate",
    ),
    (
        "reopen-as-another-keeper", "keeper/wal.rs",
        "id == keeper.0.to_be_bytes() && !paths.is_empty()", "id.len() == 16 && !paths.is_empty()",
        KEEPER_TEST + "existing_keeper_directory_rejects_identity_change_and_missing_wal", "assertion failed",
    ),
    (
        "bypass-seal-policy", "keeper/rules.rs", "if !view.seal_allowed {", "if !view.seal_allowed && false {",
        KEEPER_TEST + "nomination_policy_can_refuse_a_seal", "right: Refused(Unauthorized)",
    ),
    (
        "single-survivor", "keeper/sweep.rs",
        "let (left, right) = tokio::try_join!(\n"
        "            self.seal(transport, first, next),\n"
        "            self.seal(transport, second, next)\n"
        "        )?;",
        "let left = self.seal(transport, first, next).await?;\n"
        "        let (second, right) = match self.seal(transport, second, next).await {\n"
        "            Ok(view) => (second, view),\n"
        "            Err(_) => (first, left.clone()),\n"
        "        };",
        KEEPER_TEST + "sweeper_uses_two_survivors_and_activates_the_trimmed_learner",
        "matches!(outcome, Err(SweepError::Transport",
    ),
    (
        "sync-activates-learner", "keeper/state.rs",
        "self.view.synced = Some(epoch);", "self.view.synced = Some(epoch);\n                    self.view.learner = false;",
        KEEPER_TEST + "replacement_fences_stale_routes_and_resumes_a_split_install", "sync alone activated a replacement",
    ),
    (
        "stale-seal", "keeper/rules.rs",
        "if *ensemble != state.ensemble {\n                    return wrong_ensemble(state);\n                }\n                let current",
        "if *ensemble != state.ensemble && false {\n                    return wrong_ensemble(state);\n                }\n                let current",
        KEEPER_TEST + "replacement_fences_stale_routes_and_resumes_a_split_install", "stale route gained a promise",
    ),
    (
        "stale-delete", "keeper/rules.rs",
        "if *ensemble != state.ensemble {\n                    return wrong_ensemble(state);\n                }\n            }",
        "if *ensemble != state.ensemble && false {\n                    return wrong_ensemble(state);\n                }\n            }",
        KEEPER_TEST + "replacement_fences_stale_routes_and_resumes_a_split_install", "stale route gained a tombstone",
    ),
    (
        "writes-by-reader", "transport.rs", "_ => can_write,", "_ => can_write || can_read,",
        TLS_TEST, "reader reached a writer verb",
    ),
    (
        "bypass-client-uri", "transport.rs", "|| (!can_read && !can_write)", "|| (!can_read && !can_write && false)",
        TLS_TEST, "accepted unauthorized URI",
    ),
    (
        "bypass-keeper-uri", "transport.rs", "if peer != keeper {", "if peer != keeper && false {",
        TLS_TEST, "keeper URI does not match route",
    ),
]


def run(control, source, evidence):
    name, relative, old, new, test, assertion = control
    path = source / "src/stream" / relative
    original = path.read_bytes()
    old = old.encode()
    if original.count(old) != 1:
        raise ValueError(f"{path}: expected one mutation site for {name}")
    mutated = original.replace(old, new.encode(), 1)
    if name == "ignore-failed-sync":
        old_return = b"            let _ = done.send(reply);\n        }\n        Ok(())"
        if mutated.count(old_return) != 1:
            raise ValueError(f"{path}: expected one return site for {name}")
        mutated = mutated.replace(old_return, b"            let _ = done.send(reply);\n        }\n        covering_sync", 1)
    try:
        path.write_bytes(mutated)
        command = [
            str(GUARD), "logkeeper", "test", "--manifest-path", str(source / "Cargo.toml"),
            "--target-dir", str(source / "target"), "--config", "profile.test.debug=0",
            "--lib", "--all-features", test, "--", "--exact",
        ]
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
    finally:
        path.write_bytes(original)
    (evidence / f"{name}.log").write_text(result.stdout)
    if result.returncode == 0 or f"test {test} ... FAILED" not in result.stdout or assertion not in result.stdout:
        raise ValueError(f"{name}: did not fail at the expected check, see {evidence}")
    print(f"{name}: failed at {test}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("controls", nargs="*")
    args = parser.parse_args()
    selected = set(args.controls) or {control[0] for control in CONTROLS}
    if unknown := selected - {control[0] for control in CONTROLS}:
        parser.error(f"unknown controls: {', '.join(sorted(unknown))}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "src/stream"], cwd=ROOT).returncode:
        parser.error("commit the keeper source before running the controls")
    results = ROOT / "verification/verus/.results"
    results.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="keeper-runtime-", dir=results))
    print(f"Evidence: {evidence}", flush=True)
    # A guarded Cargo invocation serializes builds. Keep the mutations outside
    # the production source tree so a normal build can never compile a control.
    with tempfile.TemporaryDirectory(prefix="source-", dir=evidence) as scratch:
        source = Path(scratch)
        for name in ("Cargo.toml", "Cargo.lock"):
            shutil.copyfile(ROOT / name, source / name)
        for name in ("contract", "src"):
            shutil.copytree(ROOT / name, source / name)
        for control in CONTROLS:
            if control[0] in selected:
                run(control, source, evidence)


if __name__ == "__main__":
    main()
