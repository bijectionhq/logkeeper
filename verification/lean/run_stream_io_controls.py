#!/usr/bin/env python3
"""Weaken stream I/O, replacement and WAL guards and check their named proofs."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
MODULES = HERE / "Logkeeper"

# name: (original text, weakened text, theorem whose proof must fail first)
IO_CONTROLS = {
    "discard-after-minority-capacity-refusals": (
        "      (∀ k, (s.pending e).refused k ≠ none) →",
        "      (∃ k, (s.pending e).refused k ≠ none) →",
        "discard_preserves_pending_evidence",
    ),
    "discard-after-an-unanswered-append": (
        "      (s.pending e).uncertainThrough ≤ (s.writer.issued e).length →",
        "      (s.pending e).uncertainThrough = (s.pending e).uncertainThrough →",
        "discard_preserves_pending_evidence",
    ),
    "capacity-refusal-for-a-duplicate": (
        "def CapacityAt (k : Keeper Payload) (position : Nat) : Prop :=\n  position = k.tail + 1",
        "def CapacityAt (k : Keeper Payload) (position : Nat) : Prop :=\n  position = k.tail",
        "capacity_refusal_excludes_retry",
    ),
    "complete-sync-head-past-request": (
        "      SyncHeadAdmitted k.head head (start - 1 + records.length) (k.syncFloor floor)",
        "      SyncHeadAdmitted k.head head (max head (start - 1 + records.length)) (k.syncFloor floor)",
        "complete_sync_head_within_request",
    ),
    "complete-sync-installs-ghost-seed": (
        "  | .sync e floor start records head =>\n"
        "      { accept k e (syncImage k (w.seed e) floor start records) with\n",
        "  | .sync e floor _ _ head =>\n"
        "      { accept k e (w.seed e) with\n",
        "complete_sync_uses_request_records",
    ),
    "stage-from-another-identity": (
        "  | .stage e floor start _ => k.live ∧ k.promised = e ∧ k.identity = caller ∧ k.synced ≠ e ∧",
        "  | .stage e floor start _ => k.live ∧ k.promised = e ∧ True ∧ k.synced ≠ e ∧",
        "deliver_refines",
    ),
    "stage-after-complete-sync": (
        "  | .stage e floor start _ => k.live ∧ k.promised = e ∧ k.identity = caller ∧ k.synced ≠ e ∧",
        "  | .stage e floor start _ => k.live ∧ k.promised = e ∧ k.identity = caller ∧ True ∧",
        "deliver_refines",
    ),
    "sync-without-agreement": (
        "      records = (w.seed e).drop (start - 1) ∧ Agrees k e (w.seed e) floor start ∧",
        "      records = (w.seed e).drop (start - 1) ∧ floor = floor ∧",
        "deliver_refines",
    ),
    "append-anywhere": (
        "      position = k.tail + 1 ∧ payloads ≠ [] ∧ head ≤ k.tail + payloads.length",
        "      position = position ∧ payloads ≠ [] ∧ head ≤ k.tail + payloads.length",
        "deliver_refines",
    ),
    "append-unissued-payload": (
        "      stamp e payloads = ((w.issued e).drop (position - 1)).take payloads.length ∧",
        "      True ∧",
        "deliver_refines",
    ),
    "publish-unsynced": (
        "  | .publish e head => k.live ∧ MayAppend k e ∧ k.identity = caller ∧ head ≤ k.tail",
        "  | .publish e head => k.live ∧ k.promised = e ∧ k.identity = caller ∧ head ≤ k.tail",
        "deliver_refines",
    ),
    "publish-uncertified-head": (
        "  | .publish e head => Elected w e identity ∧ head ≤ (w.issued e).length ∧\n"
        "      w.advertised ((w.issued e).take head)",
        "  | .publish e head => Elected w e identity ∧ head ≤ (w.issued e).length ∧ True",
        "deliver_refines",
    ),
    "trim-above-head": (
        "  | .trim e through => k.live ∧ k.identity = caller ∧ MayTrim k e through",
        "  | .trim e through => k.live ∧ k.identity = caller ∧ Synced k e ∧ through = through",
        "deliver_refines",
    ),
    "seal-at-epoch-zero": (
        "  | .promise e => 0 < e",
        "  | .promise e => e = e",
        "reply_evidence",
    ),
    "collect-a-later-seal-reply": (
        "  | collectSeal {s e k i v} : .reply k (.sealed e i v) ∈ s.net → s.writer.round e = none →",
        "  | collectSeal {s e k i v} : .reply k (.sealed e i v) ∈ s.net →",
        "next_inv",
    ),
    "choose-an-unsaved-report": (
        "      s.seals e r.first = some (r.identity, r.report r.first) →\n",
        "",
        "next_inv",
    ),
    "elect-an-epoch-twice": (
        "  | choose {s e} {r : Round Payload} : 0 < e → s.writer.round e = none →",
        "  | choose {s e} {r : Round Payload} : 0 < e →",
        "next_inv",
    ),
    "certify-one-lane": (
        "  | certify {s e h} (a b : KeeperId) {ha hb : History Payload} : a ≠ b →",
        "  | certify {s e h} (a b : KeeperId) {ha hb : History Payload} :",
        "next_inv",
    ),
}

REPLACEMENT_CONTROLS = {
    "promote-before-both-installs": (
        "def mayInstallLearner (first second : Bool) : Bool := first && second",
        "def mayInstallLearner (first second : Bool) : Bool := first || second",
        "learner_install_requires_both",
    ),
    "allow-learner-during-split": (
        "  | .installing first _, .first => some (if first then .new else .old)",
        "  | .installing true false, .learner => some .new\n"
        "  | .installing first _, .first => some (if first then .new else .old)",
        "split_install_has_no_quorum",
    ),
    "count-a-seal-on-both-routes": (
        "  voter phase node == some route",
        "  let _ := route\n  (voter phase node).isSome",
        "exclusive_ensemble_authority",
    ),
    "repair-uses-a-lost-signer": (
        "(survivingSigners : round.first ≠ lost ∧ round.second ≠ lost)",
        "(survivingSigners : round.first ≠ lost)",
        "surviving_copy_and_adopted_seed",
    ),
    "replace-without-survivor-repair": (
        "  | .intact | .lost => original\n  | .repaired | .installing .. | .promoted => seed",
        "  | .intact | .lost | .repaired => original\n  | .installing .. | .promoted => seed",
        "repaired_survivors_cover",
    ),
    "promote-without-learner-history": (
        "  | .installing .. | .promoted => some seed",
        "  | .installing .. => some seed",
        "promoted_cut_survives_any_one_loss",
    ),
    "import-shortened-repair-cut": (
        "(installed : QuorumAccepted after.keeper repair moved.winner.history)",
        "(installed : QuorumAccepted after.keeper repair [])",
        "seal_after_replacement_covers_acknowledged",
    ),
}

WAL_CONTROLS = {
    "torn-tail-loses-complete-entries": (
        "  | .torn :: _ => if newest then some ([], pending) else none",
        "  | .torn :: _ => none",
        "torn_tail_keeps_complete_entries",
    ),
    "torn-closed-segment-is-accepted": (
        "  | .torn :: _ => if newest then some ([], pending) else none",
        "  | .torn :: _ => some ([], pending)",
        "torn_closed_segment_fails",
    ),
    "partial-entry-prevents-reopening": (
        "      if pending stream then scan newest pending frames else none",
        "      if pending stream then none else scan newest pending frames",
        "incomplete_entry_is_discarded",
    ),
    "finish-without-start": (
        "      if pending entry.1 then\n        (scan newest",
        "      if true then\n        (scan newest",
        "fragments_are_demultiplexed",
    ),
    "rollover-drops-pending-fragments": (
        "  scan newest (if continued then pending else fun _ => false) frames",
        "  let _ := (continued, pending)\n  scan newest (fun _ => false) frames",
        "continued_fragments_finish_after_rollover",
    ),
    "fresh-segment-keeps-pending-fragments": (
        "  scan newest (if continued then pending else fun _ => false) frames",
        "  let _ := continued\n  scan newest pending frames",
        "fresh_segment_discards_incomplete_entries",
    ),
    "checkpoint-captures-newer-entries": (
        "      Next base old r { r with index := some (boundary base old) }",
        "      Next base old r { r with index := some (fun s => replay s (boundary base old s) r.newer) }",
        "next_sound",
    ),
    "publish-before-pack-sync": (
        "  | publish {r} : r.packDurable = true →",
        "  | publish {r} : True →",
        "next_sound",
    ),
    "retire-before-durable-index": (
        "  | retire {r} : r.index.isSome = true →",
        "  | retire {r} : True →",
        "next_sound",
    ),
    "reopen-drops-newer-entries": (
        "      if r.packDurable then some (replay stream (images stream) r.newer) else none",
        "      if r.packDurable then some (images stream) else none",
        "reopen_recovers_each_stream",
    ),
}


WRITER_CONTROLS = {
    "compare-another-epoch": (
        "(rightAt : right[i]? = some b) (same : a.epoch = b.epoch)",
        "(rightAt : right[i]? = some b) (same : a.epoch = a.epoch)",
        "same_epoch_agrees",
    ),
    "extend-page-past-first-head": (
        "start + copied + count ≤ first.length",
        "start + copied ≤ first.length",
        "assemble_read_chunk",
    ),
    "delete-minority": (
        "(durable : JournalRefinement.Majority ensemble deleted)",
        "(durable : deleted 0 = true)",
        "delete_quorum_blocks_live_quorum",
    ),
}

HEAD_CONTROLS = {
    "sample-before-opening": (
        "round.opened ≤ sent k ∧ sent k ≤ round.sampled k ∧ round.sampled k ≤ call.replied",
        "sent k ≤ sent k ∧ sent k ≤ round.sampled k ∧ round.sampled k ≤ call.replied",
        "Samples.confirmed",
    ),
    "return-below-sampled-tails": (
        "{result prior : Nat} (covers : SamplesCovered round result)",
        "{result prior : Nat} (covers : result = result)",
        "head_linearizable",
    ),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=str(Path.home() / ".elan/bin/lake"))
    args = parser.parse_args()
    subprocess.run([args.lake, "build", "Logkeeper.StreamIOWitness",
                    "Logkeeper.StreamWriter", "Logkeeper.StreamHead",
                    "Logkeeper.StreamReplacement", "Logkeeper.StreamWAL"], cwd=HERE, check=True,
                   capture_output=True)
    directory = HERE / ".results"
    directory.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="stream-io-controls-", dir=directory))
    print(f"Evidence: {evidence}", flush=True)
    modules = {
        "StreamIO": IO_CONTROLS,
        "StreamWriter": WRITER_CONTROLS,
        "StreamHead": HEAD_CONTROLS,
        "StreamReplacement": REPLACEMENT_CONTROLS,
        "StreamWAL": WAL_CONTROLS,
    }
    for (module, cases) in modules.items():
        check_controls(args.lake, (MODULES / f"{module}.lean").read_text(), cases, evidence)


def check_controls(lake, original, cases, evidence):
    for name, (old, new, law) in cases.items():
        if original.count(old) != 1:
            raise RuntimeError(f"{name}: mutation site changed")
        mutated = original.replace(old, new)
        path = evidence / f"{name}.lean"
        path.write_text(mutated)
        lines = mutated.splitlines()
        start = next(i for i, line in enumerate(lines, 1) if re.match(rf"^theorem {law}\b", line))
        end = next(i for i, line in enumerate(lines, 1) if i > start and not line)
        result = subprocess.run([lake, "env", "lean", str(path)], cwd=HERE, text=True,
                                capture_output=True)
        output = result.stdout + result.stderr
        path.with_suffix(".log").write_text(output)
        errors = re.findall(r":(\d+):\d+: error(?:\([^\n]*?\))?:", output)
        if result.returncode != 1 or not errors or not start <= int(errors[0]) < end:
            first = errors[0] if errors else "none"
            raise RuntimeError(f"{name}: expected first error in {law} (lines {start}-{end}), "
                               f"got line {first}; see {path.with_suffix('.log')}")
        print(f"{name}: rejected at {law}", flush=True)


if __name__ == "__main__":
    main()
