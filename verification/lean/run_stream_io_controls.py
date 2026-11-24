#!/usr/bin/env python3
"""Weaken each guard of the stream I/O automaton and check that its proof fails."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
MODULES = HERE / "Logkeeper"

# name: (original text, weakened text, theorem whose proof must fail first)
IO_CONTROLS = {
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
                    "Logkeeper.StreamWriter", "Logkeeper.StreamHead"], cwd=HERE, check=True,
                   capture_output=True)
    directory = HERE / ".results"
    directory.mkdir(exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="stream-io-controls-", dir=directory))
    print(f"Evidence: {evidence}", flush=True)
    modules = {
        "StreamIO": IO_CONTROLS,
        "StreamWriter": WRITER_CONTROLS,
        "StreamHead": HEAD_CONTROLS,
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
        start = next(i for i, line in enumerate(lines, 1) if line.startswith(f"theorem {law} "))
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
