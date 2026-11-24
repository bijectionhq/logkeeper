#!/usr/bin/env python3
"""Run Study 119 and reject failures outside their designated checks."""

import argparse
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import (
    check_lean_mutation,
    check_lean_theorems,
    check_tla,
    command_in,
)

LEAN = ROOT.parent / "lean"
LAKE = Path.home() / ".elan/bin/lake"
STUDY_117 = ROOT.parents[2] / "logkeeper-k5/verification/117-shared-wal"
JAVA = Path("/Users/sachaichbiah/cycle3/jdk/Contents/Home/bin/java")
TLC = Path("/Users/sachaichbiah/cycle3/tools/formal/tla-1.7.4/tla2tools.jar")

RULES = (
    "CreateGuard", "SealOrder", "SealHolder", "SyncPromise", "SyncRetainsCommit",
    "SyncComplete", "AppendPromise", "AppendSynced", "AppendCondition", "AppendRetry",
    "TrimEpoch", "TrimCommit", "CheckPure", "ReadFloor", "ReadExact", "DeleteTerminal",
)
PROTOCOL = (
    "KeeperBounds", "CommittedPrefix", "QuorumCommit", "ServedSeal", "WinnerRank", "HeadLinearizable",
    "RecoverableAfterLoss", "BothSurvivorsAfterRepair", "LearnerExcluded", "ReplyDurable", "ExactDemux",
)
WAL = ("ReplyDurable", "ExactDemux")
BASELINES = {
    "rules": (*RULES, "KeeperBounds"),
    "rank": ("WinnerRank",),
    "protocol": (*RULES, *PROTOCOL),
    "wal": WAL,
    "handoff": (*RULES, "DelayedAppendAlreadyCommitted"),
    "retention": (*RULES, "KeeperBounds"),
}
WITNESSES = (
    ("protocol", "NoProtocolWitness"),
    ("protocol", "NoNonWriterWitness"),
    ("wal", "NoWalWitness"),
    ("handoff", "NoDelayedAppendWitness"),
)
CONTROLS = (
    ("rules", "recreate", "CreateGuard"),
    ("rules", "seal-lower", "SealOrder"),
    ("rules", "seal-tie", "SealHolder"),
    ("rules", "sync-promise", "SyncPromise"),
    ("rules", "sync-truncate", "SyncRetainsCommit"),
    ("rules", "sync-incomplete", "SyncComplete"),
    ("rules", "append-promise", "AppendPromise"),
    ("rules", "append-unsynced", "AppendSynced"),
    ("rules", "append-gap", "AppendCondition"),
    ("rules", "append-conflict", "AppendCondition"),
    ("rules", "append-retry", "AppendRetry"),
    ("rules", "trim-epoch", "TrimEpoch"),
    ("rules", "trim-above", "TrimCommit"),
    ("rules", "trim-above", "KeeperBounds"),
    ("rules", "check-mutates", "CheckPure"),
    ("rules", "read-below", "ReadFloor"),
    ("rules", "read-uncommitted", "ReadExact"),
    ("rules", "delete-forgets", "DeleteTerminal"),
    ("rank", "last-entry", "WinnerRank"),
    ("protocol", "single-accept", "QuorumCommit"),
    ("protocol", "uncommitted-watermark", "CommittedPrefix"),
    ("protocol", "empty-rejoin", "RecoverableAfterLoss"),
    ("protocol", "skip-repair", "BothSurvivorsAfterRepair"),
    ("protocol", "seal-short", "ServedSeal"),
    ("protocol", "stale-head", "HeadLinearizable"),
    ("protocol", "learner-votes", "LearnerExcluded"),
    ("wal", "early-wal-reply", "ReplyDurable"),
    ("wal", "cross-frontier", "ReplyDurable"),
    ("wal", "wrong-stream", "ExactDemux"),
)
GAPS = (
    ("protocol", "writer-known-only", "HeadLinearizable"),
    ("protocol", "none", "BothSurvivorsAfterLoss"),
    ("handoff", "seal-observed-only", "DelayedAppendAlreadyCommitted"),
    ("retention", "none", "QuorumTrimReadFloor"),
)


def tla(scenario, name, laws, fault="none", expected=None):
    check_tla(ROOT, "StreamJournal", name, "Spec",
              {"Scenario": f'"{scenario}"', "Fault": f'"{fault}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla(selected):
    if JAVA.is_file():
        os.environ.setdefault("JAVA_BIN", str(JAVA))
    local_jar = ROOT / ".tools" / "tla2tools.jar"
    if TLC.is_file() and not local_jar.exists():
        local_jar.parent.mkdir(exist_ok=True)
        local_jar.symlink_to(TLC)

    for scenario, laws in BASELINES.items():
        if selected in (None, scenario):
            tla(scenario, scenario, laws)
    for scenario, law in WITNESSES:
        if selected in (None, scenario):
            tla(scenario, f"witness-{law}", (law,), expected=law)
    for prefix, experiments in (("control", CONTROLS), ("gap", GAPS)):
        for scenario, fault, law in experiments:
            if selected in (None, scenario):
                tla(scenario, f"{prefix}-{fault}-{law}", (law,), fault, law)


def verify_lean(shared_wal):
    results = ROOT / ".results"
    build = results / "lean-build"
    code, log, _ = command_in(LEAN, build, [str(LAKE), "build"])
    if code:
        raise SystemExit(f"Lean package failed to build. See {log}")

    toolchain = (LEAN / "lean-toolchain").read_text().strip()
    command = [str(LAKE), f"+{toolchain}", "-d", str(LEAN), "env", "lean"]
    source = LEAN / "Logkeeper/StreamJournal.lean"
    check_lean_theorems(ROOT, command, source, count=21)

    controls = (
        ("append-unsynced",
         "def MayAppend (k : Keeper Payload) (epoch : Nat) : Prop := Synced k epoch",
         "def MayAppend (k : Keeper Payload) (epoch : Nat) : Prop := k.promised = epoch ∧ True",
         "exact admitted.2 -- synced guard"),
        ("seal-tie",
         "k.promised = epoch ∧ k.holder = holder",
         "k.promised = epoch ∧ holder = holder",
         "exact tied.2 -- holder guard"),
        ("last-entry",
         "def recoveryEpoch (vote : Vote (Record Payload)) : Nat := vote.ballot",
         "def recoveryEpoch (vote : Vote (Record Payload)) : Nat := "
         "(vote.history.getLast?.map Record.epoch).getD 0",
         "rfl -- recovery key"),
        ("trim-above",
         "Synced k epoch ∧ through ≤ k.commit",
         "Synced k epoch ∧ through = through",
         "exact admitted.2 -- trim guard"),
        ("stale-round",
         "def Fresh (call : Invocation) (round : CheckRound) : Prop :=\n  call.started ≤ round.opened",
         "def Fresh (_call : Invocation) (_round : CheckRound) : Prop := True",
         "exact confirmed.fresh -- fresh round guard"),
    )
    for name, old, new, failure in controls:
        check_lean_mutation(ROOT, command, source, name, ((old, new),), failure)

    external = shared_wal / "SharedWAL.lean"
    if not external.is_file():
        raise SystemExit(f"Study 117 source unavailable at {external}. Pass --shared-wal.")
    code, log, _ = command_in(ROOT, results / "lean-study-117", [
        *command, f"--root={external.parent}", "-o", str(build / "SharedWAL.olean"),
        str(external),
    ])
    if code:
        raise SystemExit(f"Study 117 Lean module failed to build. See {log}")
    bridge_command = [*command[:-1], "env", f"LEAN_PATH={build}:{LEAN / '.lake/build/lib/lean'}", "lean"]
    check_lean_theorems(ROOT, bridge_command, ROOT / "WALBridge.lean", count=1, case="lean-wal-bridge")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", choices=BASELINES, help="only check one TLC scenario")
    parser.add_argument("--lean-only", action="store_true", help="only build and check Lean")
    parser.add_argument("--shared-wal", type=Path, default=STUDY_117, help="Study 117 source directory")
    args = parser.parse_args()
    if args.lean_only and args.scenario:
        parser.error("--lean-only and --scenario cannot be combined")
    if not args.scenario:
        verify_lean(args.shared_wal.resolve())
    if not args.lean_only:
        verify_tla(args.scenario)


if __name__ == "__main__":
    main()
