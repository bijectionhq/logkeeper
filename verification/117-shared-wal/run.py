#!/usr/bin/env python3
"""Check both WAL layouts, their reachability witnesses, and single-fault controls."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import (TLA_SHA256, check_lean_mutation, check_lean_theorems,
                         check_tla, checker_jar, compile_lean_modules)


def verify_tla():
    java = Path.home() / "cycle3/jdk/Contents/Home/bin/java"
    os.environ.setdefault("JAVA_BIN", str(java) if java.is_file() else "java")
    supplied = Path(os.environ.get(
        "TLA2TOOLS_JAR", Path.home() / "cycle3/tools/formal/tla-1.7.4/tla2tools.jar"))
    if supplied.is_file():
        contents = supplied.read_bytes()
        if sha256(contents).hexdigest() != TLA_SHA256:
            raise SystemExit(f"TLC jar checksum mismatch: {supplied}")
        local = ROOT / ".tools" / "tla2tools.jar"
        local.parent.mkdir(exist_ok=True)
        local.write_bytes(contents)
    checker_jar(ROOT)
    cases = []

    def add(module, layout, name, laws, *, fault="none", expected=None):
        cases.append((module, f"{layout}-{name}", layout, fault, laws, expected))

    for layout in ("per-group", "shared"):
        add("VoterWAL", layout, "media", [
            "PromiseDurable", "AcceptDurable", "ExactDemux", "IsolatedCoverage",
        ])
        for witness in ("WALWitness", "QuotaWitness", "QuarantineWitness"):
            add("VoterWAL", layout, witness, [witness], expected=witness)
        add("VoterWAL", layout, "promise-early", ["PromiseDurable"],
            fault="early-promise", expected="PromiseDurable")
        add("VoterWAL", layout, "accept-early", ["AcceptDurable"],
            fault="early-accept", expected="AcceptDurable")

        add("WALAgreement", layout, "agreement", ["PrefixAgreement", "QuorumAtOneBallot",
            "OneCoveringSync", "SyncCount",
        ])
        witness = "ChangedMajorityWitness"
        add("WALAgreement", layout, witness, [witness], expected=witness)
        add("WALAgreement", layout, "blank-overlap", ["PrefixAgreement"],
            fault="empty-rejoin", expected="PrefixAgreement")

        add("WALAgreement", layout, "split-ballot", ["QuorumAtOneBallot"],
            fault="split-ballot", expected="QuorumAtOneBallot")

        add("WALAgreement", layout, "double-barrier", ["SyncCount"],
            fault="double-barrier", expected="SyncCount")

        add("WALErasure", layout, "erasure", [
            "NoResurrection", "ExactRecovery", "NoPlaintextAfterDeadline", "D02HeldView",
            "NeighbourUnchanged", "ScopedCleanup", "CiphertextOnly",
        ])
        witness = "DeadlineWitness"
        add("WALErasure", layout, witness, [witness], expected=witness)
        for fault, law in (
            ("early-rotation", "NoResurrection"),
            ("stale-append", "ExactRecovery"),
            ("revoke-hold", "D02HeldView"),
            ("key-alias", "NoPlaintextAfterDeadline"),
            ("raw-archive", "NoPlaintextAfterDeadline"),
            ("raw-archive", "CiphertextOnly"),
            ("shared-key", "NeighbourUnchanged"),
            ("copy-obsolete", "ScopedCleanup"),
        ):
            add("WALErasure", layout, f"{fault}-{law}", [law], fault=fault, expected=law)

    for fault, law in (
        ("wrong-group", "ExactDemux"),
        ("cross-frontier", "PromiseDurable"),
        ("cross-frontier", "AcceptDurable"),
        ("global-truncate", "IsolatedCoverage"),
        ("quota-evicts-neighbour", "IsolatedCoverage"),
    ):
        add("VoterWAL", "shared", f"{fault}-{law}", [law], fault=fault, expected=law)
    add("WALAgreement", "shared", "no-coalesce", ["OneCoveringSync"],
        fault="no-coalesce", expected="OneCoveringSync")
    add("WALErasure", "shared", "drop-neighbour", ["NeighbourUnchanged"],
        fault="drop-neighbour", expected="NeighbourUnchanged")
    for module, witness in (("VoterWAL", "TwoGroupTearWitness"),
                            ("WALAgreement", "BatchedQuorumWitness")):
        add(module, "shared", witness, [witness], expected=witness)

    def run(case):
        module, name, layout, fault, laws, expected = case
        check_tla(ROOT, module, name, "Spec", {"Layout": f'"{layout}"', "Fault": f'"{fault}"'},
                  [("INVARIANT", law) for law in laws], expected=expected)

    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(run, cases))


def verify_lean():
    lean = Path.home() / ".elan/bin/lean"
    os.environ.setdefault("LEAN_BIN", str(lean) if lean.is_file() else "lean")
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "SharedWAL.lean"
    check_lean_theorems(ROOT, command, source, count=8)
    check_lean_mutation(ROOT, command, source, "remove-demux",
                        [("  project group frames", "  frames")],
                        "  exact other_scope_append group wal tail different")
    check_lean_mutation(ROOT, command, source, "reply-without-barrier",
                        [("\n  id ∈ covered wal\n", "\n  id ∈ wal.written\n")],
                        "  exact reply")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", nargs="?", choices=("tla", "lean"))
    suite = parser.parse_args().suite
    if suite in (None, "tla"):
        verify_tla()
    if suite in (None, "lean"):
        verify_lean()
