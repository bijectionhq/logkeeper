#!/usr/bin/env python3
"""Build the codec references, audit their axioms, and check weakened premises."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


def main():
    lake = os.environ.get("LAKE_BIN", "lake")
    subprocess.run([lake, "build"], cwd=ROOT, check=True)
    command = [lake, "env", "lean"]
    codec = ROOT / "Logkeeper" / "Codec.lean"
    domains = ROOT / "Logkeeper" / "CodecDomains.lean"
    image = ROOT / "Logkeeper" / "CompactImage.lean"
    slot = ROOT / "Logkeeper" / "VoterSlotHeader.lean"
    transport = ROOT / "Logkeeper" / "VoterTransport.lean"
    check_lean_theorems(ROOT, command, codec, count=7, case="codec")
    check_lean_theorems(ROOT, command, domains, count=11, case="codec-domains")
    check_lean_theorems(ROOT, command, image, count=12, case="compact-image")
    check_lean_theorems(ROOT, command, slot, count=4, case="voter-slot-header")
    check_lean_theorems(ROOT, command, transport, count=4, case="voter-transport")
    check_lean_mutation(
        ROOT, command, transport, "transport-ignore-installed-group",
        [("  group = authorized ∧ group = installed\n", "  group = authorized ∧ True\n")],
        "  exact accepted",
    )
    check_lean_mutation(
        ROOT, command, slot, "voter-slot-header-ignore-voter",
        [("header.voter = voter ∧", "True ∧")],
        "  rfl\n\nprivate theorem take_field",
    )
    check_lean_mutation(
        ROOT, command, codec, "codec-ignore-maximum",
        [("minimum ≤ declared ∧ declared ≤ maximum", "minimum ≤ declared ∧ True")],
        "    boundedBodyLength declared minimum maximum = none := by",
    )
    check_lean_mutation(
        ROOT, command, image, "object-name-allow-zero-first",
        [("    | first :: _ => objectNameBefore zeroName first) ∧", "    | _ :: _ => True) ∧")],
        "    have edge : objectNameBefore zeroName first := accepted.2.1",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-allow-reused-receipt-position",
        [("  receiptPositionsUnique image.receiptPositions ∧", "  True ∧")],
        "  exact valid.1",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-vacancy-resets-generation",
        [("{ writer with holder := none }", "{ writer with holder := none, keyGeneration := 1 }")],
        "  rfl\n",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-torn-object-name",
        [("count ≤ maximum ∧ 32 * count ≤ remaining", "count ≤ maximum ∧ count ≤ remaining")],
        "  omega\n\ndef rootReferenceRowValid",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-unknown-root",
        [("known = true ∧ match previous with", "True ∧ match previous with")],
        "  accepted\n",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-missing-receipt",
        [("receiptPosition = some admittedAt", "receiptPosition = some admittedAt ∨ receiptPosition = none")],
        "  exact ⟨row.1, checked row member, rfl⟩",
    )
    for name, original, weakened, law in [
        (
            "fixed-field-consume-suffix-byte",
            "then some (frame.take width) else none",
            "then some (frame.take (width + 1)) else none",
            "    readFixedField (field ++ suffix) field.length = some field := by",
        ),
        (
            "decision-keep-last-time-byte",
            "frame.take 1 ++ frame.drop 9",
            "frame.take 1 ++ frame.drop 8",
            "  simpa [decisionRequestBytes, decisionHeader, List.drop_append, width]",
        ),
        (
            "service-allow-count-truncation",
            "count : Nat) : Prop := count ≤ 64",
            "count : Nat) : Prop := count ≤ 256",
            "  have fits : count < 256 := by omega",
        ),
        (
            "service-allow-barrier-with-rotation",
            "hasBarrier = false ∧ coversReceipt = true",
            "hasBarrier = true ∧ coversReceipt = true",
            "  exact Bool.noConfusion good.1",
        ),
        (
            "compact-image-allow-unsorted-old-roots",
            "layout.oldRoots.Pairwise (fun a b => oldRootKeyIncreases b.1 (some a.1))",
            "layout.oldRoots.Pairwise (fun a b => a.1 ≠ b.1)",
            "    accepted.1.imp",
        ),
        (
            "compact-image-allow-explicit-empty-trailer",
            "present = true ↔ roots ≠ 0 ∨ fences ≠ 0",
            "present = true ↔ True",
            "  exact accepted.mp rfl",
        ),
        (
            "compact-image-drop-receipt-position-freshness",
            "  position ∉ positions",
            "  True",
            "    fun member => fresh",
        ),
        (
            "compact-image-ignore-retry-horizon",
            "expiresAt - decisionPosition ≤ retryHorizon ∧",
            "True ∧",
            "  exact ⟨positive, past, by omega⟩",
        ),
    ]:
        check_lean_mutation(ROOT, command, domains, name, [(original, weakened)], law)


if __name__ == "__main__":
    main()
