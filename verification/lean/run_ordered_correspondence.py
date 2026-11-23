#!/usr/bin/env python3
"""Evaluate the Lean definitions and check the corresponding Verus specs on the same cases."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
WRITER = "Logkeeper.Kernel.Ordered"
RECEIPT = "Logkeeper.Protocol.Ordered"
MAX = 2**64 - 1

CASES = {
    "ordered_writer": (WRITER, [
        ("append_next_lsn 0 0 7", "append_next_lsn(0, 0, 7)"),
        ("append_next_lsn 3 4 7", "append_next_lsn(3, 4, 7)"),
        ("append_next_lsn 3 2 7", "append_next_lsn(3, 2, 7)"),
        (f"append_next_lsn {MAX} {MAX} {MAX}", f"append_next_lsn({MAX}, {MAX}, {MAX})"),
        (f"next_writer_epoch {MAX - 1} {MAX}", f"next_writer_epoch({MAX - 1}, {MAX})"),
        (f"next_writer_epoch {MAX} {MAX}", f"next_writer_epoch({MAX}, {MAX})"),
        ("authorize_writer (some 5) (some (5, 2, 3)) (5, 2, 3)",
         "authorize_writer(Some(5u64), Some((5u64, 2, 3)), (5u64, 2, 3))"),
        ("authorize_writer (some 5) (some (5, 2, 3)) (5, 1, 3)",
         "authorize_writer(Some(5u64), Some((5u64, 2, 3)), (5u64, 1, 3))"),
        ("authorize_writer (some 5) (some (5, 2, 3)) (5, 2, 2)",
         "authorize_writer(Some(5u64), Some((5u64, 2, 3)), (5u64, 2, 2))"),
        ("authorize_writer (some 4) (some (5, 2, 3)) (5, 2, 3)",
         "authorize_writer(Some(4u64), Some((5u64, 2, 3)), (5u64, 2, 3))"),
        ("authorize_writer (some 5) none (5, 2, 3)",
         "authorize_writer(Some(5u64), None, (5u64, 2, 3))"),
        ("withdraw_grant (some 5) true", "withdraw_grant(Some(5u64), true)"),
        ("withdraw_grant (some 5) false", "withdraw_grant(Some(5u64), false)"),
    ]),
    "ordered_receipt": (RECEIPT, [
        ("retains_receipt 7 8 false", "retains_receipt(7, 8, false)"),
        ("retains_receipt 8 8 false", "retains_receipt(8, 8, false)"),
        ("retains_receipt 9 8 true", "retains_receipt(9, 8, true)"),
        ("replay_mutation [0, 1] [0, 2] 9", "replay_mutation(seq![0u8, 1], seq![0u8, 2], 9u64)"),
        ("replay_mutation [0, 1] [0] 9", "replay_mutation(stored, shortened, 9u64)"),
        ("replay false [0, 1] [0, 1] 9", "replay(false, seq![0u8, 1], seq![0u8, 1], 9u64)"),
        ("replay true [0, 1] [0, 1] 9", "replay(true, seq![0u8, 1], seq![0u8, 1], 9u64)"),
        ("record_after_apply true (.error (3 : Nat) : Except Nat Nat)",
         "record_after_apply(true, Result::<u64, u64>::Err(3))"),
        ("record_after_apply true (.ok (3 : Nat) : Except Nat Nat)",
         "record_after_apply(true, Result::<u64, u64>::Ok(3))"),
        ("record_after_apply false (.error (3 : Nat) : Except Nat Nat)",
         "record_after_apply(false, Result::<u64, u64>::Err(3))"),
    ]),
}


def verus_literal(value):
    if value in ("true", "false"):
        return value
    if value == "none":
        return "None"
    if match := re.fullmatch(r"some (\d+)", value):
        return f"Some({match.group(1)})"
    raise ValueError(f"Unexpected Lean result {value!r}")


def check_area(lake, verus, scratch, area, namespace, cases):
    lean = scratch / "Correspondence.lean"
    module_name = "OrderedWriter" if area == "ordered_writer" else "OrderedReceipt"
    lean.write_text(
        f"import Logkeeper.{module_name}\nopen {namespace}\n"
        + "".join(f"#eval ({expression})\n" for expression, _ in cases),
        encoding="utf-8",
    )
    evaluation = subprocess.run(
        [lake, "env", "lean", str(lean)], cwd=ROOT, check=True, text=True, capture_output=True,
    ).stdout.splitlines()
    if len(evaluation) != len(cases):
        raise ValueError(f"{area}: expected {len(cases)} Lean results, saw {evaluation!r}")

    area_path = Path("verification/verus") / area
    shutil.copytree(REPO / area_path, scratch / area_path)
    harness = scratch / area_path / "proof.rs"
    assertions = "".join(
        f"        assert(laws::{expression} == {verus_literal(value)});\n"
        for (_, expression), value in zip(cases, evaluation, strict=True)
    )
    if area == "ordered_receipt":
        assertions = (
            "        let stored = seq![0u8, 1];\n"
            "        let shortened = seq![0u8];\n"
            "        assert(stored.len() == 2 && shortened.len() == 1);\n"
            + assertions
        )
    with harness.open("a", encoding="utf-8") as file:
        file.write(
            "\nmod correspondence {\n"
            "    use crate::laws;\n"
            "    use vstd::prelude::*;\n"
            "    verus! {\n"
            "    proof fn reference_agrees_on_cases() {\n"
            "        broadcast use vstd::seq::group_seq_axioms;\n"
            + assertions + "    }\n    }\n}\n"
        )
    result = subprocess.run(
        [verus, "--output-json", "--no-external-by-default", "--verify-module", "correspondence",
         str(area_path / "proof.rs")],
        cwd=scratch, text=True, capture_output=True,
    )
    if result.returncode:
        raise SystemExit(result.stderr)
    if json.loads(result.stdout)["verification-results"]["verified"] != 1:
        raise SystemExit(f"{area}: Verus did not check the correspondence proof")
    print(f"{area}: Lean and Verus agree on {len(cases)} cases")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verus", default="verus")
    args = parser.parse_args()
    verus = shutil.which(args.verus)
    if verus is None:
        parser.error(f"Verus executable not found: {args.verus}")
    lake = os.environ.get("LAKE_BIN", str(Path.home() / ".elan/bin/lake"))
    subprocess.run([lake, "build"], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)

    results = ROOT / ".results"
    results.mkdir(exist_ok=True)
    with TemporaryDirectory(prefix="ordered-correspondence-", dir=results) as scratch_path:
        scratch = Path(scratch_path)
        sources = scratch / "src/ordered"
        sources.mkdir(parents=True)
        for name in ("writer.rs", "refusal.rs", "receipt.rs", "admission.rs"):
            shutil.copyfile(REPO / "src/ordered" / name, sources / name)
        for area, (namespace, cases) in CASES.items():
            check_area(lake, verus, scratch, area, namespace, cases)


if __name__ == "__main__":
    main()
