#!/usr/bin/env python3
"""Check physical read reservations across compaction, expiry and moves."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("LiveBorrowHasBytes", "NoAdmissionAfterClose", "FencedReadCannotSucceed")


def check(name, laws, *, design="exact", mutation="none", expected=None, count=1):
    constants = {
        "Design": f'"{design}"', "Mutation": f'"{mutation}"',
        "Reads": "{1}" if count == 1 else "{1,2}",
    }
    check_tla(ROOT, "ReadCustody", name, "FairSpec", constants, laws, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "ReadCustody.lean"
    check_lean_mutation(ROOT, command, source, "unreserved-bytes",
        (("(reserved : store.physical image.extent = some image.bytes)", "(reserved : True)"),),
        "exact reserved")
    check_lean_mutation(ROOT, command, source, "reclaim-borrowed",
        (("""(unborrowed : ∀ request image, store.operations request = .borrowing image →
        image.extent ≠ extent)""", "(unborrowed : True)"),),
        "have distinct : image.extent ≠ extent := unborrowed request image live")
    check_lean_theorems(ROOT, command, source, count=6)


def main():
    verify_lean()
    for mutation, law in (
        ("stale_lookup", "LiveBorrowHasBytes"),
        ("logical_only", "LiveBorrowHasBytes"),
        ("admit_after_close", "NoAdmissionAfterClose"),
        ("timeout_is_stop", "LiveBorrowHasBytes"),
        ("late_reply", "FencedReadCannotSucceed"),
    ):
        check(f"control-{mutation}", (("INVARIANT", law),), mutation=mutation, expected=law)
    invariant_checks = tuple(("INVARIANT", law) for law in LAWS)
    for design in ("exact", "drain"):
        for count in (1, 2):
            check(f"baseline-{design}-{count}", invariant_checks + (("PROPERTY", "DrainWithSource"),),
                  design=design, count=count)
    check("drain-without-fence-evidence", (("PROPERTY", "DrainEvenIfSourceLost"),), expected="liveness")
    law = "NeverTrimsAndCompletesBorrow"
    check("witness-exact-borrow-completes-after-trim", (("INVARIANT", law),), expected=law)
    check("drain-disallows-borrow-completing-after-trim", (("INVARIANT", law),), design="drain")
    law = "NeverServesOldAndNewSite"
    check("witness-old-and-new-borrows", (("INVARIANT", law),), expected=law, count=2)


if __name__ == "__main__":
    main()
