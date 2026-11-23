#!/usr/bin/env python3
"""Check compact provider admission and physical namespace reuse."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("AllIssuedAccounted", "NoReopen", "NeverReuseIssued", "OneEffectPerTicket",
          "StableErase", "BoundedLive")
SCOPE_SAFETY = ("NeverReusesClosedScope", "WritesOnlyInOwnScope", "OnlyReclaimsAbsent")


def check(name, laws, *, tickets=4, width=2, policy="active", variant="reference", expected=None):
    constants = {"Tickets": tickets, "Width": width, "Policy": f'"{policy}"', "Variant": f'"{variant}"'}
    check_tla(ROOT, "TicketBook", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def namespace(name, laws, *, variant="reference", expected=None):
    check_tla(ROOT, "PhysicalNamespace", name, "Spec", {"Variant": f'"{variant}"'},
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    for variant, law in (
        ("missing_is_live", "StableErase"),
        ("split_issue", "NoReopen"),
        ("split_issue", "StableErase"),
        ("certify_unissued", "NoReopen"),
        ("restart_drops_issuance", "NeverReuseIssued"),
    ):
        check(f"control-{variant}-{law}", (law,), variant=variant, expected=law)
    check("control-unsafe-marker-compaction", ("StableErase",), policy="markers",
          variant="forget_markers", expected="StableErase")
    check("control-marker-rows-grow", ("BoundedTerminalRows",), policy="markers", expected="BoundedTerminalRows")
    for tickets, width in ((3, 1), (5, 2)):
        check(f"active-{tickets}-{width}", (*SAFETY, "BoundedTerminalRows"), tickets=tickets, width=width)
        check(f"markers-{tickets}-{width}", SAFETY, tickets=tickets, width=width, policy="markers")
    for law in ("NeverConfirmsAfterCompactionAndRestart", "NeverRejectsDelayedCompletedAfterErase",
                "NeverIssuesBeyondWidthWithAnOldLive"):
        check(f"witness-{law}", (law,), expected=law)
    for variant, law in (
        ("route_only", "WritesOnlyInOwnScope"),
        ("forget_namespace_issuance", "NeverReusesClosedScope"),
        ("reclaim_before_absence", "OnlyReclaimsAbsent"),
    ):
        namespace(f"control-{variant}", (law,), variant=variant, expected=law)
    namespace("exact-namespace", SCOPE_SAFETY)
    reused = "NeverReusesAddressAndRefusesOldTicket"
    namespace(f"witness-{reused}", (reused,), expected=reused)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "06-generations/Reservation.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
    ))
    source = ROOT / "TicketBook.lean"
    check_lean_mutation(ROOT, command, source, "serial-only-provider-lookup",
        (("  ticket ∈ state.book.live\n\ndef MayWrite",
          "  ticket.serial ∈ Serials state.book\n\ndef MayWrite"),),
        "exact live")
    check_lean_mutation(ROOT, command, source, "reuse-address-without-absence",
        (("  CanErase address.state ∧ address.state.present = false\n",
          "  CanErase address.state ∧ True\n"),),
        "exact verified")
    check_lean_mutation(ROOT, command, source, "route-only-effect",
        (("def ScopedWrite (address : Address Image) (id : Nat) (ticket : Ticket Image) : Prop :=\n"
          "  LiveNamespace address id ∧ MayWrite address.state ticket",
          "def ScopedWrite (address : Address Image) (_id : Nat) (ticket : Ticket Image) : Prop :=\n"
          "  True ∧ MayWrite address.state ticket"),),
        "exact permitted.1")
    check_lean_theorems(ROOT, command, source, count=19)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
