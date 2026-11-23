# Study 101 · Give independent exact reads a bounded selective window

2026-11-23

## Verdict

If a caller issues independent exact-read attempts concurrently, a missing early attempt can block all later opens under a next-only floor.
Use a bounded window for callers that explicitly permit independent opens to overtake.
Mark just the exact admitted or abandoned nonce.
Advance the floor only over already resolved identities and normalize the bitmap before using its upper boundary.
The window admits a later eligible nonce while preserving the earlier one's right to admission.
A hole that eventually fills the window still requires resolution, abandonment, or a valid scope change.

## Evidence

Lean 4.35.0 checked nine theorems with standard axioms only.
The pure candidate spends exactly one in-range fresh nonce per accepted decision.
Every finite sequence preserves old spent identities and the issuance ceiling.
Compaction preserves the exact spent set.
Normalization takes at most the configured width, stops at the first unresolved nonce, and preserves every bit's meaning.
For a given width, equal spent sets have equal normalized floors and bitmaps.
This last fact prevents compacted and uncompact states at the same logical history from making different window-edge decisions.
The width-one admission law recovers the exact next-nonce rule for a normalized state within its issuance limit.
The constructive program admits nonce 2, leaves nonce 1 eligible, then admits nonce 1.
The Lean control allows compaction over an unresolved first nonce and falsifies the trace invariant.

The existing [TLC comparison](../architecture-reopening/tensions.md#a-next-nonce-floor-imposes-head-of-line-blocking) was rerun.
It demonstrates the width-one stall, width-two progress, a full-window refusal, safe later arrival, gap abandonment, and the failures from guessing a floor or losing sparse marks at restart.

## Design rule

Apply chosen admission or authenticated abandonment and its normalized summary in one exact ordered step.
Scope the window to a writer grant and bind its fixed width, floor and all bitmap bits to the certified checkpoint and exact ordered suffix.
Each successful open still needs its own protected result and custody.
A live predecessor result keeps its original identity for reconciliation.
An older writer grant stays fenced against fresh admission.
Represent the next-only semantic policy with the same width-one window.
Use a larger width only for an explicitly independent caller contract.

## Acceptance

An independent caller issues two authenticated nonces.
The earlier request is delayed.
Open and close the later one, then reopen from certified state.
Reject a duplicated later nonce and allow the original earlier one when it arrives within scope.
Refuse beyond the outstanding window until the intervening gap is explicitly resolved.

## Limits

Lean verifies the pure state and normalization.
The old model comparison covers bounded live-row cleanup and restart.
The candidate still needs to replace the floor in the combined chosen read reducer and bind its canonical encoding through both selectable roots and writer handoff.
Bijection's caller review determines where requests are independent and whether the external API can expose overtaking.
Larger windows require a caller contract that permits overtaking.
Use [A401–A403](../amendments.md#study-101--2026-11-23).

## Reproduction

```sh
LEAN_BIN=/path/to/elan/bin/lean python3 verification/101-selective-read-window/run.py
JAVA_BIN=/path/to/jdk/bin/java python3 verification/architecture-reopening/run.py read-identities
```
