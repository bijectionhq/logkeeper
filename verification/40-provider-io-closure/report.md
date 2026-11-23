# Study 40 report · Close outstanding provider writes

2026-11-23

## Verdict

A durable producer-side admission fence stops new tickets.
A provider-side effect fence or durable completion of every issued one-use ticket stops materialization from the old tickets.
Both layers matter before absence can be certified.
The provider serializes ticket consumption with the effect, and preserves both ticket decisions and fences through recovery.

An original custodian can take over the full remaining charge before provider I/O has closed.
That permits the target to release its own capacity even if a write is still pending.
Erasure and removal of the receiving charge require stable absence.

## Bounded comparison

TLC explored one authorized retiring physical version, at most two or three issued tickets, two deliveries per ticket, one restart, and separately observed local and provider closure.
The charge model reserves the full possible footprint and tracks the issued ticket identities.
Provider absence and transfer of the receiving charge are atomic model boundaries.

| Candidate and setting | Tickets | Distinct states | Checked result |
| --- | ---: | ---: | --- |
| Provider effect fence, reachable | 2 | 3,312 | Three safety laws, erasure, target release, and reclaiming both charges hold. |
| Drain exact ticket completions, reachable | 2 | 504 | Same laws hold. |
| Provider effect fence, reachable | 3 | 26,952 | Same laws hold. |
| Drain exact ticket completions, reachable | 3 | 2,436 | Same laws hold. |
| Provider down, original custodian has room | 2 | 32 | Three safety laws and target release hold. |
| Provider down, original custodian has no room | 2 | 16 | Three safety laws hold. |
| Provider effect fence, ticket 1 never arrives | 2 | 744 | Three safety laws and all three progress properties hold. |

The safety laws check the closure and exact absence behind every erasure, absence across later deliveries, and a charge for all possible physical work.
Conditional progress after admission closure assumes weak fairness of the relevant enabled provider and custody actions.
The connected drain comparison grants fair delivery of queued writes.
An admitted upload that never arrives invalidates that assumption even if the provider can still install a fence.

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A152 | `local_close_is_fence`, `timeout_is_stop` | Certify erasure while a pending write still can land. It recreates bytes in four or five transitions respectively. |
| A152 | `wrong_receipt` | Treat completion of a sibling ticket as termination of a pending ticket and recreate bytes in nine transitions. |
| A152 | `check_only_at_admission` | Install the provider fence, certify erasure, and accept an old ticket at the effect point in six transitions. |
| A153 | `replay_writes_again` | Complete the first delivery, erase the bytes, and rematerialize them on a retry in seven transitions. |
| A153 | `lose_provider_fence`, `lose_consumption` | Restart forgets the provider fence or completion and permits rematerialization in seven or eight transitions respectively. |
| A154 | Drain a stalled ticket | With ticket 1 permanently stalled, an execution can keep an admitted write pending forever. Erasure under the effect fence still progresses in the same fault setting. |
| A154 | Erasure during provider outage | A fair execution with the provider inaccessible cannot verify physical erasure. |
| A155 | `charge_visible_only` | Transfer a record covering visible bytes alone and leave an authorized pending write uncharged in four transitions. |
| A155 | `release_before_charge`, `lose_custody` | Release before proving disposition in two transitions or lose the sole receiving charge at restart in four. |
| A156 | Require erasure before target release, or transfer without capacity | In either case, a permanent provider outage can prevent target charge release. |
| A156 | Retain receiving charge forever | Stable absence holds permanently and the receiving charge remains stranded. |

The six-transition fence witness rejects delivery of a still-pending ticket after confirmed erasure.
The seven-transition drain witness rejects a duplicate completed ticket after confirmed erasure.
The four-transition outage witness releases the target charge while a physical ticket remains pending under the original custodian.
The nine-transition witness transfers custody and returns the target charge before an old ticket materializes bytes. The custodian then establishes stable absence and returns its own charge.

## General proofs

Lean checked sixteen theorems using standard axioms only. [Provider proofs](ProviderIOClosure.lean) · [Disposition bridge](DispositionBridge.lean)
The exact provider effect checks both the version fence and the ticket state.
A consumed ticket stays consumed across arbitrary finite traces, including restart.
An observed provider fence or the exact observed completion of every issued ticket implies closure of all possible writes.
Once certified, absence survives every later transition.
An indistinguishability theorem exhibits two states with the same local closure, issued tickets, observations, and observed absence. A pending ticket can still land in one state.

The charge invariant gives either the target reservation, stable absence, or a custodian reservation covering the full footprint and every issued ticket.
The proof constructs target release while an old ticket is still eligible to land.
The bridge supplies the Study 39 disposition from an authenticated packet for the exact original copy.
An older custodian receipt remains safe to apply after later transitions. If the receiving charge has already been released, stable absence supplies the justification.
The acceptance theorem combines the exact registration release and scoped provider disposition and orders the target's cleanup.

The four proof controls fail when physical effect admission omits the provider fence, confirmation omits observed absence, takeover omits issued tickets, or verification accepts a receipt for another copy.

## Remaining obligations

The core model assumes a single immutable physical version already authorized for retirement.
Shared references and other rightful users must still be fenced or moved under the shared custody protocol.
The provider adapter must implement the modeled atomic effect boundary, authenticate the scoped state and its history, and recover the durable effect fence and ticket decisions.
The model abstracts the footprint reservation and does not count actual bytes or simultaneous takeovers.
Compaction of terminal ticket state and the physical effect namespace remain open.
[Study 41](../41-provider-ticket-compaction/report.md) checks compact live admission, recovered closure, and reuse of physical addresses.

Apply [A152–A156](../amendments.md#study-40--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves the commands, settings, traces and proof diagnostics in the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/40-provider-io-closure/run.py
```
