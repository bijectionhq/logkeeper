# Study 15 · Replay permit identity and composition

## Question

Can an acknowledged close fence a delayed admission without closing a different reader, and can the snapshot combine that logical rule with exact physical borrowing?

## Sources and model

Use S06 and P06 from the [requirements](../requirements.md), the [retention races](../03-retention/report.md), and the independent [physical read-custody model](../14-read-custody/report.md).

TLC models two or three independently allocated permits, two start positions, and one move.
A preparation allocates a durable nonce and leaves an authenticated envelope that can be delayed.
Admission checks the current reservation and its exact start LSN.
Close clears an exact issued nonce.
Trim protects all holding permits.
The destination inherits both active reservations and the issuance high-water mark.
Mutants reopen from an old envelope, close by range, check only the latest permit, or lose prepared state or issuance metadata during installation.

Generalize the reference kernel to an arbitrary table of permits with monotone issuance.
Prove that an issued and spent nonce cannot be reused by any finite trace and that closing it leaves other permits unchanged.
Compose that kernel with the physical read model with one tracked permit and arbitrarily many bounded operations.
New borrows need an exact logical record within the admitted range.
A logical action preserves that permit while its admission gate stays open.
Once it closes, already-borrowed exact inputs remain independently protected.

## Rules

Run the pinned TLC and Lean runners and save both counterexamples and accepted traces.
Require the weakened reference and composition controls to fail at the intended proofs.
Report exact coverage and physical-fence premises in the [report](report.md).
