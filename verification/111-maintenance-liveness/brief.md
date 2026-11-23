# Study 111 · Keep the maintenance lane live under repeated writer replacement

2026-11-23

## Question

Can the installed journal's fixed maintenance reserve always admit the records needed to publish the next checkpoint, whatever the number of writer replacements?

## Model and comparisons

Compare the per-term claim design with deriving the term from the Logkeeper grant, and with a grant that the journal does not fence.
Use TLC 2.19 for headroom, single upload per block and eventual checkpoints, and Lean 4.35.0 for a bound under any number of replacements.
