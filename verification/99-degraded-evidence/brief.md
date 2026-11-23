# Study 99 · Diagnose a failure or choose an exclusion

2026-11-23

## Question

Can the current owner use its surviving responses both to identify a physically failed AZ without false positives and to guarantee degraded admission whenever that AZ is unreachable?

## Sources

Use [Study 67](../67-full-admission/report.md) for exact surviving coverage and an existing fault allowance, and the [architecture decision](../architecture-reopening/comparison.md) for installed-group service without another decision quorum.

## Model and comparisons

Give a ready current owner the same two replies in two worlds, with a third AZ slow in one and unreachable in the other.
Compare inferring the missing AZ has physically failed, waiting for independent diagnosis, and choosing a degraded exclusion under an explicitly authorized policy.
The exclusion operates on the observed scope and states no conclusion about physical failure.
The selected candidate requires exact current recovery inputs.
Lean compares arbitrary pairs of observations.
TLC checks two survivors, one eligibility decision, one admission, and weak fairness of enabled actions.

## Boundaries

Hold configured authorization, exact inputs and the installed scope as explicit inputs.
This study isolates the observation problem.
It supplies neither a health detector nor a fault-budget transition proof.
The existing public protection and exclusion contract stays subject to product review.
Use Python 3.13, TLC 2.19, Java 21 and Lean 4.35.0.
