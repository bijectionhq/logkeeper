# Study 12 · Journal voter replacement

## Question

Can a journal group replace a voting member while preserving the exact acknowledged cut and excluding stale commits from its old membership?

## Sources and comparisons

Use S01, S02 and S07 from the [requirements](../requirements.md), the [commit study](../01-commit/report.md), and the retained cut required by the [placement refinement](../11-authority-refinement/report.md).
RTDB's `LogService` contract distinguishes a durable journal identity from its address and requires an intersecting seal quorum.
[Raft membership changes](https://raft.github.io/raft.pdf) supply the joint-majority comparison.
The [reconfiguration literature](https://lamport.azurewebsites.net/pubs/reconfiguration-tutorial.pdf) distinguishes authoritative ordering from the mechanics of moving data.

Compare direct replacement of the voters, a joint phase that admits commits through both majorities, and a sealed, write-paused transition that hands off an exact cut.
In both safe candidates an old majority durably fences old-only votes before the transition, and new membership is adopted only with a certified durable cut.

## Model and properties

The old voters are {1, 2, 3} and the new voters are {2, 3, 4}.
Voters 1 and 4 have distinct durable identities in the same AZ, so loss of that zone excludes both.
The other voters occupy different AZs.
Each voter can hold metadata about the acknowledged end independently of the payload bytes.
A staged learner copy can be tested with the wrong bytes and the right length.
The witness separates an old command's durable decision from delivery of a late response.

Check that stale old-only voters cannot produce a new positive result, that every available recovery majority can read the exact acknowledged record, and that at least one eligible copy survives a modeled AZ loss.
Use one replacement, histories of at most two or three records, two payload values, and at most one AZ loss.
Commit and ordered membership decisions are abstract, indivisible events with explicit storage and vote premises.
The model does not run leader election, ballots, snapshot installation, or actual network replication.

## General proof

Import the existing Lean reference kernel.
Model record coverage as an exact durable majority for every still-retained entry.
Show that append, checkpoint and trim decisions refine the kernel and that membership, staging and reclamation stutter.
Prove by induction that every trace preserves the retained cut when the new membership is certified before finalization.
Independently show old-majority fencing, distinct-zone quorum survival, and the counterexample to intersection across merely overlapping voter lists.
Use no unstated quorum disjointness or read availability assumption.

## Rules

Use the pinned TLC and Lean 4.35.0.
Run weakened guards before baselines.
Record exact assumptions, controls and reproduction in the [report](report.md).
