# Study 82 · Verify protected read checkpoint and handoff recovery

2026-11-23

## Verdict

A data frontier can stay fixed while a read closes, its slot is reused, and its protected basis changes.
Authenticate the result rows and snapshot holds together at the exact ordered control cut.
Restore each occupied row with its exact held basis.
Derive required read dependencies from that restored state before allowing recovery or activation.

A funded seal binds an immutable attachment for the protection state at its ordered cut.
The target opens that attachment locally, checks all original read dependencies, and then uses the existing funded activation decision.
A protected read can reissue with its original invocation through the installed target.
The sealed source leaves logical releases for the installed successor.
An independent physical endpoint can still finish its own borrow and submit exact stop evidence.

## Bounded comparison

[JointReadRecovery.tla](JointReadRecovery.tla) models two control images at the same fixed data frontier.
The older image has the original protected read.
The newer image records its closure and a different read in the reused slot.
A move may lose its original route after sealing, and exact original read dependencies can be unavailable.
The model distinguishes answering before closure from issuing afterwards.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Close and reuse before sealing | 8 | The exact newer control opens and serves through source loss. |
| Closure reaches the sealed source | 7 | The sealed image keeps its original open read, which the successor can serve after source loss. |
| Missing original basis | 3 | Coverage failure prevents activation. |
| Logical close at the installed target | 9 | The old read can answer before the close and cannot reopen afterwards. |

The two positive handoff cases use weak fairness for the valid enabled preparation, seal, route loss, mount, activation and answer actions.
The missing-basis and installed-close cases check safety.

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Match only the data frontier | Mount the older control in three transitions. A closed read answers through that mount in six. |
| Select results and holds independently | A result from the chosen image mounts with another image's hold in three transitions. |
| Omit the original read's media dependency | The target activates without the exact basis in four transitions. |
| Allow the sealed source to acknowledge a logical close | The successor installs the frozen read and answers after the acknowledged closure in six transitions. |
| Serve from a cached read after the installed successor closes it | A closed read answers in six transitions. |
| Recontact the old route after a verified mount | The fully covered target stalls forever after source-route loss. Temporal counterexample. |

These are small control histories with opaque image and basis identities.
They exercise ordered validity and progress under the specified route and coverage conditions.

## General proofs

[JointReadRecovery.lean](JointReadRecovery.lean) checks thirteen theorems with standard axioms only.

- The encoder writes each canonical result into the same typed control section as its snapshot hold table. A sound state round-trips. An undecodable occupied slot refuses the whole section. Every recovered row has a matching held basis, the same end cut and logical protection.
- The checkpoint opener uses the existing authenticated envelope and named catalog for the journal and read section. It checks the ordered position independently of the data frontier. A verified open retains every dependency derived from the original admitted bases. A missing required dependency prevents opening.
- The actual ordered source seal checks and retains the exact read attachment as part of its evidence. The install gate opens that retained attachment at the sealed ordinal and delegates to the existing funded activation. It can activate from the local image without recontacting the old route. The composed recovery program reissues the original caller's packet and retains every named original basis dependency.
- The authority-aware close gate refuses logical release at the sealed source and delegates exact release to the installed successor. Older proofs establish that exact release preserves other reads and refuses recycled permit identities.

The seal attachment contains the read section and its required storage references.
It carries no whole source image containing that same seal.
Checkpoint recovery names the complete typed control that includes both read and journal components.
This layout keeps references acyclic and retains the same ordered binding without a second ordering decision.

## Amendments and acceptance programs

[A322–A325](../amendments.md#study-82--2026-11-23) bind checkpoint and sealed storage references, require old basis coverage, and give logical close one authority during and after transfer.

- P154. Close and reuse a read slot at an unchanged data frontier. Restore the later exact checkpoint and refuse an old or mixed result and hold.
- P155. Deliver a logical close after the source seals. The sealed source cannot acknowledge it. The installed successor can apply exact stop or completion and then refuse the old invocation.
- P156. Restore an exact funded seal with outstanding reads. Refuse activation if one original basis dependency is unavailable. With full local evidence, activate during source loss and reissue the original read.

## Residue

The proof abstracts typed catalog identity and the issuer that certifies the exact projected read state at the ordered cut.
The full control and command wire encoders and joint replay of the projected read state still need refinement.
Actual dependency enumeration and media retention must cover the original root and suffix, even when they belong to former physical owners.
Real takeover, signer verification, and provider and endpoint settlement remain to be qualified.
Immutable stop evidence and an acknowledged logical close remain distinct events during handoff.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner checks the controls first and saves commands, configurations and raw logs under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/82-joint-read-recovery/run.py
```
