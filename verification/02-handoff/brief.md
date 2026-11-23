# Study 02 · Authority between replica groups

## Question

Can a stream safely finish an already authorized move when its placement directory is down, and what evidence must cross the boundary before the successor can commit?

## Sources

Use S07, L01, L02, and P07 from the [requirements](../requirements.md), along with [study 01](../01-commit/report.md) for the single-authority contract.
RTDB's present `StaticStability` and `HandOff` rules are integration inputs.
The distinction between a configured successor and an activated configuration has a precedent in [Vertical Paxos II](https://lamport.azurewebsites.net/pubs/vertical-paxos.pdf).

## Model and abstractions

Two independent groups hold the source and target of one move of one stream.
The groups each serialize their own durable operations.
The source starts writable.
The directory can authorize an intent and then fail.
A network partition can prevent the groups from exchanging state while clients can still reach either group.
Old routes stay usable as requests to the old group.
Precopy can race source appends.
The final installation verifies the source's sealed prefix and installs it durably in the target.
The move slot fixes the source, target, and generation, with identity and certification abstracted as authentic.
There is no cross-group atomic operation.
Append payloads are either A or B, and each history is bounded at two records.

Directory reachability and the inter-group link can change independently.
Durable protocol facts survive the loss of any coordinator response.
The model abstracts individual RPCs, retry transport, group membership, proof encoding, and the storage holding the certified cut.
At this level `Install` is one group commit after carrying the seal and the exact prefix.
Retirement, trim, and redirect chain bounds remain separate studies.

## Comparisons

- **Directory activation.** The source seals and the target installs. The target activates after the directory grants the new placement.
- **Portable activation.** The source commits the authorized successor before sealing. The target activates after installing the authenticated seal and exact prefix. The directory learns the new route independently.
- **Deliberate weakenings.** Activate an isolated target without proof, install a precopy without comparing to the seal, or reopen the source after a disconnection.

## Properties

| ID | Kind | Statement |
| --- | --- | --- |
| `SingleAuthority` | Safety | At most one group can commit. |
| `NoFork` | Safety | Histories agree at every shared LSN. |
| `ExactCut` | Safety | Once the target activates, its installed cut includes the entire source prefix. |
| `WithDirectoryProgress` | Liveness | After authorization, stable links and directory availability suffice for eventual activation. |
| `LinkOnlyProgress` | Liveness | After authorization, a stable inter-group link suffices for eventual activation, even after directory loss. |
| `InstalledProgress` | Liveness | Once the exact cut is installed, the target can finish activation without inter-group connectivity or directory availability. |

Liveness assumes both group quorums continue to operate and weak fairness for the durable handoff actions.
The entire state graph includes arbitrary finite outages and stuttering.
The progress formula imposes eventual stable connectivity only where the guarantee needs it.

## Rules and report

Pin TLA+ tools 1.7.4, use one worker and 512 MiB heap, and stop each check after 60 seconds.
Check deliberate weakenings before both baselines.
Run Lean 4.35.0 for the unbounded abstract boundary and exercise a deliberate failed theorem for each law.
Record verdict, exact strengths, comparisons, counterexamples, acceptance programs and assumptions in the [report](report.md).
