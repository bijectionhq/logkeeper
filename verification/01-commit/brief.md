# Study 01 · Commit authority

## Question

Can two durability designs implement the same ordered append, fencing, retry, and read-barrier contract through a single AZ loss?

## Sources

Use the [requirements](../requirements.md), the RTDB contract cited there, and the proposed Logkeeper endgame.
The comparison candidate is inspired by [WarpStream's published write path](https://docs.warpstream.com/warpstream/overview/architecture/write-path).
This is a comparison of two candidate designs, with a shared model and property list.

## Model and abstractions

Model one stream, two writer epochs, two payloads, one in-flight append, three AZs, and at most one permanent AZ loss.
Both candidates use a serializable, durable ordered authority.
The quorum candidate stages exact payload bytes on individual voters and commits using a majority.
The object candidate first persists an immutable object, assumed to survive one AZ loss, then commits its reference in the same ordered authority.
An in-flight proposal can be forgotten.
Network delay is represented by scheduling persistence and commit separately from proposal arrival.
A committed operation and its externally delivered receipt are separate steps.

The model abstracts authority leader election, disk recovery, multiple streams, simultaneous pending proposals, authority partitions with fewer than two survivors, and writer authentication.
With one uniquely authorized holder per epoch, a writer grant is represented by its epoch.
Read barriers are atomic authority observations.
Actual network invocation and response intervals require a refinement study.
Checkpoint, trim, membership changes, erasure, and liveness are outside this model.

## Properties and comparisons

Both candidates check S01 through S05, for precisely the safety slices stated below.

| Property | Kind | Scope |
| --- | --- | --- |
| `DenseHistory` | Safety | Committed sequence entries occupy their own LSN. |
| `ReceiptMatchesCommit` | Safety | Every positive receipt matches an exact committed request. |
| `Recoverable` | Safety | Every committed entry has a surviving durable payload. |
| `Fenced` | Safety | Each commit used the writer epoch installed at the decision. |
| `ExactFenceCut` | Safety | The fence returns exactly the earlier epoch's committed prefix. |
| `ExactBarrier` | Safety | Each recorded barrier cut equals the authority's committed cut at observation. |

Finite reachability witnesses cover P01, P02, the single-AZ continuation of P03, P04's delayed-writer refusal state, and the staged write in P05.
A reachability witness establishes existence of a trace, with progress under contention left open.
Witness runs record extra observations using `TraceAcceptance`, which changes no protocol guards.

## Rules

Run deliberate mutations first with the TLA+ tools 1.7.4 distribution pinned by SHA-256.
One worker, a 512 MiB JVM heap, and a 60-second limit per run are sufficient for the configured bounds.
The runner checks the expected invariant name and exit status.
It keeps exact configurations, commands, and raw logs in ignored local directories within the study.
If the tool cannot run, record the blocker and leave the result open.

## Report

Record verdict, property results and bounds, comparison, amendments, acceptance programs and their cost, residue, and reproduction in [the report](report.md).
