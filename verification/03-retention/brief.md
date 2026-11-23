# Study 03 · Bounded retention and replay admission

## Question

Can checkpoint publication, replay admission, and trim race without making an admitted replay unreadable, and which progress promises fit a finite recovery window?

## Sources and comparisons

Use S06, B01, P06, and P09 from the [requirements](../requirements.md).
RTDB already uses a directory CAS to coordinate the certified replica floor and replay registration in `TrimCertifiedReplicaPrefix` and `AdmitLatestCheckpointReplay`.
The baseline requires both final decisions to serialize against the same state.
The weakened candidates check only an earlier replay observation, check only an earlier trim observation, or use an uploaded checkpoint as authority to trim.
Further controls drop each of the two admission bounds.

## Model and properties

One stream has a committed head, an uploaded cut, a published cut, a retention floor, and one replay hold.
Replay and trim requests can stage their decisions before committing them.
Append work uses record count as the capacity unit.
The model can close an admitted hold and retry a staged operation.
It abstracts object contents, checkpoint trust and its digest, multiple replay holds, physical reclamation latency, bytes, expiry, scheduling fairness, and checkpoint control traffic.

| Property | Kind | Requirement |
| --- | --- | --- |
| `PublishedBeforeTrim` | Safety | Trim cannot pass the published reconstructable cut. |
| `ReplayProtected` | Safety | An admitted replay can still read its first requested LSN. |
| `RecoveryBound` | Resource safety | The suffix above the published cut fits its replay budget. |
| `RetainedBound` | Resource safety | The suffix above the retention floor fits its separate retention budget. |

## Rules

Use the shared pinned TLC runner at five and eight LSNs, with budgets of two and three records.
Use Lean 4.35.0 for unbounded arithmetic consequences.
Run controls first, then clean baselines and reachability witnesses.
Report comparison, controls, programs, assumptions, and reproduction in the [report](report.md).
