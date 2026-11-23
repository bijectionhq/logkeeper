# Study 05 · Move and retirement composition

## Question

What happens when terminal retirement races a portable move and the client still points at the source?

## Sources and scope

Compose the authority-transfer rules from [study 02](../02-handoff/report.md) with the custody and retirement rules from [study 04](../04-retirement/report.md).
Use S07, S08, and P08 from the [requirements](../requirements.md).
The model has one move and three possible locations, including an optional earlier copy.
History is represented by its length.
Independent source and target serving states are explicit.
The model ignores byte contents, repeated moves, cloud storage behavior, and network liveness.

## Comparisons and laws

The baseline serializes the source's terminal and seal decisions, makes retirement receipts specific to the current owner, and transfers outstanding custody with the exact cut.
Mutations permit sealing after retirement, allow a sealed predecessor to acknowledge global retirement, and drop old custody when the successor installs.

Check unique authority, exact cut, terminal receipt semantics, absence of appends after a terminal receipt and complete erasure scope.
Witness both outcomes of the race.
An acknowledged source retirement wins before seal.
A request reaching the sealed source follows the redirect and retires at the successor.

## Rules

Run the controls first in TLC, then exhaust the two- and three-LSN baselines and produce the two acceptance traces.
The [report](report.md) contains outcomes and reproduction.
