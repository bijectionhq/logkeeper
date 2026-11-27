# Consensus keeper runbooks

Each runbook gives the exact commands, the output to expect, and when to stop.
Read [the deployment guide](../deployment.md) first. Steps marked **[ops]** or
**[upgrades]** depend on features that are still landing (see the guide's
introduction), and each says what to do without them.

| Runbook | When |
| --- | --- |
| [Rolling upgrade](rolling-upgrade.md) | A new keeper release |
| [Add, drain or remove a keeper](add-drain-remove-keeper.md) | Changing the keeper set |
| [Replace a failed disk](replace-disk.md) | A keeper's media is lost or replaced |
| [Lose two of three voters](lose-two-voters.md) | A stream has one surviving voter |
| [Corruption](corruption.md) | Verify failures, quarantined streams, a disabled keeper |
| [Certificate rotation](certificate-rotation.md) | Keeper, client or CA certificates |
| [Capacity expansion](capacity-expansion.md) | More disk, more streams, more keepers |
| [Cutover from the stream keeper](cutover-from-stream-keeper.md) | Moving RTDB Multi to the consensus keeper |

## Conventions

The commands assume the systemd layout from `deploy/consensus/`:

```sh
CONFIG=/etc/logkeeper/keeper.json     # this host's keeper config
ADMIN=http://127.0.0.1:5741           # this host's admin listener [ops]
UNIT=logkeeper-consensus              # systemd unit
lk() { sudo -u logkeeper /usr/local/bin/logkeeper "$@"; }
probe() { curl -sS -o /dev/stderr -w '%{http_code}\n' "$ADMIN/$1"; }
```

`lk admin ... --config operator.json` runs the operator's client; the file
holds an administrator certificate and every keeper's application and admin
address (see `deploy/consensus/operator.example.json`).

`probe ready` prints the JSON body and then the HTTP status: `200` means
yes, and `503` means no. On Kubernetes, run the same commands inside the pod
with `kubectl -n logkeeper exec logkeeper-N -c keeper -- curl -sS
http://127.0.0.1:5741/ready`. Stop and start keepers by deleting the pod or
updating the StatefulSet, never with `kubectl exec ... kill`.

**General abort rule.** Stop any procedure, and change nothing else, if any
of these appears on a keeper:

- `/problems` shows a stream as `leaderless`;
- a stream has fewer than two live voters that the procedure did not expect;
- `/live` fails on a keeper you did not stop.

Then work out why before you continue.

Without **[ops]**, use the keeper's stderr (`journalctl -u $UNIT`): it prints
refusal counters every 5 s. For per-stream health, use `lk admin status
--stream UUID`, which reads the configuration, leader, head and each voter's
replica over the application lane.
