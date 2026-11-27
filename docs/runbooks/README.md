# Consensus keeper runbooks

Each runbook gives the exact commands, the output to expect, and when to stop.
Read [the deployment guide](../deployment.md) first.

| Runbook | When |
| --- | --- |
| [Staging qualification](production-qualification.md) | Evidence for a production readiness review |
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
KEEPER=$(jq -r .keeper "$CONFIG")     # this host's keeper UUID
ADMIN=http://127.0.0.1:5741           # this host's admin listener
UNIT=logkeeper-consensus              # systemd unit
lk() { sudo -u logkeeper /usr/local/bin/logkeeper "$@"; }
probe() { curl -sS -o /dev/stderr -w '%{http_code}\n' "$ADMIN/$1"; }
```

`lk admin ... --config operator.json` runs the operator's client; the file
holds an administrator certificate and every keeper's application and admin
address (see `deploy/consensus/operator.example.json`).

`probe ready` prints the JSON body and then the HTTP status. `200` means
ready, and `503` means unready. The Kubernetes loopback probe endpoint is
available through `kubectl --context "$STAGING_CONTEXT" -n logkeeper exec
logkeeper-N-0 -c keeper -- curl -sS http://127.0.0.1:5742/ready`.
For planned Kubernetes pod replacements, use the
[guarded rollover procedure](rolling-upgrade.md#kubernetes).

**General abort rule.** Stop any procedure, and change nothing else, if any
of these appears on a keeper:

- `/problems` shows a stream as `leaderless`;
- a stream has fewer than two live voters that the procedure did not expect;
- `/live` fails on a keeper you did not stop.

Then work out why before you continue.

For per-stream health, use `lk admin status --config operator.json --stream
UUID`, which reads the configuration, leader, head and each voter's replica
over the application lane. `lk admin problems --config operator.json` merges
every keeper's `/problems`.

For an incident, collect a debug bundle before changing anything:
`lk keeper debug-bundle --config $CONFIG --out /tmp/bundle.tar` writes a tar
with this keeper's redacted config and the admin pages of every keeper it
reaches. With `admin.mtls: true` it also fetches the keepers listed in
`admin.cluster`, using the keeper's own certificate. With loopback-only
listeners, run it on each host. Add `--data` on a stopped keeper to include
offline `inspect` and `verify`. `probe status` gives one keeper's summary
page.
