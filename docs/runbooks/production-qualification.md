# Production qualification in staging

Record evidence against the exact Logkeeper image digest and RTDB binary or
image digest. Include the Git commits, keeper configurations with secrets
redacted, topology, volume classes and mount options, and the test start and
finish times. Run each destructive drill on an isolated cell with synthetic
data, independent enrollment and credentials, and no production endpoints.

## Build and compatibility

- Run the repository CI on Linux and macOS. Retain the consensus seed range
  and logs, TLA+ state counts, and proof tool versions and results.
- Run the real N−1 keeper binary through the rolling-upgrade tests. In staging,
  run the pinned RTDB build before, during, and after one-keeper-at-a-time
  replacement. Verify all acknowledged transaction receipts after every cut.
  Rehearse rollback before finalizing a feature level that N−1 cannot read.
- Run the RTDB two-voter process drill on the exact artifacts. It creates six
  keepers and a replicated catalog on one machine, durably retires both lost
  identities, checks that they refuse restart, and compares every observed
  transaction receipt before and after recovery.

  ```sh
  python3 verification/measure/rtdb_recovery.py \
    --logkeeper /path/to/logkeeper --rtdb /path/to/rtdb \
    --rtdb-source /path/to/rtdb-checkout --max-rto-seconds 90 \
    /path/to/new-run-directory
  ```

  Install the RTDB benchmark's Python dependencies first. Keep
  `results.json` and the logs. The work directory contains throwaway private
  keys and should be kept separately from the evidence. The 90 seconds in
  this example is a local drill budget. Record the staging budget separately.

## Independent hosts and storage

Use six keeper hosts or dedicated nodes across three availability zones,
two keepers per zone, with separate persistent block devices and independent
enrollment durability. Verify that every normal stream and the replicated
catalog place voters in three distinct domains.

1. Drive commits from an independent RTDB client. Save the acknowledged
   transaction ID, basis, system time and outcome in an external ledger.
   Record commit latency, throughput, refused or timed-out transactions,
   repair delay, and time to restore three voters.
2. Isolate one keeper and then one zone at the network boundary. In the
   one-zone test, isolate both keepers in that zone and their keeper lanes.
   Record the sustained load, quorum health and time before new commits
   succeed. Recheck every receipt after each fault and after restoring the link.
3. Drill slow storage, full storage, failed I/O, abrupt host power loss and
   media replacement on disposable staging volumes. Keep the enrollment
   authority separate from the volume being faulted. Record the injected
   fault, WAL and disk metrics, watchdog exits, offline verification and
   recovery results. See [corruption](corruption.md) and
   [replace a failed disk](replace-disk.md).
4. Rehearse a stopped survivor with the two old voters partitioned on a
   still-running network. Confirm recovery refuses without both proofs.
   Finish the [signed retirement procedure](lose-two-voters.md), recheck
   all receipts, and verify that both retired identities fail at restart.
5. Lose catalog quorum and interrupt a joint membership transition. Verify
   catalog-changing requests and unsafe forced recovery refuse. Restore
   enough of the original participants to regain the required quorums and
   verify the prior committed placements and transaction receipts.
6. Run production-shaped workload and repeated one-keeper failures through
   the release soak. Include checkpointing, trimming, parked-stream repair,
   near-quota workloads, peak bursts and snapshot transfer. Save timeseries
   through the end of repair.

A process kill exercises process and journal restart. Use a VM or host
power interruption on the staging volume class to collect evidence about
device flush durability.

## Service objectives and paging

Choose peak and sustained load, record-size distribution, commit p95/p99,
application error budget, maximum failover duration, and maximum repair
duration before running the soak. Record the same limits for the intended
staging and production topologies. The acceptance criteria for failures that
leave a durable quorum include zero lost acknowledged receipts and preserved
transaction ordering. Record the exact verified RPO and end-to-end RTO for
every accepted loss scenario separately.

Use the [keeper alerts and dashboard](../../README.md#operations) together
with RTDB commit latency, checkpoint age, recovery acknowledgements, and
journal faults. Route and test at least one page for a lost WAL, leaderless
stream, replica quarantine, near-full storage, and RTDB journal shortening.
Have the on-call operator collect a debug bundle, identify affected streams
and confirm the relevant runbook on the staged cell.

Verify signed mTLS identities for keeper, RTDB, operator and metrics roles.
Test missing, expired, wrong-CA and revoked or rotated credentials.
Trial the overlapping trust-bundle and key rotation sequence while requests
are live, including long-lived connections. Audit which principals share
stream access and choose a separate cluster wherever writers or readers
belong to distinct trust domains. Check that the keeper's volume, enrollment,
runtime and network permissions match the intended boundaries.

## Backup, migration and rollback

Require a cold restore into a fresh cell from application artifacts alone.
Use a new cluster identity, new keeper UUIDs and enrollment, and new
credentials. Isolate the old cell's writers. Record the last proven snapshot
or application export, recheck transaction and data invariants, and measure
what could not be restored against the agreed RPO and RTO. Preserve the
storage and key material needed by the application backup independently of
the source journals and catalog.

Test [cutover](cutover-from-stream-keeper.md) on representative databases.
Exercise abort before writes, then exercise a reverse transfer after the
new cell accepts writes. Compare the source and destination at each closed
cut and test credential, routing and data barriers. Retain the old cell
until the last reversible point has been demonstrated. Document which
backup mechanism and database classes the evidence covers.

Record a pass for a gate only when it ran against the identified artifact
pair and topology. Missing evidence, loss of an acknowledged receipt in a
quorum-preserving test, and an untested cold restore block production signoff.
