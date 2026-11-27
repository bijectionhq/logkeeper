# Capacity expansion

## More disk on a keeper

The keeper reads free space from the filesystem live (`fs2::available_space`),
so growing the media filesystem online takes effect without a restart:

```sh
sudo xfs_growfs /var/lib/logkeeper/media      # or resize2fs for ext4
curl -sS $ADMIN/metrics | grep '^logkeeper_consensus_accepting'   # 1 [ops]
```

The allocation unit must stay at or below 16 KiB. A keeper that was full
(`accepting 0`, `Full` refusals) resumes once the allocator reports the room,
including the 88 MiB headroom. Do this before streams hit their quota. Watch
`near_quota_ceiling` in `/problems`.

## More streams per keeper

`max_streams` (default 128) limits streams with an open group. Parked streams
do not count, so most RTDB deployments run far more databases than 128 per
keeper, as long as fewer than 128 are active at once. A keeper at the limit
refuses to open more groups ("keeper stream limit reached"). To raise it,
set `max_streams` in each keeper config, then restart the keepers one at a
time (see [rolling upgrade](rolling-upgrade.md), steps 5 to 8). Size memory
first: about 1 MiB per open group plus 300 bytes per retained record per
voter (see the [sizing section](../deployment.md#sizing)).

## More keepers

Add keepers in whole sets, one per domain, so placement stays balanced across
the three domains. Follow [add a keeper](add-drain-remove-keeper.md#add-a-keeper)
for each, then add them to RTDB's `placement`.

- **New streams** are placed by rendezvous ranking, and placement skips keepers more than
  a quarter above the average. New databases therefore land mostly on the new
  keepers.
- **Existing streams** do not rebalance by themselves. To move load, drain
  part of a busy keeper: list it in `draining` until enough streams have
  moved, then remove it from `draining` again. Each move copies the stream to
  a learner and is paced by the 64 MiB/s keeper-wide snapshot send rate
  (`snapshot_send_bytes_per_second`).

## More catalog capacity

The catalog stream compacts itself after 1,024 records. It needs no
expansion. Only its voter count matters, and that is fixed at three.
