# Stream journal measurements

## Host and method

The measurements ran on a Mac mini (Mac18,5, Apple M6, 12 CPU cores, 24 GiB RAM, macOS 27.0 build 26A425). All processes, the proxy, and the keeper WALs shared the host and its internal APFS SSD. The host also ran other builds during the evaluation. Absolute tail latency is specific to this setup.

Each scenario starts fresh `logkeeper keeper --config` processes with distinct keeper certificates and directories. The benchmark's clients use the shipped `Writer`, `TcpTransport`, and mutual TLS. All mutation acknowledgements pass through the keeper's normal WAL path, which calls `fsync` on this host. The benchmark runtime uses four worker threads and each keeper runtime uses two, plus its WAL thread. The default keeper round admits 64 requests and charges at most 4 MiB per stream. Each proxy delays both directions by RTT/2, including TLS handshakes, using a separate monotonic deadline thread. The queue preserves byte order and pipelines large records. A 1,000-sample one-byte TCP echo measures the resulting delay before each scenario series.

The commit workload uses 256-byte records. A producer submits one batch of 1 or 32 concurrent `Journal::append` calls, then waits for its acknowledgements. Batch size is the number of calls in flight per stream. The shipped writer sends one data record per keeper append RPC. Every stream is initialized before timing and participates in every pass. Up to 256 producers are admitted at once. The retry at 10,000 streams with batch size 32 uses a single pass and admits 64 producers. Ack latency starts after producer admission. The producer queue, final batch acknowledgement, and total record throughput are reported separately. The general default issues at least 1,000 records and at least two passes. The benchmark retries `Unavailable` from mutations for up to 60 seconds per call. Percentiles use nearest rank.

The head workload uses one caller per stream, across 32 streams, and uses a separate read-only certificate for observers. Under load, the same streams continuously append. Requests are counted when the transport is invoked and completions when the transport returns. Transport errors are counted separately. A losing quorum call can be dropped before or after transmission. The rates count logical RPC envelopes and exclude frame fragments and TLS records.

The kill and partition cases use 256-byte records that were acknowledged before the event. Per-stream recovery runs from the event to the first subsequent append acknowledgement. The ack gap starts at that stream's last pre-event acknowledgement and includes any pre-event skew from the warm-up wave. The harness writes one row per stream to an ignored CSV file. The kill case sends SIGKILL to a real keeper. The partition case blackholes one keeper link for 3,000 streams, then immediately starts the 1,000 claims whose consumer lease policy has authorized takeover. It times seal, applying the acknowledged record through the returned head, and the first new append. The surviving writer also appends on the unaffected streams. This measures the claim burst after authorization. Consumer lease expiry and drift are outside the interval.

Replacement begins when a fresh learner process is ready. The retired keeper is already stopped. Every stream starts with one retained 256-byte record. For each parked stream, setup uses the keeper protocol to seed two durable copies, one on the lost keeper and one on alternating survivors. The active streams are seeded with the shipped writer. The harness runs the shipped sweeper on up to 64 independent streams while 1% of the streams continue writing at up to one append per second each. After the idle streams move, the active writers drain and their streams move. A separate post-timing pass checks the learner's installed ensemble, voting status, head, and last retained payload for every stream.

The noisy-neighbour case runs one stream with 8 MiB records at a paced target of 200 MB/s, plus 32 small-record neighbours. Each run lasts four seconds plus the time to drain admitted calls. The 64 MiB comparison setting leaves every hot record unfragmented by the per-stream cap. Reported MB/s is acknowledged payload per second, using decimal MB.

## Reproduce

Run from the Logkeeper worktree root. Copy the release executables into the ignored results directory to keep a reproducible pair when using the shared build target.

```sh
/Users/sachaichbiah/code/codesign-agents/guarded-cargo.py logkeeper \
  build --release --features stream --bin logkeeper --example stream-measure
out=verification/.results/measure
artifacts=/Users/sachaichbiah/code/codesign-agents/logkeeper-target/release
mkdir -p "$out/bin"
cp "$artifacts/logkeeper" "$artifacts/examples/stream-measure" "$out/bin/"
verification/measure/run.sh "$out/bin/logkeeper" "$out/bin/stream-measure" 1000 2000 \
  > "$out/cases.jsonl" 2> "$out/cases.stderr"
```

Run a single case with `stream-measure KEEPER CASE RTT_US`. `scale-check` is the batching regression guard described under node-level batching. `commit` accepts stream count, batch size, batches per stream, and the producer admission limit. `head`, `kill`, `partition`, `replace`, and `hot` accept an optional stream count. `pool-check` fails if a warmed 64-channel route reconnects during 24 more waves of 64 concurrent `Check` calls.

## Node-level batching

This section compares the N7 build (`f14f65e`, "before") with the node-level batching build ("after") in back-to-back runs on the same host, at the 1 ms profile. Both builds ran the same harness: commit, head and noisy neighbour. The 10,000-stream batch-32 case ran with both 64 and 256 admitted producers. The calibrated echo was 1.57 / 1.60 / 1.73 ms before and 1.57 / 1.60 / 1.64 ms after (p50 / p99 / p99.9). The 64-channel pool check reopened no connections in either build.

What changed:

- **One connection per keeper.** Every writer in a process shares one long-lived mutually authenticated connection per keeper. Calls queued while a frame is written are coalesced into one `Request::Batch`, up to 4 MiB. Frames are pipelined. The keeper decides a connection's frames concurrently, so it can group them, and answers them in order. A keeper round admits whole envelopes, so a batch is decided and synced in one round. Waiting reads and requests of 1 MiB or more keep using pooled exclusive channels.
- **Appends amortize.** Before, each lane sent one record per keeper append, so one stream's batch of 32 used 32 sequential keeper rounds on every lane. A lane now sends the contiguous run of known records in one append. Committed payloads stay in writer memory, up to 1 MiB per stream, until every lane holds them, so a lagging lane no longer issues one `Recover` and one append per record. A batched retry after a lost reply would overlap the keeper's tail and be refused as `Conflict`. A lane therefore retries one record after an uncertain result, and adopts the keeper's reported tail.
- **Fresh observer reads.** Before, every settle round resampled the maximum eligible tail. Under continuous writes, a newly accepted record is almost always ahead of the published heads, so the call spent its 25 ms settle budget chasing it and returned `Unavailable`. The observer now pins its read index from its first quorum round and waits for quorum head coverage of that index. Any committed position at or above the index covers every append acknowledged before the call, so read-index linearizability is unchanged.
- **Background WAL rotation.** With batching in place, 10,000 streams at batch 32 still had periodic 4 s stalls. Instrumentation showed that each full 64 MiB segment checkpointed all 10,000 dirty streams inline, taking about 3.8 s on every keeper. That is roughly five file or directory syncs per stream, and APFS serializes them, so running 16 checkpoint threads made no difference. With rotation disabled in a probe build, the same case ran at 492,000 records/s with no transport errors. Rotation now writes the checkpoints on a worker thread, as of the segment boundary, while rounds continue in the next segment. Old segments are retired only after every checkpoint is durable. Delete still rotates synchronously.

### Commit

Latencies are `p50 / p99 / p99.9` in ms. New connections are summed over the three keeper links.

| Build | Streams | Batch | Admitted | Records | Record ack | Batch ack | Queue p99 | Records/s | Transport errors | New connections |
| --- | ---: | ---: | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: |
| before | 1 | 1 | 1 | 1,000 | 3.90 / 4.03 / 5.07 | 3.90 / 4.03 / 5.07 | 0.00 | 256 | 0 | 0 |
| after | 1 | 1 | 1 | 1,000 | 3.95 / 4.09 / 6.00 | 3.95 / 4.09 / 6.00 | 0.00 | 253 | 0 | 0 |
| before | 1 | 32 | 1 | 1,024 | 30.82 / 58.46 / 63.26 | 55.58 / 63.83 / 63.83 | 0.00 | 568 | 0 | 505 |
| after | 1 | 32 | 1 | 1,024 | 5.85 / 6.10 / 6.36 | 5.94 / 6.45 / 6.45 | 0.00 | 5,391 | 0 | 0 |
| before | 100 | 1 | 100 | 1,000 | 6.49 / 14.50 / 17.37 | 6.49 / 14.50 / 17.37 | 0.00 | 13,229 | 0 | 14 |
| after | 100 | 1 | 100 | 1,000 | 3.84 / 5.76 / 5.85 | 3.84 / 5.76 / 5.85 | 0.00 | 24,530 | 0 | 0 |
| before | 100 | 32 | 100 | 6,400 | 75.05 / 185.37 / 192.50 | 136.74 / 193.52 / 194.05 | 0.00 | 19,635 | 0 | 1,910 |
| after | 100 | 32 | 100 | 6,400 | 8.64 / 11.77 / 12.20 | 8.65 / 11.91 / 12.23 | 0.00 | 301,582 | 0 | 0 |
| before | 1,000 | 1 | 256 | 2,000 | 17.22 / 18.22 / 18.56 | 17.22 / 18.22 / 18.56 | 52.38 | 14,644 | 0 | 5 |
| after | 1,000 | 1 | 256 | 2,000 | 5.44 / 8.48 / 8.92 | 5.44 / 8.48 / 8.92 | 17.66 | 43,148 | 0 | 0 |
| before | 1,000 | 32 | 256 | 64,000 | 156.73 / 324.96 / 343.45 | 289.81 / 344.33 / 345.59 | 920.74 | 27,615 | 0 | 162 |
| after | 1,000 | 32 | 256 | 64,000 | 8.20 / 16.84 / 19.08 | 8.23 / 16.85 / 19.09 | 31.87 | 866,278 | 0 | 0 |
| before | 10,000 | 1 | 256 | 20,000 | 19.96 / 146.29 / 167.83 | 19.96 / 146.29 / 167.83 | 1080.19 | 10,878 | 0 | 7 |
| after | 10,000 | 1 | 256 | 20,000 | 3.98 / 6.01 / 7.62 | 3.98 / 6.01 / 7.62 | 154.71 | 63,148 | 0 | 0 |
| before | 10,000 | 32 | 64 | 320,000 | 70.44 / 20023.41 / 22167.59 | 160.75 / 22167.42 / 23866.91 | 275128.19 | 1,161 | 1,134,468 | 153,580 |
| after | 10,000 | 32 | 64 | 320,000 | 4.16 / 7.09 / 11.69 | 4.21 / 7.41 / 11.75 | 685.67 | 457,401 | 0 | 0 |
| before | 10,000 | 32 | 256 | 320,000 | 1831.04 / 17227.78 / 18702.82 | 3764.28 / 18709.56 / 19269.96 | 205196.89 | 1,542 | 811,302 | 105,559 |
| after | 10,000 | 32 | 256 | 320,000 | 8.46 / 17.87 / 19.11 | 8.48 / 17.91 / 19.16 | 350.70 | 874,353 | 0 | 0 |

Throughput scales with the stream count until the 256-producer admission limit, at about 0.87 million records/s. At 10,000 streams with batch 32, transport errors fell from about 1.1 million to zero, and new connections fell from about 150,000 to zero. On one stream, batch 32 now delivers 5,391 records/s against 253 at batch 1. The keeper cost per record falls about 21-fold, and the record median rises only from 3.95 ms to 5.85 ms. Before, batch 32 was 2.2 times batch 1 throughput and had a 7.9 times higher record median. The single-stream batch-1 cost is unchanged. It still needs an accept round and a publication round.

### Head

| Build | Load | Caller | OK | Unavailable | Head | RPC starts/s | Writer data and publication starts/s | Transport errors |
| --- | --- | --- | ---: | ---: | --- | ---: | ---: | ---: |
| before | idle | writer | 1024 | 0 | 1.76 / 7.45 / 8.01 | 37,493 | 0 | 0 |
| after | idle | writer | 1024 | 0 | 1.67 / 1.74 / 1.74 | 57,433 | 0 | 0 |
| before | idle | observer | 1024 | 0 | 1.73 / 6.97 / 7.56 | 40,822 | 0 | 0 |
| after | idle | observer | 1024 | 0 | 1.68 / 3.55 / 3.56 | 55,193 | 0 | 0 |
| before | write | writer | 748 | 276 | 5.98 / 821.46 / 1054.07 | 7,534 | 3,843 | 9,485 |
| after | write | writer | 1024 | 0 | 4.07 / 4.37 / 4.42 | 68,573 | 47,896 | 0 |
| before | write | observer | 735 | 289 | 9.03 / 53.13 / 142.29 | 11,409 | 17,948 | 2,250 |
| after | write | observer | 1024 | 0 | 4.12 / 5.54 / 5.66 | 43,485 | 55,994 | 0 |

Under write load, both callers now return every head. Before, the writer returned `Unavailable` on 27% of calls and the observer on 28% in this paired run. N7 recorded 7% for the observer.

### Noisy neighbour

| Build | Cap | Hot records | Hot MB/s | Neighbour acks | Neighbour latency in ms |
| --- | --- | ---: | ---: | ---: | --- |
| before | 4 MiB | 39 | 80.24 | 8,274 | 4.03 / 260.70 / 1394.68 |
| before | 64 MiB | 4 | 8.17 | 314 | 89.29 / 3142.53 / 3803.33 |
| after | 4 MiB | 90 | 186.29 | 24,941 | 4.01 / 15.19 / 250.66 |
| after | 64 MiB | 77 | 159.01 | 17,374 | 4.06 / 69.06 / 376.79 |

Large hot records use exclusive channels, so they never block small neighbours on the shared connection. With the 4 MiB cap, neighbour p99 fell from 260.70 ms to 15.19 ms, and the hot stream rose from 80 to 186 MB/s against the 200 MB/s offer.

### Faults and regression guard

On the after build at 1 ms, SIGKILL of one keeper recovered 1,000 streams in 11.95 / 12.66 / 12.66 ms, with an ack gap of 43.92 / 71.33 / 71.44 ms. The partition-and-claim case took 2037.16 / 2039.30 / 2039.30 ms, still dominated by the two-second deadline on the blackholed route. Both are no slower than N7's results.

`stream-measure KEEPER scale-check RTT_US` fails when any of these conditions holds:

- one stream's batch-32 throughput is below four times its batch-1 throughput;
- 10,000 streams at batch 32 produce any transport error or new connection;
- a head call returns `Unavailable`.

`run.sh` now runs it. Of three scale checks on the after build, two passed. The first, which started right after the long before-build runs, failed: its idle observer phase got `Unavailable` 32 times. That phase recorded 960 fast-failing transport errors at 1,726 RPCs/s, so its connections failed rather than timed out. The failure did not recur in three isolated head runs or two further scale checks. The harness now records `unreachable` and `timed_out` counts so a recurrence can be attributed. The before build fails every criterion above.

## Transport regression and saturation

The prior transport kept 16 idle connections per route and left concurrent dials unbounded. A warm-route control with 1,536 `Check` calls reopened 1,152 TLS connections in 24 waves. The bounded pool reopened zero connections at both requested RTTs. It admits 64 concurrent calls per route and limits waiting reads to 16 of those slots. Extra idle channels expire after a short grace period so a burst leaves room for other clients later.

In a paired 1,000-stream, batch-1 probe with all producers admitted, the pre-fix transport opened 7,285 connections and reported 9,821 transport errors. It delivered 1,888 records/s at 940.45 ms p99. With the bounded pool the same workload opened 10 connections, reported no transport errors, and delivered 13,624 records/s at 72.62 ms p99. This probe preceded the idle-grace cleanup. The warm-route regression also passed with the cleanup enabled.

A fully simultaneous 10,000-stream, batch-1 burst still ran at 824 records/s and 23.26 s p99 with 145,363 transport errors. A separate batch-32 run with 256 producers stopped writing WAL records and still had pending calls when it was stopped. The blocked-publication regression isolates a case where a later append failure stopped a lane before it published an earlier chosen head. The original benchmark did not record enough state to attribute all of its stalls to that condition. The host also exhausted ephemeral loopback ports under concurrent test and benchmark load.

The first 100,000-stream replacement attempt reached the sweeper, which stopped on `NotFound` from one survivor. A create quorum can include the lost keeper. Replacement now rebuilds a missing survivor when the other survivor confirms the stream. A second run exposed a retry gap. When one keeper reports absence and the other is unreachable, the latter error now reaches the sweeper caller so it can retry. The final run deliberately gives each parked stream a single surviving copy.

## Delay calibration

| RTT target | One-byte echo p50 | p99 | p99.9 |
| --- | ---: | ---: | ---: |
| 0 ms | 0.05 ms | 0.08 ms | 0.14 ms |
| 1 ms | 1.61 ms | 4.23 ms | 31.32 ms |
| 2 ms | 3.04 ms | 3.26 ms | 8.82 ms |

The 1 ms profile covers all six workload families. The 2 ms profile repeats head and the commit matrix through 1,000 streams, plus batch size 1 at 10,000 streams.

## Commit

Latencies are `p50 / p99 / p99.9` in ms. Queue is the producer queue p99, also in ms. Throughput includes the queue and all acknowledgements.

| RTT target | Streams | Batch | Admitted | Records | Record ack | Batch ack | Queue p99 | Records/s |
| --- | ---: | ---: | ---: | ---: | --- | --- | ---: | ---: |
| 0 ms | 1 | 1 | 1 | 1,000 | 0.97 / 1.21 / 4.75 | 0.97 / 1.21 / 4.75 | 0.00 | 1,018 |
| 1 ms | 1 | 1 | 1 | 1,000 | 4.05 / 45.40 / 65.88 | 4.05 / 45.40 / 65.88 | 0.00 | 160 |
| 1 ms | 1 | 32 | 1 | 1,024 | 47.08 / 204.34 / 284.13 | 87.41 / 285.83 / 285.83 | 0.00 | 317 |
| 1 ms | 100 | 1 | 100 | 1,000 | 16.28 / 46.20 / 48.43 | 16.28 / 46.20 / 48.43 | 0.00 | 5,025 |
| 1 ms | 100 | 32 | 100 | 6,400 | 248.57 / 972.99 / 1059.57 | 547.06 / 1064.76 / 1075.56 | 0.00 | 4,125 |
| 1 ms | 1,000 | 1 | 256 | 2,000 | 31.92 / 45.01 / 47.76 | 31.92 / 45.01 / 47.76 | 112.51 | 7,935 |
| 1 ms | 1,000 | 32 | 256 | 64,000 | 206.27 / 520.48 / 555.15 | 375.73 / 558.30 / 565.71 | 1387.89 | 20,507 |
| 1 ms | 10,000 | 1 | 256 | 20,000 | 21.39 / 49.43 / 56.25 | 21.39 / 49.43 / 56.25 | 921.21 | 11,433 |
| 1 ms | 10,000 | 32 | 64 | 320,000 | 108.58 / 25926.59 / 28284.91 | 207.10 / 28039.12 / 30229.14 | 410449.62 | 745 |
| 2 ms | 1 | 1 | 1 | 1,000 | 6.67 / 7.21 / 7.39 | 6.67 / 7.21 / 7.39 | 0.00 | 151 |
| 2 ms | 1 | 32 | 1 | 1,024 | 58.05 / 107.41 / 113.30 | 105.17 / 113.32 / 113.32 | 0.00 | 304 |
| 2 ms | 100 | 1 | 100 | 1,000 | 8.64 / 15.55 / 16.60 | 8.64 / 15.55 / 16.60 | 0.00 | 10,668 |
| 2 ms | 100 | 32 | 100 | 6,400 | 86.82 / 190.45 / 195.68 | 159.96 / 197.45 / 199.57 | 0.00 | 18,147 |
| 2 ms | 1,000 | 1 | 256 | 2,000 | 22.59 / 23.83 / 24.30 | 22.59 / 23.83 / 24.30 | 67.96 | 11,091 |
| 2 ms | 1,000 | 32 | 256 | 64,000 | 235.73 / 1403.53 / 1442.98 | 392.32 / 1451.70 / 1460.61 | 2404.72 | 15,114 |
| 2 ms | 10,000 | 1 | 256 | 20,000 | 21.71 / 29.34 / 30.35 | 21.71 / 29.35 / 30.35 | 843.00 | 11,630 |

## Head

Head percentiles are in ms and cover successful calls. The RPC rates are per second. For writer rows, data and publication RPCs share the reported writer transport. For observer rows they use a separate transport.

| RTT target | Load | Caller | OK | Unavailable | Head | RPC starts | RPC returns | Check starts | Writer data and publication starts |
| --- | --- | --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 ms | idle | writer | 1024 | 0 | 2.10 / 3.98 / 9.71 | 37,068 | 24,712 | 37,068 | 0 |
| 1 ms | idle | observer | 1024 | 0 | 1.89 / 7.29 / 7.81 | 38,511 | 25,674 | 38,511 | 0 |
| 1 ms | write | writer | 1024 | 0 | 4.72 / 8.20 / 9.18 | 58,207 | 51,025 | 18,079 | 38,146 |
| 1 ms | write | observer | 949 | 75 | 10.41 / 28.16 / 32.49 | 22,869 | 21,277 | 22,869 | 47,947 |
| 2 ms | idle | writer | 1024 | 0 | 2.39 / 7.06 / 15.09 | 30,087 | 20,058 | 30,087 | 0 |
| 2 ms | idle | observer | 1024 | 0 | 2.43 / 9.01 / 9.77 | 28,585 | 19,057 | 28,585 | 0 |
| 2 ms | write | writer | 1024 | 0 | 5.87 / 13.56 / 13.89 | 45,116 | 40,070 | 14,252 | 30,322 |
| 2 ms | write | observer | 976 | 48 | 10.83 / 28.36 / 40.01 | 18,344 | 16,409 | 18,344 | 31,818 |

## Keeper loss and replacement

Fault times and ack gaps are in ms. The partition result includes the successor's client trying the blackholed first read route under its configured two-second RPC deadline.

| Fault | RTT target | Affected streams | Event to ack | Ack gap | Last ack |
| --- | --- | ---: | --- | --- | ---: |
| SIGKILL | 1 ms | 1,000 | 56.90 / 69.84 / 69.84 | 91.39 / 111.84 / 112.69 | 69.85 |
| AZ partition and claim | 1 ms | 1,000 | 2198.85 / 2214.11 / 2215.12 | 2233.77 / 2249.39 / 2252.78 | 2215.13 |

At 1 ms, the sweeper installed 100,000 learner copies in 108.18 s of measured installation time (924 streams/s). A post-timing pass verified every copy. The 1,000 active streams acknowledged 48,871 new records during the sweep. Stream completion from sweep start was 65787.45 / 107913.71 / 108155.88 ms (p50 / p99 / p99.9).

## Noisy neighbour

| Trial | RTT target | Cap | Hot records | Hot MB/s | Neighbour acks | Neighbour latency in ms |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 1 | 1 ms | 4 MiB | 79 | 75.10 | 8154 | 4.31 / 144.49 / 4373.78 |
| 1 | 1 ms | 64 MiB | 2 | 1.87 | 37 | 8311.52 / 8767.41 / 8767.41 |
| 2 | 1 ms | 4 MiB | 77 | 161.31 | 19216 | 3.62 / 93.93 / 182.13 |
| 2 | 1 ms | 64 MiB | 70 | 146.69 | 17173 | 3.62 / 113.15 / 289.54 |

Both trials offered 200 MB/s. On the repeat, the cap improved neighbour p99 from 113.15 ms to 93.93 ms while the hot stream completed 161 MB/s with the cap and 147 MB/s without it. The first uncapped trial produced just 37 neighbour acknowledgements and its p99 is the sample maximum. Neither trial achieved 200 MB/s across the full interval, so the comparison is an equal-offer measurement.

## D06 verdict

Keep writer-driven, per-stream quorums provisionally for latency-sensitive workloads with admission control. The 100,000-stream sweep, including the one-copy parked histories, took 1 minute 48 seconds. This clears the brief's hours-scale replacement criterion on this host. A simple remote-leader model adds one client-to-leader round trip. The calibrated extra hop is about 1.56 ms or 2.99 ms at the two settings. That amounts to 39% or 45% of the corresponding single-stream median append latency, so the hop can matter at low load.

At the saturated 10,000-stream, batch-32 operating point, the additional hop is immaterial beside 25.93 s record p99. The batch completed, but its run started over 225,000 new connections and recorded about 1.8 million transport errors and only 745 records/s. A one-group-per-cell design would win under the brief's latency criterion for that operating point. Its throughput and failover behavior still need a direct comparison. The per-stream design has no demonstrated 10,000-stream batch-32 operating budget from this run.

Addendum (node-level batching): that operating point now runs with zero transport errors at 457,401 records/s and 7.09 ms record p99 with 64 producers, and 874,353 records/s and 17.87 ms p99 with 256. The per-stream logical consensus is unchanged: batching happens at the node connection and in the keeper round. The collapse was caused by per-call connections and per-record keeper rounds, not by per-stream quorums.

The comparison uses the decision criteria stated in the N7 brief. The granularity deep dive's numerical thresholds were absent from the supplied Wave N report directory. The loopback setup measures one disk and one network stack across all processes, and the experiment models the remote leader's additional RTT. It supplies no cell-leader measurements or independent-AZ hardware results.

## F6 shared checkpoint rotation

The baseline was `8d88239`. Both release builds ran the complete `run.sh`
on the same loopback host at the 1 ms and 2 ms settings, including the
100,000-stream replacement and the scale guard. The calibrated echo
latencies were:

| RTT setting | Before echo (ms) | F6 echo (ms) |
| --- | --- | --- |
| 0 ms | 0.02 / 0.11 / 0.13 | 0.02 / 0.15 / 0.25 |
| 1 ms | 1.62 / 1.66 / 1.73 | 1.63 / 1.72 / 1.80 |
| 2 ms | 3.17 / 6.09 / 9.73 | 3.11 / 3.26 / 3.78 |

All latency triples are p50 / p99 / p99.9. The 64-channel pool check
reopened zero connections in both builds at both RTTs.

F4 measured about 3.8 s for a rotation over 10,000 dirty streams, with about
five syncs per new stream. The F6 regression counts seven syncs total for a
rotation with either one or 10,000 dirty streams, including the successor
segment and the retirement sync. The pack writer and index publication run
off the round thread. Physical WAL segments stop at 64 MiB, including while
the previous checkpoint is in progress. The gate tests stop the checkpoint
worker while an unrelated append completes for both startup and delete.

### Commit

The first three commit probes per RTT belong to the scale guard. The table
below reports the full commit matrix. The 10,000-stream batch-32 row admits
64 producers.

| RTT | Streams | Batch | Before record ack (ms) | F6 record ack (ms) | Before records/s | F6 records/s |
| --- | ---: | ---: | --- | --- | ---: | ---: |
| 1 ms | 1 | 1 | 3.75 / 4.08 / 4.16 | 4.09 / 4.55 / 5.14 | 268 | 247 |
| 1 ms | 1 | 32 | 5.96 / 6.60 / 6.61 | 6.12 / 6.73 / 6.79 | 5,228 | 5,051 |
| 1 ms | 100 | 1 | 3.90 / 5.27 / 5.38 | 4.15 / 7.27 / 7.54 | 23,888 | 22,129 |
| 1 ms | 100 | 32 | 6.38 / 8.40 / 8.63 | 10.38 / 14.46 / 14.58 | 439,800 | 240,962 |
| 1 ms | 1,000 | 1 | 4.06 / 6.19 / 6.30 | 4.17 / 12.38 / 12.68 | 58,220 | 47,741 |
| 1 ms | 1,000 | 32 | 7.55 / 14.89 / 15.77 | 7.85 / 13.31 / 14.57 | 959,620 | 934,582 |
| 1 ms | 10,000 | 1 | 3.99 / 5.85 / 6.94 | 4.43 / 5.72 / 7.14 | 62,658 | 57,023 |
| 1 ms | 10,000 | 32 | 4.40 / 12.19 / 16.11 | 4.85 / 7.79 / 10.38 | 419,414 | 401,319 |
| 2 ms | 1 | 1 | 6.40 / 34.06 / 139.95 | 6.98 / 7.57 / 9.30 | 97 | 145 |
| 2 ms | 1 | 32 | 6.62 / 12.72 / 12.73 | 7.06 / 10.73 / 11.06 | 3,939 | 3,708 |
| 2 ms | 100 | 1 | 5.76 / 7.74 / 7.89 | 5.64 / 8.13 / 8.88 | 15,887 | 16,297 |
| 2 ms | 100 | 32 | 7.24 / 9.74 / 9.91 | 6.63 / 8.81 / 9.82 | 333,178 | 336,968 |
| 2 ms | 1,000 | 1 | 5.91 / 8.22 / 9.80 | 6.18 / 8.06 / 9.35 | 39,940 | 39,157 |
| 2 ms | 1,000 | 32 | 9.82 / 15.88 / 16.98 | 15.85 / 27.98 / 29.37 | 751,051 | 465,622 |
| 2 ms | 10,000 | 1 | 5.86 / 8.38 / 11.94 | 6.02 / 14.52 / 16.50 | 42,784 | 38,738 |
| 2 ms | 10,000 | 32 | 6.44 / 12.14 / 14.11 | 6.35 / 9.87 / 11.43 | 298,535 | 304,043 |

The measured single-record median still includes two keeper round trips.
Publishing in the first request would allow one keeper to show an unchosen
record that a takeover can discard. Acknowledging before publication would
let a fresh read index observe the chosen tail without quorum head coverage.
The writer keeps the existing publication rule and preserves
`Unavailable` after uncertain publication.

### Head and scale guard

The full head case and the head phase of `scale-check` each ran 4,096
calls per RTT and build. They recorded zero `Unavailable`, zero
`Unreachable` and zero `TimedOut` in both observer and writer RPC counters.
The table shows the full head case.

| RTT | Load | Caller | Before head (ms) | F6 head (ms) |
| --- | --- | --- | --- | --- |
| 1 ms | Idle | Writer | 1.77 / 2.10 / 2.11 | 1.73 / 1.89 / 1.90 |
| 1 ms | Idle | Observer | 1.33 / 3.89 / 3.89 | 1.75 / 3.86 / 3.87 |
| 1 ms | Write | Writer | 3.47 / 6.29 / 6.64 | 4.01 / 4.71 / 4.81 |
| 1 ms | Write | Observer | 4.14 / 5.67 / 5.73 | 4.19 / 5.72 / 5.77 |
| 2 ms | Idle | Writer | 3.10 / 3.66 / 3.68 | 3.33 / 3.61 / 3.64 |
| 2 ms | Idle | Observer | 3.22 / 6.91 / 6.92 | 3.32 / 7.01 / 7.03 |
| 2 ms | Write | Writer | 5.76 / 6.61 / 6.72 | 5.98 / 7.56 / 7.63 |
| 2 ms | Write | Observer | 6.63 / 7.94 / 8.11 | 6.40 / 8.23 / 8.68 |

The standalone F6 scale guard also passed at both settings. Its 256-producer
batch-32 case and the corresponding in-harness cases had zero transport
errors and reconnects. Each standalone head phase had zero `Unavailable`,
`Unreachable` or `TimedOut`.

| RTT | Before records/s | F6 records/s | F6 standalone records/s | F6 standalone batch-32 ratio |
| --- | --- | --- | --- | --- |
| 1 ms | 868,973 | 825,253 | 667,937 | 23.2× |
| 2 ms | 558,874 | 790,638 | 699,994 | 21.7× |

### Loss, replacement and noisy neighbour

The replacement verifier checked all 100,000 learner copies after timing
at each setting. The partition case still waits about two seconds for the
blackholed route.

| RTT | Case | Before elapsed (s) | F6 elapsed (s) | Before stream p99 (ms) | F6 stream p99 (ms) |
| --- | --- | --- | --- | --- | --- |
| 1 ms | kill | 0.012 | 0.013 | 11.78 | 12.41 |
| 1 ms | partition | 2.039 | 2.035 | 2038.05 | 2034.71 |
| 1 ms | replace | 44.906 | 38.104 | 44529.53 | 37771.18 |
| 2 ms | kill | 0.019 | 0.017 | 18.88 | 16.57 |
| 2 ms | partition | 2.040 | 2.037 | 2039.56 | 2036.97 |
| 2 ms | replace | 66.398 | 64.362 | 65766.52 | 63845.37 |

| RTT | Round cap | Before hot MB/s | F6 hot MB/s | Before neighbour p99 (ms) | F6 neighbour p99 (ms) |
| --- | --- | --- | --- | --- | --- |
| 1 ms | 4 MiB | 22.6 | 192.4 | 70.50 | 35.06 |
| 1 ms | 64 MiB | 110.5 | 83.6 | 419.06 | 60.96 |
| 2 ms | 4 MiB | 163.3 | 192.2 | 79.40 | 48.40 |
| 2 ms | 64 MiB | 48.2 | 61.0 | 48.78 | 689.57 |

The 2 ms noisy-neighbour repeat moved in both directions:

| Round cap | Before hot MB/s | F6 hot MB/s | Before neighbour p99 (ms) | F6 neighbour p99 (ms) |
| --- | --- | --- | --- | --- |
| 4 MiB | 138.7 | 58.9 | 47.17 | 95.97 |
| 64 MiB | 177.7 | 186.3 | 92.97 | 52.46 |

The first pass's 689.57 ms p99 at the 64 MiB cap did not recur. These
loopback runs share a disk and network stack. The run-to-run differences
do not isolate filesystem contention from host scheduling.
