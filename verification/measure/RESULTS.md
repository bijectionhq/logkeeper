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

Run a single case with `stream-measure KEEPER CASE RTT_US`. `commit` accepts stream count, batch size, batches per stream, and the producer admission limit. `head`, `kill`, `partition`, `replace`, and `hot` accept an optional stream count. `pool-check` fails if a warmed 64-channel route reconnects during 24 more waves of 64 concurrent `Check` calls.

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

The comparison uses the decision criteria stated in the N7 brief. The granularity deep dive's numerical thresholds were absent from the supplied Wave N report directory. The loopback setup measures one disk and one network stack across all processes, and the experiment models the remote leader's additional RTT. It supplies no cell-leader measurements or independent-AZ hardware results.
