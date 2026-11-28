# Writer-driven journal vs. consensus keeper: head-to-head on separate hosts

This file reports a benchmark of Logkeeper's two `journal_contract::Journal`
implementations on separate Macs:

- **writer-driven**: the client `Writer` and proposer over plain keepers
  (`logkeeper keeper --config` with a stream `Config`). The client reaches them
  the way RTDB does, with `TcpTransport::discover` on `logkeeper+tls://a,b,c`.
- **consensus**: `ConsensusJournal` over consensus keepers, with one OpenRaft
  group per stream, a replicated catalog and enforced catalog leases.

One harness drives both: `verification/measure/head_to_head.rs`, built as the
`head-to-head` example. It uses the same `Journal` calls wherever the contract
allows. Each case ran once. The network is home Wi-Fi with heavy tail jitter,
and other jobs ran on the hosts during the runs. Read the tails as specific to
this setup.

## Hosts and topology

| Role | Host (Rex label) | Hardware | macOS | Network | Notes |
| --- | --- | --- | --- | --- | --- |
| keeper `a`, zone-a; spare, zone-a | `mac-mini-1-rex` | Mac mini Mac18,5, Apple M6, 12 cores, 24 GiB | 27.0 | 1 GbE (192.168.1.25) | Ran four unrelated Python processes at about 90% CPU each during the runs |
| keeper `b`, zone-b | `sachas-macbook-pro-rex` (the MacBook Pro M4; `macbook-pro-m4-rex` is a stale label) | MacBook Pro Mac16,5, M4 Max, 14 cores, 36 GiB | 26.3 | Wi-Fi (192.168.1.14) | AC power |
| keeper `c`, zone-c, **and the client** (main run) | `macbook-pro-m1-rex` | MacBook Pro 18,1, M1 Pro, 10 cores, 16 GiB | 15.5 | Wi-Fi (192.168.1.18) | Also the build host |
| keeper `c`, zone-c (first run only) | `sachas-macbook-air-rex` (hostname `mac-1`) | MacBook Air Mac17,4, Apple M5, 10 cores, 16 GiB | 26.6 | Wi-Fi (192.168.1.19) | On battery. It dropped off the network mid-run, so the main run does not use it |

**Topology change.** The brief named `macbook-pro-m4-rex` and `macbookair-rex`.
Neither name resolves. The M4 answers as `sachas-macbook-pro-rex`. The Air
answered as `sachas-macbook-air-rex` for the first run, then went offline
repeatedly. The main run (run 3) therefore puts keeper `c` on the M1, on the
same host as the client. Both backends use that same topology:

- The consensus client's `domain` is `zone-c`, as RTDB sets it to the zone of
  its co-located keeper. Each stream's leader therefore moves to keeper `c` at
  seal, on the client's host.
- The writer-driven client talks to all three keepers. One of them is local.

Run 1 used keepers mini / M4 / Air, with the client alone on the M1 and the
consensus client in `zone-a`, so leaders were on the wired mini. Its complete
cases are kept below for comparison.

Every keeper used its own APFS internal SSD. Keeper media lived under
`~/code/wd-bench/run` and were wiped after every case.

### RTT

Each row is a TCP one-byte echo between the harness agents, 1,000 samples
5 ms apart. The client is the M1.

Run 3, keepers mini (.25), M4 (.14) and M1 (.18); the client is on the M1:

| From | To | Echo RTT p50 / p99 / p99.9 ms |
| --- | --- | --- |
| client | 192.168.1.25 | 4.2 / 93.0 / 95.2 |
| client | 192.168.1.14 | 9.1 / 100.4 / 358.4 |
| client | 192.168.1.18 | 0.1 / 0.2 / 0.5 |
| 192.168.1.25 | 192.168.1.14 | 5.5 / 92.1 / 94.0 |
| 192.168.1.25 | 192.168.1.18 | 4.7 / 91.5 / 94.6 |
| 192.168.1.14 | 192.168.1.25 | 4.5 / 92.2 / 418.3 |
| 192.168.1.14 | 192.168.1.18 | 8.7 / 98.4 / 266.0 |
| 192.168.1.18 | 192.168.1.25 | 4.2 / 93.2 / 94.8 |
| 192.168.1.18 | 192.168.1.14 | 8.9 / 97.2 / 107.9 |

Run 1, keepers mini (.25), M4 (.14) and Air (.19); the client is on the M1:

| From | To | Echo RTT p50 / p99 / p99.9 ms |
| --- | --- | --- |
| client | 192.168.1.25 | 4.8 / 96.0 / 254.1 |
| client | 192.168.1.14 | 10.7 / 113.0 / 426.4 |
| client | 192.168.1.19 | 10.2 / 135.9 / 153.7 |
| 192.168.1.25 | 192.168.1.14 | 6.3 / 160.0 / 261.8 |
| 192.168.1.25 | 192.168.1.19 | 6.1 / 139.0 / 209.9 |
| 192.168.1.14 | 192.168.1.25 | 5.5 / 92.3 / 95.9 |
| 192.168.1.14 | 192.168.1.19 | 11.0 / 103.2 / 160.4 |
| 192.168.1.19 | 192.168.1.25 | 5.2 / 120.3 / 346.8 |
| 192.168.1.19 | 192.168.1.14 | 11.3 / 141.4 / 365.8 |

The medians are 4–6 ms between the wired mini and a laptop, and 9–11 ms
between two Wi-Fi laptops. Every Wi-Fi path has p99 ≈ 90–100 ms. That tail
is periodic Wi-Fi stalls, and it bounds every p99 below.

## Commits and binaries

- Base: `origin/writer-driven-endgame` = `origin/main` = `d04d04c8`. It compiles;
  the library prints only five existing warnings.
- Harness: branch `writer-driven/bench`. Run 1 used `1b14f48` (the binary was built at `633c76d`; only the script changed after it). The run 2 kill
  and repair reruns used `60810c3`. Run 3 used `dc1710b`. Changes between
  runs touched only the harness: the kill case counts unacknowledged streams
  instead of aborting, the repair wait is bounded, and the client zone and
  settle time became settings.
- `logkeeper` release binary sha256 `de66c4ed…0456`, identical on every keeper.
  It was built on the M1 with Rust 1.94.1 through `guarded-cargo.py` and
  `cargo build --release --features consensus-testing --bin logkeeper --example head-to-head`.

## Method

`head-to-head agent` runs on every keeper host. It writes the files the
controller sends below its root, runs `logkeeper keeper initialize`, spawns
`logkeeper keeper --config`, SIGKILLs it, reports `ps` RSS and CPU time and
disk use, and echoes bytes for RTT probes. `head-to-head run` on the client
does the rest. For every case it generates a new CA and new keeper
identities, provisions fresh media, starts the keepers, runs one workload, and
prints one JSON line.

### Settings, identical unless noted

| Setting | Writer-driven | Consensus |
| --- | --- | --- |
| Record | 256 B | 256 B |
| TLS | mTLS 1.3, one rcgen CA, URI SAN identities | same |
| `sync_mode` | `full` (`F_FULLFSYNC`) | `full` (`F_FULLFSYNC`) |
| Keepers | 3, one per host and zone | 3 voters, one per host and zone, plus a spare in zone-a only in the repair case |
| Client handle | `Writer` from `TcpTransport::discover` (5 s deadline) | `ConsensusJournal::new`, `deadline_ms` 10,000, `placement` = the 3 keepers, `domain` = client zone |
| Catalog | none | replicated: `catalog_voters` = the 3 keepers, `catalog` = keeper `a` |
| Leases | none | cluster level finalized to `CLUSTER_VERSION_CURRENT` at start, so leases are enforced; default `lease_millis` 30,000, drift margin 3,000 |
| Other keeper settings | limits as in `cluster.rs`: 8 GiB quota, 4 MiB round cap, 64 requests per round | `max_streams` 4,096 (the default 128 is below 1,000 streams), `async_append` true, defaults otherwise |
| Batch of 1 | `Journal::append` | `Journal::append` |
| Batch of 32 | 32 concurrent `Journal::append` calls in LSN order, which the writer coalesces (RTDB's `StreamJournal::append_batch`) | one `ConsensusJournal::append_batch` (RTDB's `ConsensusJournalBatch`) |
| Admission | at most 256 streams with a batch in flight | same |
| Retry | the harness retries `Unavailable` for up to 60 s per call | same; `ConsensusJournal` also retries internally within its deadline |

### Cases

- **commit**: S streams × batch B. At least 4,000 records and at least two
  passes, starting 500 ms after every stream is created and sealed. "Record ack"
  is per record. For a consensus batch every record shares the batch's
  latency. Keeper CPU is the `ps` CPU-time delta summed over the three keepers
  during the measured interval. RSS and disk are read after it.
- **head**: 32 streams, at least 2,000 `head` calls, 64 in parallel. Callers are
  the writer principal and a separate observer principal (consensus
  `readers`). "Under load" means every stream has a closed-loop appender
  running.
- **kill**: 1,000 streams each acknowledge record 1. The harness SIGKILLs one
  keeper through its agent, then appends record 2 on every stream at once.
  "Event to ack" runs from just before the kill request is sent. A stream not
  acknowledged within 300 s is counted (run 1 aborted at 60 s). "Led by victim"
  is the client's cached leader per stream.
- **takeover**: 1,000 streams, each with 32 records from writer W1 (writer
  principal). W1 and its connections are dropped. Then a new handle under the
  successor principal is built, and for every stream at once it runs `seal`
  at epoch 2, reads every record, and appends record 33 at epoch 2.
- **repair**: N streams with one record each, idle. Keeper `a` is SIGKILLed for
  good. A spare keeper in zone-a, on the mini, is already running before the
  loss on both backends.
  - Writer-driven: the harness runs the existing sweeper (`sweep_idle`, 64
    streams in parallel) right after the kill, with survivors `b` and `c` and
    the spare as learner. A stream counts when its sweep returns.
  - Consensus: the streams first park (`park_after_secs` 60). Repair is
    automatic with `repair_after_secs` 10. A stream counts when the spare
    reports a healthy replica and the stream's configuration is
    {spare, b, c}. The harness polls once per second.

## Results: run 3 (keepers mini / M4 / M1; client on the M1, zone-c)

All latencies are in ms, given as p50 / p99 / p99.9 unless marked otherwise.

### a. Commit

| Backend | Streams | Batch | Records | Record ack ms | Batch ack ms | Records/s | Keeper CPU s | Keeper CPU ms/record | Client CPU s | Max keeper RSS MiB | Keeper disk MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| writer | 1 | 1 | 4000 | 17.4 / 107.6 / 241.3 | 17.4 / 107.6 / 241.3 | 45 | 3.6 | 0.91 | 1.6 | 13 | 6.0 |
| consensus | 1 | 1 | 4000 | 17.9 / 114.1 / 235.9 | 17.9 / 114.1 / 235.9 | 44 | 11.1 | 2.77 | 0.4 | 52 | 7.1 |
| writer | 1 | 32 | 4000 | 20.4 / 116.0 / 116.4 | 25.8 / 116.0 / 116.4 | 1,090 | 0.2 | 0.05 | 0.1 | 13 | 3.1 |
| consensus | 1 | 32 | 4000 | 18.1 / 125.9 / 131.0 | 18.1 / 125.9 / 131.0 | 1,405 | 0.3 | 0.08 | 0.0 | 48 | 6.4 |
| writer | 32 | 1 | 4000 | 22.5 / 111.6 / 128.7 | 22.5 / 111.6 / 128.7 | 1,128 | 0.4 | 0.11 | 0.6 | 15 | 6.1 |
| consensus | 32 | 1 | 4000 | 24.3 / 129.7 / 131.4 | 24.3 / 129.7 / 131.4 | 1,050 | 2.6 | 0.65 | 0.2 | 78 | 6.3 |
| writer | 32 | 32 | 4096 | 36.6 / 121.1 / 125.4 | 38.5 / 121.1 / 125.4 | 15,356 | 0.0 | 0.01 | 0.1 | 15 | 3.1 |
| consensus | 32 | 32 | 4096 | 35.7 / 45.6 / 49.6 | 35.7 / 45.6 / 49.6 | 26,341 | 0.1 | 0.03 | 0.0 | 62 | 6.1 |
| writer | 1000 | 1 | 4000 | 29.6 / 128.1 / 128.6 | 29.6 / 128.1 / 128.6 | 6,968 | 0.2 | 0.05 | 0.6 | 19 | 6.0 |
| consensus | 1000 | 1 | 4000 | 103.6 / 2258.1 / 3244.6 | 103.6 / 2258.1 / 3244.6 | 665 | 12.7 | 3.16 | 4.0 | 474 | 14.1 |
| writer | 1000 | 32 | 64000 | 89.6 / 213.0 / 225.0 | 91.1 / 214.5 / 226.6 | 69,063 | 0.2 | 0.00 | 1.1 | 43 | 51.3 |
| consensus | 1000 | 32 | 64000 | 998.3 / 19270.2 / 26434.7 | 998.3 / 19270.2 / 26434.7 | 1,999 | 52.0 | 0.81 | 15.0 | 560 | 62.6 |

- Keeper CPU is the `ps` CPU-time delta, which has 10 ms resolution and is
  sampled once before and once after. Short runs, such as writer-driven runs
  under a second, therefore have coarse CPU figures. Client CPU is `getrusage`
  of the whole harness process.
- At 1,000 streams the consensus run's interval is 6.0 s (batch 1) and 32.0 s
  (batch 32). The writer-driven run's is 0.6 s and 0.9 s.
- Consensus batching through 32 concurrent `Journal::append` calls (the
  writer-driven native path) failed at once with `Conflict { head: Lsn(0) }`
  (run 1: `Conflict { head: Lsn(2) }`). `ConsensusJournal::append` does not
  accept pipelined appends that arrive out of order, so consensus batches use
  `append_batch`.

### b. Head

| Backend | Load | Caller | OK | Latency ms | Unavailable |
| --- | --- | --- | --- | --- | --- |
| writer | idle | writer | 2016 | 6.2 / 92.5 / 92.9 | 0 |
| writer | idle | observer | 2016 | 6.3 / 91.5 / 92.6 | 0 |
| writer | write | writer | 2016 | 22.8 / 110.4 / 115.2 | 0 |
| writer | write | observer | 2016 | 27.0 / 115.8 / 120.7 | 0 |
| writer | write | background append | 4823 | 22.9 / 109.6 / 116.4 |  |
| consensus | idle | writer | 2016 | 8.4 / 98.5 / 99.7 | 0 |
| consensus | idle | observer | 2016 | 7.9 / 98.2 / 105.2 | 0 |
| consensus | write | writer | 2016 | 9.6 / 185.4 / 1709.7 | 0 |
| consensus | write | observer | 2016 | 11.2 / 110.6 / 1056.5 | 0 |
| consensus | write | background append | 5312 | 25.7 / 136.8 / 191.3 |  |

### c. Keeper SIGKILL, 1,000 streams

`c` is the keeper on the client's host and the consensus client's preferred
leader. `a` is the wired mini. Every stream was acknowledged within the 300 s
limit.

| Backend | Victim | Streams | Led by victim | Acked | Not acked | Event to ack ms (p50 / p99 / p99.9) | Max ms | Ack gap ms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| writer | c | 1000 | None | 1000 | 0 | 89.3 / 93.1 / 93.1 | 93 | 889.8 / 1065.9 / 1074.5 |
| consensus | c | 1000 | 590 | 1000 | 0 | 2976.0 / 9736.2 / 11196.5 | 11734 | 3865.3 / 10811.7 / 12219.2 |
| writer | a | 1000 | None | 1000 | 0 | 106.5 / 118.2 / 118.2 | 118 | 806.2 / 1073.7 / 1074.9 |
| consensus | a | 1000 | 201 | 1000 | 0 | 4346.8 / 31088.0 / 33324.5 | 34559 | 5348.7 / 32075.5 / 34275.1 |

The writer-driven journal has no leaders, so "led by victim" does not apply.
After seal with `domain` zone-c, the client saw 590 of the 1,000 consensus
streams led by `c`, not all of them. Losing `a`, which led 201 streams by the
client's cache, delayed all 1,000 streams: p50 4.3 s.

### d. Writer takeover, 1,000 streams × 32 records

| Backend | Streams | New writer ms | Seal ms | Seal + catch-up ms | Seal + catch-up + first append ms | From takeover start ms | Last stream s |
| --- | --- | --- | --- | --- | --- | --- | --- |
| writer | 1000 | 65.6 | 208.0 / 224.0 / 224.5 | 229.6 / 260.9 / 262.5 | 304.0 / 324.0 / 327.4 | 383.6 / 408.1 / 408.9 | 0.41 |
| consensus | 1000 | 0.4 | 3521.6 / 7814.4 / 8327.6 | 4078.0 / 7862.4 / 8373.2 | 4644.4 / 8230.4 / 8398.3 | 4688.0 / 8270.0 / 8418.0 | 8.59 |

- **Consensus waits included.** Writer takeover on consensus is a raft-committed
  seal at epoch 2. No catalog lease or recovery wait sits on that path: leases
  gate only campaigning and serving, and the lease wait applies only to an
  operator `recover-stream` after a two-voter loss, which this benchmark does
  not run.
- **Leader failover** is the kill case above, with victim `c`. It includes
  OpenRaft elections (election timeout 450–900 ms, heartbeat 100 ms, set in
  `keeper.rs`) and client rediscovery. No lease wait is in it either.
- "New writer" is handle construction: the writer-driven `discover` makes three
  TLS connections, while `ConsensusJournal::new` is lazy, so its connection
  cost lands in the first seal.

### e. Idle-stream repair after permanent loss of keeper `a`

| Backend | Streams | Repaired | Detection wait s | Completion s (p50 / p99 / max) | Minus detection wait s (p50 / max) |
| --- | --- | --- | --- | --- | --- |
| writer | 100 | 100 | 0 | 0.3 / 0.4 / 0.4 | same |
| consensus | 100 | 100 | 10 | 416.3 / 806.4 / 806.4 | 406.3 / 796.4 |
| writer | 1000 | 1000 | 0 | 1.3 / 2.7 / 2.7 | same |

- **Writer-driven:** the harness calls the sweeper right after the kill, so
  detection costs nothing. 64 streams sweep in parallel. The spare learner
  runs before the loss.
- **Consensus:** detection is automatic. 100 streams parked 68 s after setup.
  The kill came after that, and the clock starts at the kill. All 100 streams
  reached {spare, b, c} after 806 s. Contributing waits:
  - `repair_after_secs` 10, set low on purpose (default 600). The writer-driven
    side has no equivalent setting.
  - Fixed constants that are not configurable: `REPAIR_INTERVAL` 30 s,
    `PING_INTERVAL` 2 s, `WAKES_PER_SWEEP` 8, `MAX_REPAIRS` 4 per leader.
  - In the keeper logs, the M4 (`b`) leader logged 32 `voter repair did not
    complete … outcome=refused` and repaired 1 stream. The M1 (`c`) leader
    repaired the rest.
- The first column counts from the kill. The second subtracts the 10 s
  detection wait.

## Run 1 (keepers mini / M4 / Air; client alone on the M1; consensus client zone-a)

These are kept for comparison. Leaders sat on the wired mini (`a`).

| Backend | Streams | Batch | Records | Record ack ms | Batch ack ms | Records/s | Keeper CPU s | Keeper CPU ms/record | Client CPU s | Max keeper RSS MiB | Keeper disk MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| writer | 1 | 1 | 4000 | 30.1 / 131.3 / 373.3 | 30.1 / 131.3 / 373.3 | 25 | 5.8 | 1.44 | 2.4 | 14 | 6.0 |
| consensus | 1 | 1 | 4000 | 19.3 / 109.9 / 280.5 | 19.3 / 109.9 / 280.5 | 41 | 12.1 | 3.02 | 0.4 | 49 | 7.1 |
| writer | 1 | 32 | 4000 | 33.3 / 133.8 / 135.4 | 37.6 / 134.0 / 135.4 | 712 | 0.2 | 0.06 | 0.1 | 14 | 6.0 |
| consensus | 1 | 32 | 4000 | 19.8 / 100.9 / 106.2 | 19.8 / 100.9 / 106.2 | 1,323 | 0.4 | 0.10 | 0.0 | 48 | 6.9 |
| writer | 32 | 1 | 4000 | 36.4 / 128.8 / 133.2 | 36.4 / 128.8 / 133.2 | 717 | 0.5 | 0.12 | 0.5 | 15 | 6.0 |
| consensus | 32 | 1 | 4000 | 27.2 / 116.9 / 142.5 | 27.2 / 116.9 / 142.5 | 924 | 3.2 | 0.79 | 0.3 | 75 | 6.7 |
| writer | 32 | 32 | 4096 | 66.5 / 155.8 / 158.2 | 69.4 / 156.0 / 158.2 | 10,815 | 0.1 | 0.01 | 0.1 | 14 | 2.6 |
| consensus | 32 | 32 | 4096 | 29.6 / 189.4 / 200.3 | 29.6 / 189.4 / 200.3 | 14,697 | 0.1 | 0.03 | 0.0 | 66 | 4.5 |
| writer | 1000 | 1 | 4000 | 50.0 / 163.6 / 165.1 | 50.0 / 163.6 / 165.1 | 4,028 | 0.2 | 0.04 | 0.6 | 19 | 6.1 |
| consensus | 1000 | 1 | 4000 | 1514.3 / 14932.4 / 20819.3 | 1514.3 / 14932.4 / 20819.3 | 79 | 75.1 | 18.77 | 12.3 | 587 | 21.0 |
| writer | 1000 | 32 | 64000 | 142.3 / 322.4 / 372.6 | 152.8 / 345.1 / 372.8 | 46,193 | 0.3 | 0.00 | 0.9 | 42 | 34.9 |
| consensus | 1000 | 32 | 64000 | 1653.6 / 18189.9 / 26315.8 | 1653.6 / 18189.9 / 26315.8 | 2,168 | 30.2 | 0.47 | 8.9 | 601 | 51.1 |

| Backend | Load | Caller | OK | Latency ms | Unavailable |
| --- | --- | --- | --- | --- | --- |
| writer | idle | writer | 2016 | 13.5 / 112.2 / 119.2 | 0 |
| writer | idle | observer | 2016 | 12.8 / 99.8 / 101.7 | 0 |
| writer | write | writer | 2016 | 36.7 / 124.1 / 131.9 | 0 |
| writer | write | observer | 2016 | 45.2 / 433.1 / 434.9 | 0 |
| writer | write | background append | 5892 | 36.8 / 127.7 / 132.6 |  |
| consensus | idle | writer | 2016 | 13.7 / 100.7 / 213.1 | 0 |
| consensus | idle | observer | 2016 | 13.8 / 103.1 / 372.7 | 0 |
| consensus | write | writer | 2014 | 16.2 / 3111.9 / 6357.3 | 2 |
| consensus | write | observer | 2016 | 16.7 / 114.0 / 1829.9 | 0 |
| consensus | write | background append | 10227 | 32.8 / 273.0 / 2472.2 |  |

| Backend | Victim | Streams | Led by victim | Acked | Not acked | Event to ack ms (p50 / p99 / p99.9) | Max ms | Ack gap ms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| writer | a | 1000 | None | 1000 | 0 | 601.3 / 602.0 / 602.0 | 602 | 1600.8 / 1927.7 / 1927.9 |

| Backend | Streams | New writer ms | Seal ms | Seal + catch-up ms | Seal + catch-up + first append ms | From takeover start ms | Last stream s |
| --- | --- | --- | --- | --- | --- | --- | --- |
| writer | 1000 | 117.2 | 327.0 / 336.5 / 336.7 | 812.3 / 816.9 / 817.5 | 866.7 / 888.7 / 889.0 | 988.6 / 1009.5 / 1009.5 | 1.01 |
| consensus | 1000 | 0.2 | 26195.1 / 34878.7 / 35964.9 | 26702.8 / 34909.3 / 35993.4 | 27288.3 / 35323.0 / 36047.1 | 27300.4 / 35356.7 / 36091.7 | 36.12 |

| Backend | Streams | Repaired | Detection wait s | Completion s (p50 / p99 / max) | Minus detection wait s (p50 / max) |
| --- | --- | --- | --- | --- | --- |
| writer | 100 | 100 | 0 | 0.5 / 0.6 / 0.6 | same |
| writer | 1000 | 1000 | 0 | 2.6 / 6.8 / 6.8 | same |

Run 1 consensus cases without a row:

- **Kill `a` (the leader of all 1,000 streams) and kill `b`.** Both aborted
  because at least one stream did not acknowledge within the harness's 60 s
  retry limit (`Elapsed`). The harness then still aborted on the first such
  stream. The kill case now counts streams instead of aborting. A run 2 rerun
  (`60810c3`) was lost when the Air dropped off the network (`Operation timed
  out` to its agent). Its writer-driven kill row was event to ack
  372.0 / 402.6 / 402.6 ms, all 1,000 acknowledged.
- **Repair, 100 streams.** No harness row. The keeper logs were saved before
  the wipe. Keeper `a` was killed at 10:04:33 UTC, and 99 streams were repaired
  by 10:15:33. Stream `0x15` kept failing with `voter repair did not complete …
  outcome="Broken pipe (os error 32)"` until the run was stopped at about
  10:22. A Rex session deletion on the mini killed the agent mid-case. The
  spare keeper kept running, since it was not in the session's foreground
  group, and still logged at 10:21:53, so the failures were not the spare
  exiting.

## Fairness notes: what differs between the two backends

1. **Batch path.** Batch 32 is coalesced concurrent `append` calls on the
   writer-driven journal and one `append_batch` on consensus. These are the
   paths RTDB uses. Consensus cannot run the writer-driven path (see a.).
2. **Consensus-only configuration.** `max_streams` is 4,096 (the default 128
   would refuse 1,000 open streams). The catalog is replicated on the same
   three keepers. The cluster level is finalized, so leases are enforced.
   `domain` is the client's zone. None of these settings exist for the
   writer-driven journal.
3. **Repair.** Detection is free for the writer-driven journal because the
   harness invokes the sweeper. Consensus pays `repair_after_secs` = 10 plus
   fixed 30 s repair passes. Consensus streams were parked first
   (`park_after_secs` 60); writer-driven streams were only idle, since that
   journal has no parking. The spare ran before the loss on both backends.
4. **Client placement.** In run 3 one keeper shares the client's host. The
   writer-driven client counts that local keeper toward its quorum. The
   consensus client prefers a leader on it. Neither path crosses Wi-Fi to the
   local keeper.
5. **Writer principal.** Consensus needs `administrators` to create streams, so
   the writer and successor principals have it. Writer-driven keepers list them
   in `clients` and `writers`.
6. **Keeper runtime.** Neither backend sets `TOKIO_WORKER_THREADS`, unlike the
   older `cluster.rs`, which set 2.

## What was not measured, and why

- **Repeat runs and confidence intervals.** Each case ran once, apart from the
  partial run 1. Host loads from other jobs varied: the mini ran unrelated
  Python processes, and the Air showed load averages near 45.
- **Consensus repair at 1,000 parked streams.** At the measured rate of 100
  streams in 806 s, it would take over two hours.
- **Disk use per record.** Keeper disk is the allocated size of each data
  directory after the case. It includes preallocation and is not normalized.
- **Process kills of the client and real network partitions.** Takeover drops
  the old writer in-process, which closes its connections cleanly.
- **The Air in run 3.** It went offline repeatedly (Tailscale "offline, last
  seen 1m ago"; 33% ping loss).

## Reproduce

On each keeper host, with the release `logkeeper` and `head-to-head` in
`~/code/wd-bench/bin`:

```sh
head-to-head agent --listen LAN_IP:7400 --root ~/code/wd-bench/run \
    --binary ~/code/wd-bench/bin/logkeeper --token TOKEN
```

On the client:

```sh
verification/measure/head_to_head.sh ~/code/wd-bench/bin/head-to-head TOKEN \
    192.168.1.25,192.168.1.14,192.168.1.18 results/run3.jsonl zone-c 2
python3 -I verification/measure/head_to_head_tables.py results/run3.jsonl
```

The raw JSON lines are in `verification/measure/head-to-head/`.

