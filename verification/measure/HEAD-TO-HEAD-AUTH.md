# Writer-driven journal with signed history: head-to-head rerun

2026-11-28. This reruns part of `HEAD-TO-HEAD.md` (run 3) with the writer-driven
journal's authenticated history switched on (`verification/writer-driven-authenticated.md`).
It compares three things:

- **writer, signed**: writer-driven keepers with an `authenticated` config
  section. Every keeper keeps the per-stream leaf ledger and signs heads, and the
  `Writer` mounts the key set through `Writer::with_authentication`.
- **writer, unsigned**: the same binaries and hosts in the same session, without
  the config section or the key set.
- **consensus**: `ConsensusJournal`, run only for the commit cases 32×32 and 1000×32.

Every writer-driven case ran 3 times. The signed and unsigned variants alternated
case by case, and the order flipped in each repeat. Each cell gives the
**median of the repeats, then [min–max]**. The network is home Wi-Fi with
periodic ~90 ms stalls, and other jobs ran on the hosts (see "Hosts"). Each
interval is short: a 32×32 commit finishes in 0.17–0.28 s. So differences
smaller than the repeat spread are noise.

## Build and harness

- Branch `writer-driven/bench-auth`: `writer-driven/authenticated` (`5326397d`)
  with `writer-driven/bench` (`f3a0df6f`) merged in (`21577af4`), plus the harness
  changes in `c3bc1f69`. The binaries were built from `c3bc1f69`.
- The build ran on the M4 (`sachas-macbook-pro-rex`) with
  `guarded-cargo.py logkeeper build --release --features consensus-testing --bin logkeeper --example head-to-head`,
  Rust 1.94.1, shared target `~/code/codesign-agents/logkeeper-target`. It compiled
  first time, with only the library's five existing warnings.
- The binaries were copied over the LAN to the M1 and the mini, with matching hashes:
  `logkeeper` sha256 `a219b887…7591`, `head-to-head` sha256 `baaa0de3…7564`.
  Nothing was built on the mini.
- New harness options (`verification/measure/head_to_head.rs`):
  - `--authenticated 1` (writer backend only). Each case generates a fresh Ed25519
    history key per keeper with `ring`, spare included. It also generates a
    `KeeperKeys` set with a fresh `journal` UUID that installs all of them. The
    agent writes each key as `auth/history.pk8` with mode 0600, and the key set as
    `auth/keeper-keys.json`. Each keeper config gets
    `"authenticated": {"signer_pkcs8_file", "keys_file"}`. Every client `Writer`
    gets `.with_authentication(keys)`.
  - commit: after the measured interval, the harness certifies every stream's
    final head (`authenticated_head(stream, Some(size))`). This shows that every
    committed leaf was ingested. It is not part of the commit figures.
  - head: in a signed run, two more callers ("writer signed", "observer signed")
    time `authenticated_head(stream, None)`. That is a linearizable head read, two
    keeper signatures over the Merkle root, and client-side verification.
  - repair: with `--repair-trim 1`, each stream gets 2 records and is trimmed
    through 1 before the loss. The spare then receives only the retained record,
    reports `Missing`, and `seed_authenticated` must copy the trimmed leaf with a
    head signed by `b` and `c`. In a signed run, right after each stream's
    `sweep_idle` returns, the repairer binds the moved ensemble {spare, b, c} and
    calls `seed_authenticated`, as `repair::seed_repaired` does. Then it certifies
    all 100 streams, SIGKILLs `b` as well, and certifies all 100 again. With `b`
    down only the spare and `c` remain, so this succeeds only if every spare
    ledger is complete.
- Driver: `verification/measure/head_to_head_auth.sh`. Tables:
  `verification/measure/head_to_head_auth_tables.py`. Raw JSON lines:
  `verification/measure/head-to-head/run4-auth-mini-m4-m1.jsonl`.

## Hosts and topology

This is the same topology as run 3. The Air (`macbookair-rex`) was offline and is not used.

| Role | Host (Rex label) | Hardware | macOS | Network | Other load during the run |
| --- | --- | --- | --- | --- | --- |
| keeper `a`, zone-a; spare (repair) | `mac-mini-1-rex` | Mac18,5, Apple M6 | 27.0 | 1 GbE, 192.168.1.25 | Another session's `rustc` at ~330% CPU plus a Python process at 100%; load average 7–11 |
| keeper `b`, zone-b | `sachas-macbook-pro-rex` (M4) | Mac16,5, M4 Max | 26.3 | Wi-Fi, 192.168.1.14 | Claude renderer at 100%; load average ~5 |
| keeper `c`, zone-c, and the client | `macbook-pro-m1-rex` | MacBookPro18,1, M1 Pro | 15.5 | Wi-Fi, 192.168.1.18 | Another session's `rustc` at 100%; load average ~3.5 |

The consensus client's `domain` is zone-c and the kill victim is `c`, the
keeper on the client's host, as in run 3.

RTT (TCP one-byte echo, 1,000 samples), taken at the start of this run:

| From | To | Echo RTT p50 / p99 / p99.9 ms |
| --- | --- | --- |
| client | 192.168.1.25 | 4.1 / 92.0 / 94.9 |
| client | 192.168.1.14 | 9.0 / 100.3 / 425.0 |
| client | 192.168.1.18 | 0.1 / 0.2 / 0.2 |
| 192.168.1.25 | 192.168.1.14 | 5.4 / 91.6 / 94.0 |
| 192.168.1.25 | 192.168.1.18 | 4.1 / 92.8 / 95.6 |
| 192.168.1.14 | 192.168.1.25 | 4.5 / 89.4 / 92.7 |
| 192.168.1.14 | 192.168.1.18 | 8.7 / 107.2 / 419.6 |
| 192.168.1.18 | 192.168.1.25 | 4.2 / 92.5 / 96.0 |
| 192.168.1.18 | 192.168.1.14 | 9.1 / 96.6 / 101.4 |

These match run 3 within a few tenths of a millisecond at the median.

## Settings

The settings are those of `HEAD-TO-HEAD.md`: 256 B records, mTLS 1.3, `sync_mode: full`,
three keepers, writer batches as concurrent appends coalesced by the writer,
consensus batches as `append_batch`, 256 streams admitted, and 60 s retry of
`Unavailable`. Only these differ:

| Setting | writer, unsigned | writer, signed | consensus |
| --- | --- | --- | --- |
| Keeper `authenticated` section | absent | `signer_pkcs8_file` + `keys_file`, fresh keys per case | n/a (the consensus keeper's own authenticated history is not enabled or exercised) |
| Writer key set | none | `with_authentication(KeeperKeys)` | n/a |
| Repair workload | 2 records, trim through 1 (or 1 record, untrimmed) | same, plus `seed_authenticated` per stream | not run |
| Consensus-only settings | — | — | as in run 3: replicated catalog, finalized level and leases, `max_streams` 4,096, `domain` zone-c |

## Results

### a. Commit

| Variant | Streams | Batch | Runs | Records/run | Record ack p50 ms | p99 ms | p99.9 ms | Records/s | Keeper CPU s | Client CPU s | Max keeper RSS MiB | Keeper disk MiB | Certify final head p50 ms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| writer, unsigned | 32 | 32 | 3 | 4096 | 31.9 [30.1–35.0] | 57.4 [42.2–127.8] | 124.1 [50.9–138.9] | 17,018 [15,762–26,639] | 0.05 [0.05–0.05] | 0.05 [0.05–0.06] | 15 [14–15] | 3.1 [3.1–3.1] | — |
| writer, signed | 32 | 32 | 3 | 4096 | 35.8 [35.4–40.4] | 51.5 [47.3–61.3] | 63.0 [47.5–64.3] | 22,098 [21,893–24,381] | 0.15 [0.12–0.15] | 0.05 [0.05–0.07] | 15 [15–15] | 6.0 [5.0–8.0] | 9.5 [7.5–13.1] |
| consensus | 32 | 32 | 3 | 4096 | 33.0 [30.4–33.2] | 58.1 [46.3–66.0] | 58.3 [46.3–66.0] | 25,771 [25,415–26,336] | 0.19 [0.17–0.22] | 0.02 [0.02–0.03] | 63 [62–63] | 6.2 [6.1–6.2] | — |
| writer, unsigned | 1000 | 1 | 3 | 4000 | 32.3 [32.0–35.7] | 123.0 [120.3–143.5] | 126.2 [124.5–146.3] | 6,137 [5,981–6,630] | 0.31 [0.30–0.34] | 0.56 [0.47–0.63] | 19 [19–19] | 6.0 [6.0–6.1] | — |
| writer, signed | 1000 | 1 | 3 | 4000 | 50.1 [45.0–50.3] | 131.1 [131.1–131.1] | 137.5 [132.9–150.0] | 4,536 [4,166–4,983] | 0.85 [0.78–0.96] | 0.59 [0.38–0.62] | 20 [20–20] | 17.7 [17.7–17.7] | 9.5 [9.4–21.7] |
| writer, unsigned | 1000 | 32 | 3 | 64000 | 87.3 [85.8–90.1] | 211.7 [192.4–218.4] | 230.5 [216.0–248.7] | 78,535 [71,875–81,015] | 0.29 [0.25–0.33] | 1.00 [0.53–1.01] | 43 [42–43] | 48.5 [47.3–49.3] | — |
| writer, signed | 1000 | 32 | 3 | 64000 | 116.9 [86.7–117.4] | 220.8 [220.3–236.3] | 245.8 [238.5–254.7] | 59,123 [58,618–69,522] | 0.92 [0.80–1.00] | 0.93 [0.49–1.01] | 43 [43–44] | 84.3 [74.0–85.1] | 11.0 [9.2–19.9] |
| consensus | 1000 | 32 | 3 | 64000 | 1488.8 [1287.1–1722.2] | 14643.1 [13915.3–39259.3] | 20700.5 [20437.6–48346.7] | 2,353 [1,170–2,390] | 53.07 [49.50–125.13] | 12.35 [11.88–23.92] | 567 [535–588] | 63.8 [63.2–75.8] | — |

Signing overhead (signed vs. unsigned medians; positive means signed is higher):

| Commit case | p50 ack | p99 ack | p99.9 ack | Records/s | Keeper CPU | Keeper disk |
| --- | --- | --- | --- | --- | --- | --- |
| 32×32 | +12% | −10% | −49% | +30% | +200% | +92% |
| 1000×1 | +55% | +7% | +9% | −26% | +174% | +193% |
| 1000×32 | +34% | +4% | +7% | −25% | +217% | +74% |

- **32×32 is within noise.** One unsigned repeat hit a Wi-Fi stall (p99 127.8 ms,
  15,762 rec/s), and the measured interval is under 0.3 s. So the negative tail
  overheads and the positive throughput overhead are not effects of signing. The
  p50 moved +4 ms with non-overlapping ranges.
- **At 1,000 streams signing costs 25–26% of throughput and +18 ms (1000×1) or
  +30 ms (1000×32) at p50.** The tails barely move (+4–9%), because the Wi-Fi
  stalls bound them in both variants. The spread is tight: the slowest unsigned
  repeat beats the fastest signed repeat at 1000×1. At 1000×32, one signed repeat
  (86.7 ms p50, 69,522 rec/s) did overlap the unsigned range.
- **Keeper CPU roughly triples**: about +10 µs per record summed over three
  keepers at 1000×32 (0.29 → 0.92 s for 64,000 records). Each committed record
  costs one SHA-256, plus one ledger append per changed stream per round, on the
  keeper engine thread. These are `ps` CPU-time deltas at 10 ms resolution.
- **Disk.** The ledger is 133 B per record per keeper. At 1000×32 that predicts
  64,000 × 133 B × 3 ≈ 24 MiB, and the measured growth is +36 MiB allocated. At
  1000×1 the +11.7 MiB is almost exactly one 4 KiB block for each of the
  3 × 1,000 per-stream `.leaves` files. Each stream's ledger is its own file, so
  the minimum allocation dominates at small record counts.
- **Certifying a final head** (two signatures plus client verification, taken
  after the run) has a p50 of 9.5–11 ms. No stream failed to certify in any repeat.
- **Consensus vs. writer, signed.** At 32×32 consensus still leads on throughput
  (25,771 vs. 22,098 rec/s) at a similar p50. At 1000×32 signed writer-driven
  stays about 25× faster in throughput and about 13× lower at p50, with p99
  roughly 66× lower. One consensus 1000×32 attempt failed outright, and an extra
  attempt replaced it (see "What was not measured").

### b. Head (32 streams, 2,016 calls per caller, 64 in parallel)

| Load | Caller | Variant | Runs | p50 ms | p99 ms | p99.9 ms | Unavailable |
| --- | --- | --- | --- | --- | --- | --- | --- |
| idle | writer | writer, unsigned | 3 | 6.4 [6.1–6.4] | 92.8 [92.5–93.7] | 93.8 [92.6–95.2] | 0 |
| idle | writer | writer, signed | 3 | 6.0 [6.0–7.1] | 90.4 [9.9–95.1] | 90.5 [10.8–101.7] | 0 |
| idle | writer signed | writer, signed | 3 | 14.5 [13.9–26.5] | 105.3 [102.2–122.8] | 114.2 [104.9–142.2] | 0 |
| idle | observer | writer, unsigned | 3 | 6.4 [6.1–6.8] | 94.1 [9.4–94.1] | 94.2 [9.5–96.7] | 0 |
| idle | observer | writer, signed | 3 | 6.3 [6.0–6.6] | 92.3 [92.0–93.0] | 92.4 [92.2–93.1] | 0 |
| idle | observer signed | writer, signed | 3 | 14.3 [14.1–28.3] | 102.3 [101.4–146.8] | 103.5 [103.4–155.2] | 0 |
| write | writer | writer, unsigned | 3 | 22.9 [22.7–24.6] | 113.2 [111.8–118.2] | 114.5 [114.1–123.0] | 0 |
| write | writer | writer, signed | 3 | 24.0 [22.8–25.5] | 109.7 [109.2–113.6] | 115.6 [110.5–122.4] | 0 |
| write | writer signed | writer, signed | 3 | 26.0 [25.2–28.4] | 128.2 [116.5–133.0] | 138.2 [127.3–138.4] | 0 |
| write | observer | writer, unsigned | 3 | 27.2 [26.5–28.9] | 122.9 [117.6–127.5] | 136.0 [121.1–160.1] | 0 |
| write | observer | writer, signed | 3 | 30.5 [27.9–32.3] | 123.8 [121.7–134.5] | 137.0 [126.7–144.1] | 0 |
| write | observer signed | writer, signed | 3 | 27.4 [27.3–34.2] | 144.4 [133.9–144.4] | 152.4 [151.5–153.9] | 0 |
| write | background append | writer, unsigned | 3 | 23.3 [22.3–24.5] | 115.2 [114.7–116.1] | 126.7 [122.9–150.2] |  |
| write | background append | writer, signed | 3 | 25.0 [23.4–25.9] | 115.3 [114.6–120.7] | 137.0 [124.6–139.5] |  |

Overhead, p50 / p99:

| Load | Caller | Plain `head` with signing on vs. off | Signed head vs. unsigned plain `head` |
| --- | --- | --- | --- |
| idle | writer | −6% / −3% (noise) | **+128% / +13%** (6.4 → 14.5 ms) |
| idle | observer | 0% / −2% | **+124% / +9%** (6.4 → 14.3 ms) |
| write | writer | +5% / −3% | +14% / +13% |
| write | observer | +12% / +1% | +1% / +17% |
| write | background append | +7% / 0% | — |

- Enabling the feature does not slow a plain `head`. A signed head costs about
  one more round to two keepers when idle (+8 ms p50, which matches the 4–9 ms
  RTTs to the mini and the M4). Under load the extra round overlaps the existing
  queueing, so the p50 cost is 1–14%. The tails gain 13–17%.
- No call returned `Unavailable` or any other error, including signed heads taken
  while appends advanced the head (a keeper signs only at or below its own head).

### c. SIGKILL keeper `c` (the client's local keeper), 1,000 streams

| Variant | Victim | Runs | Acked per run | Not acked (total) | Event to first ack p50 ms | p99 ms | Max ms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| writer, unsigned | c | 3 | 1000/1000/1000 | 0 | 167.1 [85.9–268.7] | 182.9 [91.3–285.0] | 186 [91–287] |
| writer, signed | c | 3 | 1000/1000/1000 | 0 | 126.7 [108.8–314.3] | 149.2 [125.9–340.9] | 149 [126–341] |

Signed vs. unsigned: −24% p50, −18% p99, −20% max. The ranges overlap almost
completely, so this is **no measurable difference**. The time is one quorum round
to the two remote keepers, plus whether a Wi-Fi stall lands in it. Run 3 measured
89.3 ms p50 for the same case.

### d. Repair of 100 idle streams after permanent loss of keeper `a`, with `seed_authenticated`

The writer-driven journal has no parking, so "parked" here means idle, as in
run 3. The spare runs on the mini before the loss. The sweeper runs 64 streams
in parallel. Times run from the SIGKILL. "Seed" is the time from a stream's
sweep returning to its `seed_authenticated` returning.

| Trimmed | Variant | Runs | Sweep p50 s | Sweep max s | Seed p50 s | Seed max s | Sweep+seed p50 s | Sweep+seed max s | Certified after repair + with `b` down (of 100, per run) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| yes | writer, unsigned | 3 | 0.19 [0.18–0.29] | 0.40 [0.30–0.58] | — | — | 0.19 [0.18–0.29] | 0.40 [0.30–0.58] | — |
| yes | writer, signed | 3 | 0.51 [0.39–1.03] | 1.31 [1.29–2.37] | 0.50 [0.49–0.50] | 0.51 [0.50–0.52] | 1.01 [0.89–1.52] | 1.61 [1.61–2.84] | 100+100, 100+100, 100+100 |
| no | writer, unsigned | 1 | 0.18 | 0.40 | — | — | 0.18 | 0.40 | — |
| no | writer, signed | 1 | 0.71 | 1.21 | 0.03 | 0.05 | 0.76 | 1.25 | 100+100 |

Signing overhead:

| Case | Sweep p50 | Sweep max | Sweep+seed p50 | Sweep+seed max |
| --- | --- | --- | --- | --- |
| trimmed (3 runs each) | +175% | +227% | **+447%** (0.19 → 1.01 s) | **+302%** (0.40 → 1.61 s) |
| untrimmed (1 run each) | +287% | +202% | +315% | +211% |

- **The seed works.** In every signed run all 100 streams certified after the
  repair. All 100 also certified again with `b` SIGKILLed, when only the spare
  and `c` can sign, so every spare ledger was complete. Before the loss, all 100
  certified in every run.
- **A real seed costs a flat ~0.5 s per stream.** It was 0.49–0.52 s in every
  trimmed run, whenever the stream's sweep finished. Untrimmed, the spare already
  holds every leaf, and `seed_authenticated` only certifies, in 0.03 s. Measured
  from the client, `seed()` is one `Leaves` page from a signer plus one `Seed`
  install, after the certify. The keeper answers authenticated requests inline on
  its engine thread (`keeper/mod.rs`), and a `Seed` install does two data syncs
  (`keeper/ledger.rs`, staging file and chain append) on the mini under
  `F_FULLFSYNC`. The flat 0.5 s is not explained by these numbers. It is worth a
  profile before RTDB relies on mass reseeding.
- **The sweep itself is 2.7–3.9× slower with signing** (p50 0.19 → 0.51 s
  trimmed, 0.18 → 0.71 s untrimmed). That cost lands before any seed call, so it
  comes from the authenticated keepers handling the sweep's requests. The likely
  sources are leaf ingestion and its ledger writes on the spare and the
  survivors. The harness does not separate them.
- Run 3 measured the untrimmed unsigned case at 0.3 / 0.4 s (p50 / max). Today's
  0.18 / 0.40 s agrees.

## What differs between the variants and backends

1. Signed vs. unsigned writer-driven: only the keeper `authenticated` section, the
   generated key files, and the writer's key set differ. Binaries, hosts,
   topology, record size and concurrency are identical. Both variants ran in one
   session, interleaved, with the order flipped per repeat.
2. Repair adds `seed_authenticated` only in the signed variant. That is the step
   signed history requires. The unsigned variant has nothing to seed. Both use the
   same trim workload.
3. Consensus ran with run 3's configuration (replicated catalog, finalized level
   and leases, `max_streams` 4,096, zone-c `domain`). Consensus authenticated
   history was not enabled, so the consensus rows are an unsigned baseline. They
   are not a signed-vs-signed comparison.
4. The commit case's "certify final head" runs outside the measured interval in
   the signed variant, so it does not affect the commit figures.

## What was not measured

- **Consensus repair, head and kill**: out of scope for this rerun (commit 32×32
  and 1000×32 only).
- **A failed consensus 1000×32 attempt.** One of four attempts exited with an
  error, and no row was written for it. Its stderr was overwritten before it
  could be read. In run 1 the same failure mode was the harness's 60 s retry limit
  (`Elapsed`). The table uses the three successful attempts.
- **Signed consensus** (consensus `create_authenticated` streams): not enabled,
  so signing overhead is measured for the writer-driven journal only.
- **Proofs other than heads**: `inclusion`, `consistency` and
  `authenticated_archive` were not timed. Nor was signing a size below the
  ledger's end, which reads the ledger in `O(size)` instead of using the
  in-memory frontier.
- **Kill victim `a`**, takeover, and repair at 1,000 streams were not rerun.
- **Statistical confidence.** Three repeats give a range, not a confidence
  interval. Other sessions' compiles ran on the mini and the M1 throughout.
- **The cause of the flat ~0.5 s seed** and of the slower authenticated sweep
  (see d.).

## Reproduce

Start the agents as in `HEAD-TO-HEAD.md`, with binaries built from this branch,
then on the client:

```sh
verification/measure/head_to_head_auth.sh ~/code/wd-bench2/bin/head-to-head TOKEN \
    192.168.1.25,192.168.1.14,192.168.1.18 run-auth.jsonl zone-c 2 3 1
python3 -I verification/measure/head_to_head_auth_tables.py run-auth.jsonl
```
