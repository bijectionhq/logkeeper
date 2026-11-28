#!/usr/bin/env python3
"""Turns head-to-head JSON lines into the Markdown tables of HEAD-TO-HEAD.md.

    python3 -I head_to_head_tables.py run1.jsonl
"""
import json
import sys


def triple(row, key="p50_ms"):
    if not row:
        return "n/a"
    return " / ".join(f"{row[k]:.1f}" for k in ("p50_ms", "p99_ms", "p999_ms"))


def table(header, rows):
    print("| " + " | ".join(header) + " |")
    print("| " + " | ".join("---" for _ in header) + " |")
    for row in rows:
        print("| " + " | ".join(str(cell) for cell in row) + " |")
    print()


def main(path):
    rows = [json.loads(line) for line in open(path) if line.strip().startswith("{")]
    failed = [row for row in rows if "failed" in row]
    by = lambda case: [row for row in rows if row.get("case") == case]

    table(["From", "To", "Echo RTT p50 / p99 / p99.9 ms"],
          [[r["from"], r["to"], triple(r["echo"])] for r in by("rtt")])

    commit = []
    for r in by("commit"):
        res = r["resources_after"]
        rss = max((v["process"] or {}).get("rss_mib") or 0 for v in res.values())
        disk = sum((v["disk"] or {}).get("allocated_mib") or 0 for v in res.values())
        cpu = r["keeper_cpu_seconds"]["total"]
        n = r["record"]["n"]
        commit.append([r["backend"] + ("" if r["batch_mode"] == "native" else " (concurrent)"),
                       r["streams"], r["batch"], n, triple(r["record"]), triple(r["batch_ack"]),
                       f"{r['records_per_sec']:,.0f}", f"{cpu:.1f}", f"{1000 * cpu / n:.2f}",
                       f"{r['client_cpu_seconds']:.1f}", f"{rss:.0f}", f"{disk:.1f}"])
    table(["Backend", "Streams", "Batch", "Records", "Record ack ms", "Batch ack ms", "Records/s",
           "Keeper CPU s", "Keeper CPU ms/record", "Client CPU s", "Max keeper RSS MiB",
           "Keeper disk MiB"], commit)

    head = []
    for r in by("head"):
        for row in r["rows"]:
            if "head" in row:
                head.append([r["backend"], "write" if row["loaded"] else "idle", row["caller"],
                             row["head"]["n"] if row["head"] else 0, triple(row["head"]),
                             row["unavailable"]])
            else:
                head.append([r["backend"], "write", "background append", row["append"]["n"],
                             triple(row["append"]), ""])
    table(["Backend", "Load", "Caller", "OK", "Latency ms", "Unavailable"], head)

    table(["Backend", "Victim", "Streams", "Led by victim", "Acked", "Not acked",
           "Event to ack ms (p50 / p99 / p99.9)", "Max ms", "Ack gap ms"],
          [[r["backend"], r["victim"], r["streams"], r["streams_led_by_victim"],
            r.get("acked", r["streams"]), r.get("not_acked", {}) or 0,
            triple(r["event_to_ack"]),
            f"{r['event_to_ack']['max_ms']:.0f}" if r["event_to_ack"] else "n/a", triple(r["ack_gap"])]
           for r in by("kill")])

    table(["Backend", "Streams", "New writer ms", "Seal ms", "Seal + catch-up ms",
           "Seal + catch-up + first append ms", "From takeover start ms", "Last stream s"],
          [[r["backend"], r["streams"], f"{r['new_writer_construct_ms']:.1f}", triple(r["seal"]),
            triple(r["seal_and_catch_up"]), triple(r["seal_catch_up_first_append"]),
            triple(r["from_takeover_start"]), f"{r['seconds']:.2f}"] for r in by("takeover")])

    def secs(row, keys):
        return " / ".join(f"{row[k] / 1000:.1f}" for k in keys) if row else "n/a"

    table(["Backend", "Streams", "Repaired", "Detection wait s", "Completion s (p50 / p99 / max)",
           "Minus detection wait s (p50 / max)"],
          [[r["backend"], r["streams"], r.get("repaired", r["streams"]), r["detection_wait_s"],
            secs(r["completion"], ("p50_ms", "p99_ms", "max_ms")),
            secs(r.get("completion_minus_repair_after"), ("p50_ms", "max_ms"))
            if "completion_minus_repair_after" in r else "same"] for r in by("repair")])

    for row in failed:
        print(f"Failed: `{row['failed']}`")


main(sys.argv[1])
