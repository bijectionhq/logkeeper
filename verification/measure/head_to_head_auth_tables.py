#!/usr/bin/env python3
"""Turns head_to_head_auth.sh JSON lines into the tables of HEAD-TO-HEAD-AUTH.md.

Each cell is the median over repeats, followed by [min-max] when a case ran
more than once. Overhead is (signed - unsigned) / unsigned of the medians.

    python3 -I head_to_head_auth_tables.py run.jsonl
"""
import json
import statistics
import sys


def table(header, rows):
    print("| " + " | ".join(header) + " |")
    print("| " + " | ".join("---" for _ in header) + " |")
    for row in rows:
        print("| " + " | ".join(str(cell) for cell in row) + " |")
    print()


def cell(values, fmt="{:.1f}"):
    values = [v for v in values if v is not None]
    if not values:
        return "n/a", None
    med = statistics.median(values)
    text = fmt.format(med)
    if len(values) > 1:
        text += f" [{fmt.format(min(values))}–{fmt.format(max(values))}]"
    return text, med


def pct(signed, unsigned):
    if signed is None or unsigned in (None, 0):
        return "n/a"
    return f"{100 * (signed - unsigned) / unsigned:+.0f}%"


def get(row, *path):
    for key in path:
        if row is None:
            return None
        row = row.get(key) if isinstance(row, dict) else None
    return row


def variant(row):
    if row["backend"] == "consensus":
        return "consensus"
    return "writer, signed" if row.get("authenticated") else "writer, unsigned"


def main(path):
    rows = [json.loads(line) for line in open(path) if line.strip().startswith("{")]
    failed = [row for row in rows if "failed" in row]
    by = lambda case: [row for row in rows if row.get("case") == case]

    def triple(stats):
        if not stats:
            return "n/a"
        return " / ".join(f"{stats[k]:.1f}" for k in ("p50_ms", "p99_ms", "p999_ms"))

    table(["From", "To", "Echo RTT p50 / p99 / p99.9 ms"],
          [[r["from"], r["to"], triple(r["echo"])] for r in by("rtt")])

    # Commit.
    groups = {}
    for r in by("commit"):
        groups.setdefault((r["streams"], r["batch"]), {}).setdefault(variant(r), []).append(r)
    out, over = [], []
    for (streams, batch), variants in sorted(groups.items()):
        meds = {}
        for name in ("writer, unsigned", "writer, signed", "consensus"):
            runs = variants.get(name)
            if not runs:
                continue
            m = {}
            p50, m["p50"] = cell([get(r, "record", "p50_ms") for r in runs])
            p99, m["p99"] = cell([get(r, "record", "p99_ms") for r in runs])
            p999, m["p999"] = cell([get(r, "record", "p999_ms") for r in runs])
            rps, m["rps"] = cell([r["records_per_sec"] for r in runs], "{:,.0f}")
            cpu, m["cpu"] = cell([r["keeper_cpu_seconds"]["total"] for r in runs], "{:.2f}")
            ccpu, m["ccpu"] = cell([r["client_cpu_seconds"] for r in runs], "{:.2f}")
            disk, m["disk"] = cell([sum((v["disk"] or {}).get("allocated_mib") or 0
                                        for v in r["resources_after"].values()) for r in runs])
            rss, m["rss"] = cell([max((v["process"] or {}).get("rss_mib") or 0
                                      for v in r["resources_after"].values()) for r in runs], "{:.0f}")
            cert, m["cert"] = cell([get(r, "certify_final_head", "latency", "p50_ms") for r in runs])
            certfail = sum(sum((get(r, "certify_final_head", "failed") or {}).values()) for r in runs)
            meds[name] = m
            out.append([name, streams, batch, len(runs), runs[0]["record"]["n"], p50, p99, p999, rps,
                        cpu, ccpu, rss, disk,
                        cert + (f" ({certfail} failed)" if certfail else "") if cert != "n/a" else "—"])
        u, s = meds.get("writer, unsigned"), meds.get("writer, signed")
        if u and s:
            over.append([f"{streams}×{batch}", pct(s["p50"], u["p50"]), pct(s["p99"], u["p99"]),
                         pct(s["p999"], u["p999"]), pct(s["rps"], u["rps"]),
                         pct(s["cpu"], u["cpu"]), pct(s["disk"], u["disk"])])
    table(["Variant", "Streams", "Batch", "Runs", "Records/run", "Record ack p50 ms",
           "p99 ms", "p99.9 ms", "Records/s", "Keeper CPU s", "Client CPU s",
           "Max keeper RSS MiB", "Keeper disk MiB", "Certify final head p50 ms"], out)
    table(["Commit case", "p50 ack", "p99 ack", "p99.9 ack", "Records/s", "Keeper CPU",
           "Keeper disk"], over)

    # Head.
    groups = {}
    for r in by("head"):
        for row in r["rows"]:
            caller = row["caller"]
            key = ("write" if row["loaded"] else "idle", caller)
            stats = row.get("head") or row.get("append")
            groups.setdefault(key, {}).setdefault(variant(r), []).append((stats, row.get("unavailable")))
    out = []
    order = lambda k: (k[0] != "idle", k[1])
    for key in sorted(groups, key=order):
        for name in ("writer, unsigned", "writer, signed"):
            runs = groups[key].get(name)
            if not runs:
                continue
            p50, _ = cell([get(s, "p50_ms") for s, _ in runs])
            p99, _ = cell([get(s, "p99_ms") for s, _ in runs])
            p999, _ = cell([get(s, "p999_ms") for s, _ in runs])
            unavailable = sum(u or 0 for _, u in runs)
            out.append([key[0], key[1], name, len(runs), p50, p99, p999,
                        unavailable if key[1] != "background append" else ""])
    table(["Load", "Caller", "Variant", "Runs", "p50 ms", "p99 ms", "p99.9 ms", "Unavailable"], out)

    # Kill.
    groups = {}
    for r in by("kill"):
        groups.setdefault(variant(r), []).append(r)
    out = []
    for name in ("writer, unsigned", "writer, signed"):
        runs = groups.get(name)
        if not runs:
            continue
        p50, _ = cell([get(r, "event_to_ack", "p50_ms") for r in runs])
        p99, _ = cell([get(r, "event_to_ack", "p99_ms") for r in runs])
        mx, _ = cell([get(r, "event_to_ack", "max_ms") for r in runs], "{:.0f}")
        acked = "/".join(str(r.get("acked")) for r in runs)
        notacked = sum(sum((r.get("not_acked") or {}).values()) for r in runs)
        out.append([name, runs[0]["victim"], len(runs), acked, notacked, p50, p99, mx])
    table(["Variant", "Victim", "Runs", "Acked per run", "Not acked (total)",
           "Event to first ack p50 ms", "p99 ms", "Max ms"], out)

    # Repair.
    groups = {}
    for r in by("repair"):
        groups.setdefault((r.get("trimmed_before_loss", False), variant(r)), []).append(r)
    out = []
    for (trim, name), runs in sorted(groups.items()):
        sec = lambda key, stat: cell([(get(r, key, stat) or 0) / 1000 if get(r, key, stat) is not None
                                      else None for r in runs], "{:.2f}")[0]
        check = []
        for r in runs:
            c = r.get("seed_check")
            if c:
                ok = lambda part: (get(c, part, "latency", "n") or 0)
                check.append(f"{ok('after_repair')}+{ok('spare_and_c_only')}")
        out.append(["yes" if trim else "no", name, len(runs), sec("sweep", "p50_ms"),
                    sec("sweep", "max_ms"), sec("seed_only", "p50_ms"), sec("seed_only", "max_ms"),
                    sec("completion", "p50_ms"), sec("completion", "max_ms"),
                    ", ".join(check) if check else "—"])
    table(["Trimmed", "Variant", "Runs", "Sweep p50 s", "Sweep max s", "Seed p50 s",
           "Seed max s", "Sweep+seed p50 s", "Sweep+seed max s",
           "Certified after repair + with b down (per run, of 100)"], out)

    for row in failed:
        print(f"Failed: `{row['failed']}`")


main(sys.argv[1])
