#!/usr/bin/env python3
"""Measure RTDB Multi through delay-proxy with keepers in three emulated zones.

Uses the RTDB v1 journal benchmark's workload and exact TxStatus verification.
The Python environment must have PyArrow installed.
"""

import argparse
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import socket
import subprocess
import sys
import time
from types import SimpleNamespace
import uuid


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def start_process(stack, log, *command):
    with log.open("w") as output:
        process = subprocess.Popen(command, stdout=output, stderr=output)
    stack.callback(stop_process, process)
    return process


def stop_process(process):
    if process is None or process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=30)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def verify_with_progress(verify):
    def checked(connect, answers):
        total = len(answers)
        started = time.monotonic()
        print(f"Timed writes finished. Checking {total} receipts through TxStatus.", flush=True)

        def progress():
            last = started
            for count, answer in enumerate(answers, 1):
                yield answer
                now = time.monotonic()
                if count == total or now - last >= 5:
                    print(f"Verified {count}/{total} receipts in {now - started:.1f}s.", flush=True)
                    last = now

        # The verifier requests the next item only after checking the current receipt.
        verify(connect, progress())

    return checked


def topology(args, harness, work):
    pki = harness.Pki(work, "journal")
    voters = [str(uuid.uuid4()) for _ in range(3)]
    catalog = str(uuid.uuid4())
    keepers = voters + [catalog]
    zones = dict(zip(keepers, "abca"))
    domains = dict(zip(keepers, ("zone-a", "zone-b", "zone-c", "directory")))
    links = []

    with ExitStack() as reservations:
        def address():
            listener = reservations.enter_context(socket.socket())
            listener.bind(("127.0.0.1", 0))
            return f"127.0.0.1:{listener.getsockname()[1]}"

        real = {
            lane: {keeper: address() for keeper in keepers}
            for lane in ("keepers", "peers", "bulk")
        }

        def route(source_zone, keeper, lane):
            target = real[lane][keeper]
            if args.direct:
                return target
            same_zone = source_zone == zones[keeper]
            delay = args.intra if same_zone else args.inter
            jitter = 0 if same_zone else args.jitter
            listen = address()
            links.append((listen, f"{listen}={target}/{delay}/{jitter}"))
            return listen

        registry = work / "registry"
        registry.mkdir()
        write_json(registry / "placement.json", dict(catalog=catalog, domains=domains))
        configs = {}
        for keeper in keepers:
            cert, key = pki.issue(
                f"keeper-{keeper}", f"URI:urn:logkeeper:keeper:{keeper}", "serverAuth,clientAuth",
            )
            data = work / f"data-{keeper}"
            write_json(registry / f"{keeper}.provision.json", dict(
                keeper=keeper, data=str(data), domain=domains[keeper],
                certificate_sha256=hashlib.sha256(cert.read_bytes()).hexdigest(),
            ))
            lanes = {
                lane: {
                    other: (real[lane][other] if other == keeper or lane == "keepers"
                            else route(zones[keeper], other, lane))
                    for other in keepers
                }
                for lane in real
            }
            config = work / f"keeper-{keeper}.json"
            write_json(config, dict(
                keeper=keeper, listen=real["keepers"][keeper], data=str(data),
                enrollment=str(registry), tls=dict(
                    certificate=str(cert), private_key=str(key), ca=str(pki.ca),
                ), **lanes, domains=domains, catalog=catalog, allow_single_catalog=True,
                sync_mode=args.sync_mode, readers=[harness.PRINCIPAL],
                writers=[harness.PRINCIPAL], administrators=[harness.PRINCIPAL],
            ))
            configs[keeper] = config

        client = pki.issue("rtdb-writer", f"URI:{harness.PRINCIPAL}", "clientAuth")
        journal = work / "journal.json"
        write_json(journal, dict(
            keepers={keeper: route("a", keeper, "keepers") for keeper in keepers},
            catalog=catalog, voters=voters, quota_bytes=8 << 30, max_record_bytes=4 << 20,
        ))

    for config in configs.values():
        subprocess.run([args.logkeeper, "keeper", "initialize", "--config", config], check=True)
    enrollment = SimpleNamespace(pki=pki, client=client, url=f"logkeeper-consensus://{journal}")
    return real, configs, links, enrollment


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("work", type=Path, help="new directory for results and logs")
    parser.add_argument("--rtdb-bench", required=True, type=Path, help="RTDB's rust/bench directory")
    parser.add_argument("--logkeeper", required=True, type=Path)
    parser.add_argument("--proxy", type=Path)
    parser.add_argument("--rtdb", required=True, type=Path)
    parser.add_argument("--direct", action="store_true", help="use direct loopback links as a control")
    parser.add_argument("--sync-mode", choices=("fsync", "full"), default="full")
    parser.add_argument("--intra", type=float, default=0.5, help="one-way delay within a zone in ms")
    parser.add_argument("--inter", type=float, default=3, help="one-way delay across zones in ms")
    parser.add_argument("--jitter", type=float, default=1, help="maximum cross-zone jitter in ms")
    parser.add_argument("--clients", type=int, nargs="+", default=[1, 4, 16, 64])
    parser.add_argument("--seconds", type=float, default=10)
    args = parser.parse_args()
    if not args.direct and not args.proxy:
        parser.error("proxied runs require --proxy")

    sys.path.insert(0, str(args.rtdb_bench.resolve()))
    import v1_consensus_keepers as harness

    work = args.work.resolve()
    work.mkdir(mode=0o700, parents=True)
    logs = work / "logs"
    logs.mkdir()
    real, configs, links, journal = topology(args, harness, work)

    def wait_for(address, process):
        host, port = address.split(":")
        harness.wait_for_port(host, int(port), process)

    results = []
    with ExitStack() as processes:
        if links:
            flags = [part for _, spec in links for part in ("--link", spec)]
            proxy = start_process(processes, logs / "proxy.log", args.proxy, *flags)
            for address, _ in links:
                wait_for(address, proxy)

        running = {
            keeper: start_process(
                processes, logs / f"keeper-{keeper}.log", args.logkeeper,
                "keeper", "--config", config,
            )
            for keeper, config in configs.items()
        }
        for lane in real.values():
            for keeper, address in lane.items():
                wait_for(address, running[keeper])

        rtdb = harness.Rtdb(args.rtdb, work, journal, logs)
        processes.callback(lambda: stop_process(rtdb.process))
        rtdb.start()

        intra, inter, jitter = (0, 0, 0) if args.direct else (args.intra, args.inter, args.jitter)
        verify = harness.driver.verify
        harness.driver.verify = verify_with_progress(verify)
        try:
            for clients in args.clients:
                print(f"Starting {clients} clients for {args.seconds:g}s of timed writes.", flush=True)
                row = harness.commit(rtdb, clients, args.seconds, "zones", [], [])
                results.append(dict(
                    sync_mode=args.sync_mode, direct=args.direct,
                    intra_ms=intra, inter_ms=inter, jitter_ms=jitter, **row,
                ))
                write_json(work / "results.json", results)
        finally:
            harness.driver.verify = verify


if __name__ == "__main__":
    main()
