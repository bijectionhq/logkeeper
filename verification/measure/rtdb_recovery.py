#!/usr/bin/env python3
"""Rehearse two-voter recovery against an isolated six-keeper RTDB Multi cell.

All service addresses, identities, credentials and storage paths are created
inside the new output directory. The result records exact binaries and the
receipts rechecked after recovery. It exercises process failure on one host.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import socket
import subprocess
import sys
import time
import uuid


def digest(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def keeper_group(check, binary, work, logs):
    class RecoveryKeepers(check.Keepers):
        def __init__(self):
            self.binary, self.logs, self.processes = binary, logs, {}
            self.pki = check.Pki(work, "journal")
            self.voters = sorted(str(uuid.uuid4()) for _ in range(3))
            self.spares = [str(uuid.uuid4()), str(uuid.uuid4())]
            self.other = str(uuid.uuid4())
            catalog = self.other
            catalog_voters = sorted([self.other, *self.spares])
            roster = self.all()
            domains = dict(zip(roster, ["a", "b", "c", "b", "c", "a"]))
            sockets = []
            try:
                self.addresses = {}
                for lane in ("keepers", "peers", "bulk"):
                    self.addresses[lane] = {}
                    for keeper in roster:
                        port = socket.socket()
                        sockets.append(port)
                        port.bind(("127.0.0.1", 0))
                        self.addresses[lane][keeper] = f"127.0.0.1:{port.getsockname()[1]}"
            finally:
                for port in sockets:
                    port.close()
            registry = work / "registry"
            registry.mkdir()
            write_json(registry / "placement.json", dict(catalog=catalog, domains=domains))
            self.configs = {}
            for keeper in roster:
                cert, key = self.pki.issue(
                    f"keeper-{keeper}", f"URI:urn:logkeeper:keeper:{keeper}",
                    "serverAuth,clientAuth",
                )
                data = work / f"data-{keeper}"
                write_json(registry / f"{keeper}.provision.json", dict(
                    keeper=keeper, data=str(data), domain=domains[keeper],
                    certificate_sha256=digest(cert),
                ))
                config = work / f"keeper-{keeper}.json"
                write_json(config, dict(
                    keeper=keeper, listen=self.addresses["keepers"][keeper], data=str(data),
                    enrollment=str(registry), tls=dict(
                        certificate=str(cert), private_key=str(key), ca=str(self.pki.ca),
                    ), **self.addresses, domains=domains, catalog=catalog,
                    catalog_voters=catalog_voters, sync_mode="fsync",
                    readers=[check.PRINCIPAL], writers=[check.PRINCIPAL],
                    administrators=[check.PRINCIPAL],
                ))
                self.command(keeper, "initialize")
                self.configs[keeper] = config
            self.client = self.pki.issue("rtdb-writer", f"URI:{check.PRINCIPAL}", "clientAuth")
            cert, key = self.client
            self.operator = work / "operator.json"
            write_json(self.operator, dict(
                tls=dict(certificate=str(cert), private_key=str(key), ca=str(self.pki.ca)),
                keepers=self.addresses["keepers"], catalog=catalog, catalog_voters=catalog_voters,
            ))
            journal = work / "journal.json"
            write_json(journal, dict(
                keepers=self.addresses["keepers"], catalog=catalog, voters=self.voters,
                catalog_voters=catalog_voters, quota_bytes=8 << 30, max_record_bytes=4 << 20,
            ))
            self.url = f"logkeeper-consensus://{journal}"

        def all(self):
            return [*self.voters, *self.spares, self.other]

        def command(self, keeper, action, *args, check=True):
            path = work / f"keeper-{keeper}.json"
            return subprocess.run(
                [binary, "keeper", action, "--config", path, *args],
                check=check, stdout=subprocess.PIPE, stderr=None, timeout=60,
            )

        def stop(self, keeper, kill=False):
            stop_process(self.processes[keeper], kill)
            del self.processes[keeper]

    return RecoveryKeepers()


def local_rtdb(check, binary, work, keepers, logs):
    rtdb = check.Rtdb(binary, work, keepers, logs, "deferred")

    # The bench fixture normally inherits the shell environment. Start this
    # drill without cloud, authentication, storage or service configuration.
    rtdb.env = {key: os.environ[key] for key in ("PATH", "LANG", "TMPDIR") if key in os.environ}
    rtdb.env.update({
        "RTDB_MULTI_BINARY_CHECKPOINTS": "1",
        "RTDB_MULTI_DEFERRED_CHECKPOINTS": "1",
        "XTDB_LOGGING_LEVEL_DB_CHECKPOINT": "debug",
    })
    return rtdb


def refuse_restart(keepers, keeper):
    result = subprocess.run(
        [keepers.binary, "keeper", "--config", keepers.configs[keeper]],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10,
    )
    (keepers.logs / f"retired-{keeper}.log").write_bytes(result.stdout)
    if result.returncode == 0:
        raise RuntimeError(f"retired keeper {keeper} restarted")


def stop_process(process, kill=False):
    if process is None or process.poll() is not None:
        return
    process.send_signal(signal.SIGKILL if kill else signal.SIGTERM)
    try:
        process.wait(timeout=30)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def finalize(keepers):
    for attempt in range(10):
        result = subprocess.run(
            [keepers.binary, "admin", "finalize-version", "--config", keepers.operator, "--json"],
            capture_output=True, timeout=10,
        )
        if result.returncode == 0:
            version = json.loads(result.stdout)["cluster_version"]
            if version < 3:
                raise RuntimeError(f"recovery markers require cluster version 3, found {version}")
            return version
        if attempt < 9:
            time.sleep(0.5)
    raise RuntimeError(f"could not finalize the cluster version: {result.stderr.decode()}")


def verify_markers(log, streams):
    markers = {}
    for line in log.read_text().splitlines():
        if "code=rtdb/journal-recovered" not in line or "marker_lsn=" not in line:
            continue
        fields = dict(re.findall(r"\b(database|head|epoch|marker_lsn)=([0-9a-f-]+)\b", line))
        database = fields.pop("database")
        if database in markers or int(fields["marker_lsn"]) != int(fields["head"]) + 1:
            raise RuntimeError(f"unexpected recovery marker for {database}")
        markers[database] = fields
    if markers.keys() != set(streams):
        raise RuntimeError(f"expected one atomic recovery marker per stream, got {markers}")
    return markers


def rehearse(args, check, work, logs, report):
    keepers = keeper_group(check, args.logkeeper, work, logs)
    rtdb = local_rtdb(check, args.rtdb, work, keepers, logs)
    receipts = []
    phases = report["phases"]
    try:
        for keeper in keepers.all():
            keepers.start(keeper)
        report["cluster_version"] = finalize(keepers)
        rtdb.start()
        check.commit(rtdb, args.clients, args.seconds, "before-recovery", phases, receipts)
        if not receipts:
            raise RuntimeError("no acknowledged pre-recovery transactions")
        report["pre_recovery_receipts"] = len(receipts)
        # Keep the original receipt identities as evidence for read-back.
        write_json(args.output / "pre-recovery-receipts.json", [
            {key: value.hex() if isinstance(value, bytes) else value for key, value in item.items()}
            for item in receipts
        ])
        stop_process(rtdb.process, kill=True)
        outage = time.monotonic()
        survivor, *lost = keepers.voters
        for keeper in lost:
            keepers.stop(keeper, kill=True)
        keepers.stop(survivor)

        inspected = json.loads(keepers.command(survivor, "inspect", "--json").stdout)
        streams = [
            item["stream"] for item in inspected["streams"]
            if item["stream_state"] == "live" and item["head"] is not None
        ]
        if not streams:
            raise RuntimeError("no live streams on the surviving keeper")
        proofs = []
        for keeper in lost:
            proof = keepers.command(
                keeper, "fence-recovery", "--acknowledge-keeper-retirement", keeper,
            ).stdout
            json.loads(proof)
            path = logs / f"{keeper}.fence.json"
            path.write_bytes(proof)
            proofs.extend(["--fence-proof", path])
            refuse_restart(keepers, keeper)

        for stream in streams:
            report_bytes = keepers.command(
                survivor, "recover-stream", "--stream", stream, "--acknowledge-data-loss",
                "--lost", ",".join(lost), "--with", ",".join(keepers.spares), *proofs,
            ).stdout
            (logs / f"recover-{stream}.log").write_bytes(report_bytes)
        report["recovered_streams"] = streams
        report["retired_keepers"] = lost
        keepers.start(survivor)
        rtdb.start()
        check.recheck(rtdb, "after-recovery", phases, receipts)
        report["rto_seconds"] = round(time.monotonic() - outage, 3)
        report["lost_acknowledged_receipts"] = 0
        check.commit(rtdb, args.clients, args.seconds, "new-writes", phases, receipts)
        if len(receipts) <= report["pre_recovery_receipts"]:
            raise RuntimeError("no acknowledged transactions after recovery")
        check.recheck(rtdb, "final-recheck", phases, receipts)
        stop_process(rtdb.process, kill=True)
        rtdb.start()
        check.recheck(rtdb, "after-second-rtdb-restart", phases, receipts)
        report["total_receipts"] = len(receipts)
        report["recovery_markers"] = verify_markers(logs / "rtdb.log", streams)
        if report["rto_seconds"] > args.max_rto_seconds:
            raise RuntimeError("recovery exceeded the configured RTO")
    finally:
        try:
            stop_process(rtdb.process)
        finally:
            for keeper in list(keepers.processes):
                keepers.stop(keeper)


def positive(value):
    result = int(value)
    if result < 1:
        raise argparse.ArgumentTypeError("enter a positive integer")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logkeeper", required=True, type=Path)
    parser.add_argument("--rtdb", required=True, type=Path)
    parser.add_argument("--rtdb-source", required=True, type=Path, help="RTDB checkout with rust/bench")
    parser.add_argument("--max-rto-seconds", required=True, type=positive)
    parser.add_argument("--clients", default=4, type=positive)
    parser.add_argument("--seconds", default=2, type=positive)
    parser.add_argument("output", type=Path, help="new directory for local drill data and reports")
    args = parser.parse_args()
    for key in ("logkeeper", "rtdb", "rtdb_source", "output"):
        setattr(args, key, getattr(args, key).resolve())
    sys.path.insert(0, str(args.rtdb_source / "rust" / "bench"))
    import v1_consensus_keepers as check

    # These scratch directories hold generated private keys.
    os.umask(0o077)
    args.output.mkdir(exist_ok=False)
    work, logs = args.output / "work", args.output / "logs"
    work.mkdir()
    logs.mkdir()
    report = {
        "scope": "isolated single-host process failure",
        "logkeeper_sha256": digest(args.logkeeper),
        "rtdb_sha256": digest(args.rtdb),
        "rtdb_fixture_commit": subprocess.check_output(
            ["git", "-C", args.rtdb_source, "rev-parse", "HEAD"], text=True
        ).strip(),
        "max_rto_seconds": args.max_rto_seconds,
        "phases": [],
    }
    try:
        rehearse(args, check, work, logs, report)
        report["passed"] = True
    except Exception as error:
        report.update(passed=False, error_type=type(error).__name__)
        raise
    finally:
        write_json(args.output / "results.json", report)


if __name__ == "__main__":
    main()
