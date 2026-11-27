#!/usr/bin/env python3
"""Check one keeper's safe-to-stop report and optionally evict that pod."""

import argparse
import ipaddress
import json
import re
import subprocess
import time


APP_LABELS = {"app.kubernetes.io/name": "logkeeper"}
TLS_DIR = "/etc/logkeeper/tls"


class RollError(Exception):
    pass


class Cluster:
    def __init__(self, context, namespace):
        self.namespace = namespace
        self.command = ["kubectl", "--context", context, "--namespace", namespace]

    def run(self, *args, body=None):
        result = subprocess.run(
            [*self.command, "--request-timeout=12s", *args],
            input=json.dumps(body) if body is not None else None,
            capture_output=True,
            text=True,
            timeout=15,
        )
        if result.returncode:
            detail = "\n".join(filter(None, [result.stdout.strip(), result.stderr.strip()]))
            raise RollError(f"{' '.join(args)} failed\n{detail}")
        return result.stdout

    def get(self, kind, name, *, allow_missing=False):
        args = ["get", kind, name, "-o", "json"]
        if allow_missing:
            args.append("--ignore-not-found")
        output = self.run(*args)
        return json.loads(output) if output else None

    def safe_to_stop(self, pod, host_ip):
        address = ipaddress.ip_address(host_ip)
        host = f"[{address}]" if address.version == 6 else str(address)
        return json.loads(self.run(
            "exec", pod, "-c", "keeper", "--", "curl", "--noproxy", "*",
            "--silent", "--show-error", "--fail-with-body", "--max-time", "8",
            "--cacert", f"{TLS_DIR}/ca.crt",
            "--cert", f"{TLS_DIR}/tls.crt",
            "--key", f"{TLS_DIR}/tls.key",
            f"https://{host}:5741/safe-to-stop",
        ))

    def evict(self, pod, uid):
        self.run("create", "--raw", f"/api/v1/namespaces/{self.namespace}/pods/{pod}/eviction", "-f", "-", body={
            "apiVersion": "policy/v1",
            "kind": "Eviction",
            "metadata": {"name": pod, "namespace": self.namespace},
            "deleteOptions": {"preconditions": {"uid": uid}},
        })


def owned_by(pod, statefulset_uid):
    return any(
        ref["kind"] == "StatefulSet"
        and ref.get("controller") is True
        and ref["uid"] == statefulset_uid
        for ref in pod["metadata"].get("ownerReferences", [])
    )


def rollover(cluster, keeper, evict, timeout):
    sts = cluster.get("statefulset", keeper)
    sts_spec = sts["spec"]
    sts_status = sts.get("status", {})
    sts_uid = sts["metadata"]["uid"]
    if sts_spec["replicas"] != 1 or sts_spec["updateStrategy"]["type"] != "OnDelete":
        raise RollError(f"{keeper} must be a single-replica OnDelete StatefulSet")
    if sts_status.get("observedGeneration") != sts["metadata"]["generation"]:
        raise RollError(f"wait for {keeper}'s controller to observe its current template")
    revision = sts_status.get("updateRevision")
    if not revision:
        raise RollError(f"{keeper} has no observed update revision")

    budget = cluster.get("poddisruptionbudget", "logkeeper")["spec"]
    if budget.get("selector") != {"matchLabels": APP_LABELS} or budget.get("maxUnavailable") != 1:
        raise RollError("the logkeeper PodDisruptionBudget must select all keepers and allow one disruption")

    name = f"{keeper}-0"
    pod = cluster.get("pod", name)
    meta = pod["metadata"]
    if not owned_by(pod, sts_uid) or meta.get("deletionTimestamp"):
        raise RollError(f"{name} must be owned by {keeper} and running")
    if any(meta.get("labels", {}).get(key) != value for key, value in APP_LABELS.items()):
        raise RollError(f"{name} is outside the logkeeper PodDisruptionBudget")
    uid = meta["uid"]
    report = cluster.safe_to_stop(name, pod["status"]["hostIP"])
    if report.get("safe") is not True:
        raise RollError(f"{name} refused safe-to-stop\n{json.dumps(report)}")
    print(f"{name} passed safe-to-stop\n{json.dumps(report)}", flush=True)
    if not evict:
        return

    cluster.evict(name, uid)
    print(f"Eviction accepted for {name}. Waiting for revision {revision} to become Ready.", flush=True)
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        replacement = cluster.get("pod", name, allow_missing=True)
        if replacement and replacement["metadata"]["uid"] != uid:
            meta = replacement["metadata"]
            if not owned_by(replacement, sts_uid):
                raise RollError(f"replacement for {name} has an unexpected owner")
            if meta.get("labels", {}).get("controller-revision-hash") != revision:
                raise RollError(f"replacement for {name} has an unexpected revision")
            if not meta.get("deletionTimestamp") and any(
                condition["type"] == "Ready" and condition["status"] == "True"
                for condition in replacement.get("status", {}).get("conditions", [])
            ):
                print(f"Replacement for {name} is Ready.")
                return
        time.sleep(3)
    raise RollError(f"replacement for {name} did not become Ready in {timeout}s; stop the rollout")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("keeper", help="StatefulSet name, for example logkeeper-0")
    parser.add_argument("--evict", action="store_true", help="evict after a successful fresh preflight")
    parser.add_argument("--timeout", type=int, default=900, help="seconds to wait for the replacement")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?", args.namespace):
        parser.error("namespace must be a DNS label")
    if not re.fullmatch(r"logkeeper-[0-9]+", args.keeper):
        parser.error("keeper must be a logkeeper StatefulSet name")
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    try:
        rollover(Cluster(args.context, args.namespace), args.keeper, args.evict, args.timeout)
    except (RollError, ValueError, KeyError, TypeError, OSError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"Rollover stopped. Inspect the pod and API events before retrying.\n{error}\n")


if __name__ == "__main__":
    main()
