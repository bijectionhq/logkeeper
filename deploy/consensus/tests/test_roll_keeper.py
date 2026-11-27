"""Exercise the operator guard with Kubernetes and keeper responses in memory."""

import contextlib
import importlib.util
import io
from pathlib import Path
import unittest
from unittest.mock import Mock, patch


spec = importlib.util.spec_from_file_location(
    "roll_keeper", Path(__file__).parent.parent / "kubernetes" / "roll-keeper.py"
)
roll = importlib.util.module_from_spec(spec)
spec.loader.exec_module(roll)


def pod(uid, revision, *, ready=False):
    return {
        "metadata": {
            "uid": uid,
            "ownerReferences": [{"kind": "StatefulSet", "uid": "sts", "controller": True}],
            "labels": {**roll.APP_LABELS, "controller-revision-hash": revision},
        },
        "status": {
            "hostIP": "10.0.1.10",
            "conditions": [{"type": "Ready", "status": "True" if ready else "False"}],
        },
    }


class RolloverTest(unittest.TestCase):
    def setUp(self):
        self.cluster = Mock()
        self.sts = {
            "metadata": {"uid": "sts", "generation": 3},
            "spec": {"replicas": 1, "updateStrategy": {"type": "OnDelete"}},
            "status": {"updateRevision": "new", "observedGeneration": 3},
        }
        self.budget = {"spec": {
            "selector": {"matchLabels": roll.APP_LABELS}, "maxUnavailable": 1,
        }}
        self.cluster.safe_to_stop.return_value = {"safe": True}
        self.cluster.get.side_effect = [self.sts, self.budget, pod("old-pod", "old")]

    def rollover(self, *, evict=True):
        with contextlib.redirect_stdout(io.StringIO()):
            roll.rollover(self.cluster, "logkeeper-0", evict, timeout=30)

    def test_check_only(self):
        self.rollover(evict=False)
        self.cluster.safe_to_stop.assert_called_once_with("logkeeper-0-0", "10.0.1.10")
        self.cluster.evict.assert_not_called()

    def test_safe_to_stop_refused(self):
        self.cluster.safe_to_stop.return_value = {"safe": False}
        with self.assertRaisesRegex(roll.RollError, "refused safe-to-stop"):
            self.rollover()
        self.cluster.evict.assert_not_called()

    def test_safe_to_stop_unavailable(self):
        self.cluster.safe_to_stop.side_effect = roll.RollError("TLS error")
        with self.assertRaisesRegex(roll.RollError, "TLS error"):
            self.rollover()
        self.cluster.evict.assert_not_called()

    def test_budget_not_configured(self):
        self.budget["spec"]["maxUnavailable"] = 2
        with self.assertRaisesRegex(roll.RollError, "PodDisruptionBudget"):
            self.rollover()
        self.cluster.safe_to_stop.assert_not_called()
        self.cluster.evict.assert_not_called()

    def test_eviction_waits_for_replacement(self):
        self.cluster.get.side_effect = [
            self.sts, self.budget, pod("old-pod", "old"), None,
            pod("new-pod", "new"), pod("new-pod", "new", ready=True),
        ]
        with patch.object(roll.time, "sleep"):
            self.rollover()
        self.cluster.evict.assert_called_once_with("logkeeper-0-0", "old-pod")

    def test_eviction_rejection_stops(self):
        self.cluster.evict.side_effect = roll.RollError("429 Too Many Requests")
        with self.assertRaisesRegex(roll.RollError, "429 Too Many Requests"):
            self.rollover()
        self.cluster.evict.assert_called_once_with("logkeeper-0-0", "old-pod")
        self.assertEqual(self.cluster.get.call_count, 3)

    def test_eviction_uses_uid_as_api_precondition(self):
        cluster = roll.Cluster("staging", "logkeeper")
        with patch.object(cluster, "run") as run:
            cluster.evict("logkeeper-0-0", "pod-uid")
        self.assertEqual(run.call_args.args, (
            "create", "--raw", "/api/v1/namespaces/logkeeper/pods/logkeeper-0-0/eviction", "-f", "-",
        ))
        self.assertEqual(run.call_args.kwargs["body"]["deleteOptions"], {
            "preconditions": {"uid": "pod-uid"},
        })
