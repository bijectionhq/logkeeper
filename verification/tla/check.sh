#!/usr/bin/env bash
set -euo pipefail

# Run all exhaustive TLA+ checks for Logkeeper's consensus protocol additions.
# Usage:
#   ./verification/tla/check.sh            # run all configs
#   ./verification/tla/check.sh fast       # skip the deep and slow liveness configs
#   ./verification/tla/check.sh additions  # run the focused consensus additions
#
# Exits non-zero when any configuration does not match its expected outcome:
# a property violated where it should hold, or a control that stopped failing.

ROOT="$(cd "$(dirname "$0")" && pwd)"
MODE="${1:-all}"

JAR="$("$ROOT/fetch-tla.sh")"
WORKERS="${TLC_WORKERS:-auto}"

find_java() {
  if [[ -n "${JAVA_BIN:-}" && -x "${JAVA_BIN}" ]]; then
    echo "$JAVA_BIN"
    return 0
  fi
  if command -v java >/dev/null 2>&1 && java -version >/dev/null 2>&1; then
    command -v java
    return 0
  fi
  for candidate in \
    "$HOME/.local/share/mise/installs/java"/*/bin/java \
    /opt/homebrew/opt/openjdk*/bin/java \
    /Library/Java/JavaVirtualMachines/*/Contents/Home/bin/java; do
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  done
  echo "No working Java runtime found. Install JDK 17+ or set JAVA_BIN." >&2
  exit 1
}

JAVA="$(find_java)"
RESULTS="$ROOT/.results"
mkdir -p "$RESULTS"

# expected: "pass" (exit 0), "invariant[:name]" (exit 12), or "liveness" (exit 13)
run_case() (
  local name="$1"
  local module="$2"
  local cfg="$3"
  local expected="$4"
  local extra="${5:-}"
  local log="$RESULTS/${name}.log"
  local meta
  meta="$(mktemp -d "${TMPDIR:-/tmp}/tlc-${name}.XXXXXX")"
  trap 'rm -rf "$meta"' EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM

  local args=(-Xmx2g -XX:+UseParallelGC -jar "$JAR" -workers "$WORKERS" -deadlock -metadir "$meta")
  if [[ "$extra" == "liveness" ]]; then
    args+=(-lncheck final)
  fi
  args+=(-config "$ROOT/$cfg" "$ROOT/$module")

  set +e
  "$JAVA" "${args[@]}" > "$log" 2>&1
  local rc=$?
  set -e

  local stats
  stats="$(grep -E 'states generated, [0-9]+ distinct states found' "$log" | tail -n 1 || true)"
  local elapsed
  elapsed="$(grep -E '^Finished in ' "$log" | tail -n 1 || true)"

  case "$expected" in
    pass)
      if [[ $rc -ne 0 ]] || ! grep -q "No error has been found" "$log"; then
        echo "[FAIL] $name: expected PASS, got exit=$rc (see $log)" >&2
        tail -n 20 "$log" >&2
        exit 1
      fi
      printf "[PASS] %-30s | %s | %s\n" "$name" "$stats" "$elapsed"
      ;;
    invariant|invariant:*)
      if [[ $rc -ne 12 ]]; then
        echo "[FAIL] $name: expected invariant counterexample (exit 12), got exit=$rc (see $log)" >&2
        tail -n 20 "$log" >&2
        exit 1
      fi
      local inv
      inv="$(grep -E '^Error: Invariant ' "$log" | head -n 1 || true)"
      if [[ "$expected" == invariant:* && "$inv" != "Error: Invariant ${expected#invariant:} is violated." ]]; then
        echo "[FAIL] $name: expected ${expected#invariant:}, got '$inv' (see $log)" >&2
        exit 1
      fi
      printf "[CE  ] %-30s | %s | %s | %s\n" "$name" "$inv" "$stats" "$elapsed"
      ;;
    liveness)
      if [[ $rc -ne 13 ]]; then
        echo "[FAIL] $name: expected liveness counterexample (exit 13), got exit=$rc (see $log)" >&2
        tail -n 20 "$log" >&2
        exit 1
      fi
      printf "[CE  ] %-30s | Temporal property violated | %s | %s\n" "$name" "$stats" "$elapsed"
      ;;
  esac
)

echo "Using Java: $JAVA"
echo "Using TLC:  $JAR"
echo

run_case "Relocation"                 "Relocation.tla" "Relocation.cfg"                pass liveness
run_case "RelocationNoCheckpointPin"  "Relocation.tla" "RelocationNoCheckpointPin.cfg" invariant:RootsReadable
run_case "RelocationReusePages"       "Relocation.tla" "RelocationReusePages.cfg"      invariant:RootsReadable
run_case "RelocationNoParkPins"       "Relocation.tla" "RelocationNoParkPins.cfg"      invariant:RootsReadable
run_case "RelocationLateWatermark"    "Relocation.tla" "RelocationLateWatermark.cfg"   invariant:RootsReadable
run_case "RelocationParkRace"         "Relocation.tla" "RelocationParkRace.cfg"        invariant:ParkCanReopenAfterRestart
run_case "AsyncAppend"                "AsyncAppend.tla" "AsyncAppend.cfg"               pass
run_case "AsyncAppendCountOverlay"    "AsyncAppend.tla" "AsyncAppendCountOverlay.cfg"   invariant:ChosenHasDurableQuorum
run_case "AsyncAppendRecoverTip"      "AsyncAppend.tla" "AsyncAppendRecoverTip.cfg"     invariant:RecoveryKeepsOnlyCommitted
if [[ "$MODE" != "fast" ]]; then
  run_case "AsyncAppendLiveness"      "AsyncAppend.tla" "AsyncAppendLiveness.cfg"       pass liveness
  run_case "AsyncAppendNoIdleFlush"   "AsyncAppend.tla" "AsyncAppendNoIdleFlush.cfg"    liveness liveness
fi
run_case "OffloadRetention"           "OffloadRetention.tla" "OffloadRetention.cfg"           pass liveness
run_case "OffloadRetentionNoBarrier"  "OffloadRetention.tla" "OffloadRetentionNoBarrier.cfg"  invariant:NoPostTrimRemoteRead
run_case "OffloadRetentionNoRecheck"  "OffloadRetention.tla" "OffloadRetentionNoRecheck.cfg"  invariant:NoPostTrimRemoteRead
run_case "ScopedSessions"             "ScopedSessions.tla" "ScopedSessions.cfg"             pass liveness
run_case "ScopedSessionsNoScope"      "ScopedSessions.tla" "ScopedSessionsNoScope.cfg"      invariant:ScopedDecision
run_case "ScopedSessionsNoSession"    "ScopedSessions.tla" "ScopedSessionsNoSession.cfg"    invariant:ScopedDecision
run_case "ScopedSessionsNoReplyGate"  "ScopedSessions.tla" "ScopedSessionsNoReplyGate.cfg"  invariant:LeaseGatesReply
run_case "ScopedSessionsInPlace"      "ScopedSessions.tla" "ScopedSessionsInPlace.cfg"      invariant:ImmutablePrefix

if [[ "$MODE" == "additions" ]]; then
  echo
  echo "All focused consensus checks matched expected outcomes."
  exit 0
fi

# Every property holds on the fixed protocol. The counterexamples the model
# found (CE-1 to CE-4, see README.md) are fixed, so their configurations now
# pass.
run_case "RaftParkSafety"              "LogkeeperProtocol.tla" "RaftParkSafety.cfg"              pass
run_case "ParkedRepairLiveness"        "LogkeeperProtocol.tla" "ParkedRepairLiveness.cfg"        pass liveness
run_case "AbortedReplaceLiveness"      "LogkeeperProtocol.tla" "AbortedReplaceLiveness.cfg"      pass liveness
run_case "RecoverySingleReturnNoSnap"  "LogkeeperProtocol.tla" "RecoverySingleReturnNoSnap.cfg"  pass
run_case "RecoverySingleReturnSnap"    "LogkeeperProtocol.tla" "RecoverySingleReturnSnap.cfg"    pass
run_case "RecoverySingleReturnLiveness" "LogkeeperProtocol.tla" "RecoverySingleReturnLiveness.cfg" pass liveness
run_case "RecoveryBothReturnLiveness"  "LogkeeperProtocol.tla" "RecoveryBothReturnLiveness.cfg"  pass liveness

# The endgame's epoch leases (EpochLeases.tla). The controls must fail.
run_case "AuthorityReusedId"           "EpochLeases.tla" "AuthorityReusedId.cfg"           pass
run_case "AuthorityReusedIdEpochOnly"  "EpochLeases.tla" "AuthorityReusedIdEpochOnly.cfg"  invariant
run_case "AuthorityOutageLapse"        "EpochLeases.tla" "AuthorityOutageLapse.cfg"        pass liveness
run_case "AuthorityOutageNoLease"      "EpochLeases.tla" "AuthorityOutageNoLease.cfg"      liveness liveness
run_case "AuthorityNoWaitOut"          "EpochLeases.tla" "AuthorityNoWaitOut.cfg"          invariant
run_case "AuthorityDriftBeyondBound"   "EpochLeases.tla" "AuthorityDriftBeyondBound.cfg"   invariant
run_case "AuthorityNamedOnlyFence"     "EpochLeases.tla" "AuthorityNamedOnlyFence.cfg"     invariant
run_case "AuthorityLossPoint"          "EpochLeases.tla" "AuthorityLossPoint.cfg"          invariant

if [[ "$MODE" != "fast" ]]; then
  run_case "AuthorityRecovery"         "EpochLeases.tla" "AuthorityRecovery.cfg"           pass
  run_case "AuthorityOutageSafety"     "EpochLeases.tla" "AuthorityOutageSafety.cfg"       pass
  run_case "AuthorityRF5ExclusionControl" "EpochLeases.tla" "AuthorityRF5ExclusionControl.cfg" invariant

  run_case "AmnesiaWipe"               "LogkeeperProtocol.tla" "AmnesiaWipe.cfg"                 pass
  run_case "RepairReplaceSafety"       "LogkeeperProtocol.tla" "RepairReplaceSafety.cfg"         pass
  run_case "RecoveryBothReturn"        "LogkeeperProtocol.tla" "RecoveryBothReturn.cfg"          pass
  run_case "AbortedJointRestageSafety" "LogkeeperProtocol.tla" "AbortedJointRestageSafety.cfg"   pass
  run_case "CatalogSafety"             "CatalogStream.tla"     "CatalogSafety.cfg"               pass
fi

echo
echo "All TLA+ model checks matched expected outcomes."
