#!/usr/bin/env bash
set -euo pipefail

# Run all exhaustive TLA+ checks for Logkeeper's consensus protocol additions.
# Usage:
#   ./verification/tla/check.sh            # run all configs
#   ./verification/tla/check.sh fast       # skip the two ~1 min deep safety configs

ROOT="$(cd "$(dirname "$0")" && pwd)"
MODE="${1:-all}"

JAR="$("$ROOT/fetch-tla.sh")"

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

# expected: "pass" (exit 0), "invariant" (exit 12), or "liveness" (exit 13)
run_case() {
  local name="$1"
  local module="$2"
  local cfg="$3"
  local expected="$4"
  local extra="${5:-}"
  local log="$RESULTS/${name}.log"
  local meta
  meta="$(mktemp -d "${TMPDIR:-/tmp}/tlc-${name}.XXXXXX")"
  trap 'rm -rf "$meta"' RETURN

  local args=(-Xmx2g -XX:+UseParallelGC -jar "$JAR" -workers auto -deadlock -metadir "$meta")
  if [[ "$extra" == "liveness" ]]; then
    args+=(-lncheck final)
  fi
  args+=(-config "$ROOT/$cfg" "$ROOT/$module")

  set +e
  "$JAVA" "${args[@]}" > "$log" 2>&1
  local rc=$?
  set -e
  rm -rf "$meta"
  trap - RETURN

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
    invariant)
      if [[ $rc -ne 12 ]]; then
        echo "[FAIL] $name: expected invariant counterexample (exit 12), got exit=$rc (see $log)" >&2
        tail -n 20 "$log" >&2
        exit 1
      fi
      local inv
      inv="$(grep -E '^Error: Invariant ' "$log" | head -n 1 || true)"
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
}

echo "Using Java: $JAVA"
echo "Using TLC:  $JAR"
echo

# 1. Core safety & liveness checks (expected PASS)
run_case "RaftParkSafety"              "LogkeeperProtocol.tla" "RaftParkSafety.cfg"              pass
run_case "ParkedRepairLiveness"        "LogkeeperProtocol.tla" "ParkedRepairLiveness.cfg"        pass liveness
run_case "RecoverySingleReturnNoSnap"  "LogkeeperProtocol.tla" "RecoverySingleReturnNoSnap.cfg"  pass
run_case "RecoverySingleReturnLiveness" "LogkeeperProtocol.tla" "RecoverySingleReturnLiveness.cfg" pass liveness

if [[ "$MODE" != "fast" ]]; then
  run_case "RepairReplaceSafety"       "LogkeeperProtocol.tla" "RepairReplaceSafety.cfg"         pass
  run_case "CatalogSafety"             "CatalogStream.tla"     "CatalogSafety.cfg"               pass
fi

# 2. Counterexample checks (calibration + discovered bugs, expected CE)
run_case "AmnesiaWipe"                 "LogkeeperProtocol.tla" "AmnesiaWipe.cfg"                 invariant
run_case "AbortedReplaceLiveness"      "LogkeeperProtocol.tla" "AbortedReplaceLiveness.cfg"      liveness liveness
run_case "RecoverySingleReturnSnap"    "LogkeeperProtocol.tla" "RecoverySingleReturnSnap.cfg"    invariant
run_case "RecoveryBothReturnLiveness"  "LogkeeperProtocol.tla" "RecoveryBothReturnLiveness.cfg"  liveness liveness

if [[ "$MODE" != "fast" ]]; then
  run_case "RecoveryBothReturn"        "LogkeeperProtocol.tla" "RecoveryBothReturn.cfg"          invariant
fi

echo
echo "All TLA+ model checks matched expected outcomes."
