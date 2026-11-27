#!/usr/bin/env bash
set -euo pipefail

# Download pinned TLA+ tools (TLC v1.7.4) into verification/tla/.tools/ and verify SHA-256.
ROOT="$(cd "$(dirname "$0")" && pwd)"
TOOLS_DIR="$ROOT/.tools"
JAR="$TOOLS_DIR/tla2tools.jar"
URL="https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar"
EXPECTED_SHA256="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"

mkdir -p "$TOOLS_DIR"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

if [[ ! -f "$JAR" ]]; then
  if [[ -n "${TLA2TOOLS_CACHE:-}" && -f "${TLA2TOOLS_CACHE}" ]]; then
    cp "$TLA2TOOLS_CACHE" "$JAR.tmp"
  elif [[ -f "$HOME/.local/share/tla/tla2tools.jar" ]] && [[ "$(sha256_file "$HOME/.local/share/tla/tla2tools.jar")" == "$EXPECTED_SHA256" ]]; then
    cp "$HOME/.local/share/tla/tla2tools.jar" "$JAR.tmp"
  else
    echo "Downloading tla2tools.jar (v1.7.4)..." >&2
    curl -fsSL --retry 3 "$URL" -o "$JAR.tmp"
  fi
  ACTUAL="$(sha256_file "$JAR.tmp")"
  if [[ "$ACTUAL" != "$EXPECTED_SHA256" ]]; then
    rm -f "$JAR.tmp"
    echo "SHA-256 mismatch for downloaded tla2tools.jar: got $ACTUAL, expected $EXPECTED_SHA256" >&2
    exit 1
  fi
  mv "$JAR.tmp" "$JAR"
fi

ACTUAL="$(sha256_file "$JAR")"
if [[ "$ACTUAL" != "$EXPECTED_SHA256" ]]; then
  echo "SHA-256 mismatch for $JAR: got $ACTUAL, expected $EXPECTED_SHA256" >&2
  exit 1
fi

echo "$JAR"
