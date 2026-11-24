#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
: "${GUARDED_CARGO:?Set GUARDED_CARGO to the path of the guarded Cargo executable}"

build_dir="$root/target/image-build"
"$GUARDED_CARGO" logkeeper build --locked --release --all-features --bin logkeeper \
    --target aarch64-unknown-linux-musl --target x86_64-unknown-linux-musl --target-dir "$build_dir"

mkdir -p target/keeper-image/{arm64,amd64}
install -m 0555 "$build_dir/aarch64-unknown-linux-musl/release/logkeeper" target/keeper-image/arm64/logkeeper
install -m 0555 "$build_dir/x86_64-unknown-linux-musl/release/logkeeper" target/keeper-image/amd64/logkeeper
