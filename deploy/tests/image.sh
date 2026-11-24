#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
fixture=$(mktemp -d "$root/target/keeper-image-test.XXXXXX")
image=logkeeper-image-test:${fixture##*.}
container=
cleanup() {
    if [[ -n $container ]]; then
        docker rm "$container" >/dev/null
    fi
    docker image rm "$image" >/dev/null 2>&1 || true
    rm -rf -- "$fixture"
}
trap cleanup EXIT

check_binary() {
    local arch=$1 binary=$2 machine info
    case "$arch" in
        arm64) machine='ARM aarch64' ;;
        amd64) machine='x86-64' ;;
    esac
    info=$(file -b "$binary")
    if [[ $info != *'statically linked'* && $info != *'static-pie linked'* ]]; then
        echo "Keeper executable must be statically linked: $info" >&2
        return 1
    fi
    if [[ $info != "ELF 64-bit LSB"*"$machine"* ]]; then
        echo "Keeper executable must match linux/$arch: $info" >&2
        return 1
    fi
}

expect_failure() {
    local check=$1
    shift
    if "$@" >"$fixture/control.log" 2>&1 || ! grep -qF "$check" "$fixture/control.log"; then
        echo "Expected failure at $check" >&2
        cat "$fixture/control.log" >&2
        return 1
    fi
    printf 'Control rejected at %s\n' "$check"
}

docker buildx build --platform linux/arm64,linux/amd64 --provenance=false --load \
    -f "$root/deploy/Dockerfile" -t "$image" "$root/target/keeper-image"

for arch in arm64 amd64; do
    platform=linux/$arch
    [[ $(docker image inspect --platform "$platform" --format '{{.Os}}/{{.Architecture}}' "$image") == "$platform" ]]
    container=$(docker create --platform "$platform" --pull never "$image")
    docker cp "$container:/usr/local/bin/logkeeper" "$fixture/$arch"
    docker rm "$container" >/dev/null
    container=
    check_binary "$arch" "$fixture/$arch"
    help=$(docker run --rm --network none --platform "$platform" --pull never \
        --entrypoint /usr/local/bin/logkeeper "$image" --help)
    grep -qF 'logkeeper keeper --config FILE' <<< "$help"
    printf '%s image contains a static keeper executable and runs it\n' "$platform"
done

expect_failure 'Keeper executable must match linux/arm64' check_binary arm64 "$fixture/amd64"
expect_failure 'Keeper executable must match linux/amd64' check_binary amd64 "$fixture/arm64"
printf '#!/bin/sh\n' > "$fixture/script"
expect_failure 'Keeper executable must be statically linked' check_binary arm64 "$fixture/script"
