#!/bin/sh
# Runs the head-to-head matrix from the client host, alternating the two
# backends case by case. Start `head-to-head agent` on the three keeper hosts
# first (see HEAD-TO-HEAD.md).
#
#   head_to_head.sh HEAD-TO-HEAD-BIN TOKEN IP_A,IP_B,IP_C OUT.jsonl [CLIENT_ZONE [LOCAL_KEEPER]]
#
# CLIENT_ZONE is the consensus client's domain (default zone-a). LOCAL_KEEPER
# is the index of the keeper that shares the client's host, or of the keeper
# the consensus client's streams are led by (default 0); the kill case loses
# it and then another keeper.
set -u
bin=${1:?usage: head_to_head.sh BIN TOKEN KEEPERS OUT [CLIENT_ZONE [LOCAL_KEEPER]]}
token=${2:?}
keepers=${3:?}
out=${4:?}
zone=${5:-zone-a}
local=${6:-0}
other=$(( (local + 1) % 3 ))
common="--token $token --keepers $keepers --client-zone $zone"

run() {
    echo "== $*" >&2
    # shellcheck disable=SC2086
    if ! "$bin" run $common "$@" >> "$out"; then
        printf '{"failed": "%s"}\n' "$*" >> "$out"
    fi
}

# shellcheck disable=SC2086
"$bin" rtt $common >> "$out"
for streams in 1 32 1000; do
    for batch in 1 32; do
        for backend in writer consensus; do
            run --backend "$backend" commit "$streams" "$batch"
        done
    done
done
# Consensus batches through concurrent Journal::append as well, the
# writer-driven journal's native path.
run --backend consensus --batch-mode concurrent commit 32 32
for backend in writer consensus; do
    run --backend "$backend" head 32
done
for victim in "$local" "$other"; do
    for backend in writer consensus; do
        run --backend "$backend" kill 1000 "$victim"
    done
done
for backend in writer consensus; do
    run --backend "$backend" takeover 1000 32
done
run --backend writer repair 100
run --backend consensus --repair-after-secs 10 --park-after-secs 60 \
    --repair-limit-secs 1200 repair 100
run --backend writer repair 1000
