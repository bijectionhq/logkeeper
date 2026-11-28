#!/bin/sh
# Runs the signed-history head-to-head matrix from the client host: the
# writer-driven journal with and without authenticated (signed) history on the
# same build, alternating case by case, REPEATS times, then the two consensus
# commit cases. Start `head-to-head agent` on the three keeper hosts first
# (see HEAD-TO-HEAD.md and HEAD-TO-HEAD-AUTH.md).
#
#   head_to_head_auth.sh BIN TOKEN IP_A,IP_B,IP_C OUT.jsonl [CLIENT_ZONE [LOCAL_KEEPER [REPEATS [CONSENSUS]]]]
set -u
bin=${1:?usage: head_to_head_auth.sh BIN TOKEN KEEPERS OUT [CLIENT_ZONE [LOCAL_KEEPER [REPEATS [CONSENSUS]]]]}
token=${2:?}
keepers=${3:?}
out=${4:?}
zone=${5:-zone-a}
local=${6:-0}
repeats=${7:-3}
consensus=${8:-1}
common="--token $token --keepers $keepers --client-zone $zone"

run() {
    echo "== $(date +%H:%M:%S) $*" >&2
    # shellcheck disable=SC2086
    if ! "$bin" run $common "$@" >> "$out"; then
        printf '{"failed": "%s"}\n' "$*" >> "$out"
    fi
}

# shellcheck disable=SC2086
"$bin" rtt $common >> "$out"
rep=1
while [ "$rep" -le "$repeats" ]; do
    # Alternate which variant goes first in each repeat.
    if [ $((rep % 2)) -eq 1 ]; then order="0 1"; else order="1 0"; fi
    for case in "commit 32 32" "commit 1000 1" "commit 1000 32" "head 32" \
        "kill 1000 $local" "repair 100"; do
        for auth in $order; do
            extra=""
            [ "${case%% *}" = repair ] && extra="--repair-trim 1"
            # shellcheck disable=SC2086
            run --backend writer --authenticated "$auth" $extra $case
        done
    done
    rep=$((rep + 1))
done
# The untrimmed repair of the earlier run, once per variant.
for auth in 0 1; do
    run --backend writer --authenticated "$auth" repair 100
done
if [ "$consensus" = 1 ]; then
    run --backend consensus commit 32 32
    run --backend consensus commit 1000 32
fi
