#!/bin/sh
# From the repository root, pass the release keeper and benchmark executables.
set -eu
keeper=${1:?usage: run.sh KEEPER STREAM-MEASURE [RTT_US ...]}
measure=${2:?usage: run.sh KEEPER STREAM-MEASURE [RTT_US ...]}
shift 2
if [ "$#" -eq 0 ]; then
    set -- 1000 2000
fi
"$measure" "$keeper" calibrate 0
for rtt do
    "$measure" "$keeper" calibrate "$rtt"
    "$measure" "$keeper" pool-check "$rtt"
    "$measure" "$keeper" scale-check "$rtt"
    for streams in 1 100 1000 10000; do
        for batch in 1 32; do
            if [ "$streams" -eq 10000 ] && [ "$batch" -eq 32 ]; then
                "$measure" "$keeper" commit "$rtt" "$streams" "$batch" 1 64
            else
                "$measure" "$keeper" commit "$rtt" "$streams" "$batch"
            fi
        done
    done
    "$measure" "$keeper" head "$rtt"
    "$measure" "$keeper" kill "$rtt"
    "$measure" "$keeper" partition "$rtt"
    "$measure" "$keeper" replace "$rtt"
    "$measure" "$keeper" hot "$rtt"
done
