#!/usr/bin/env bash
#
# test_gbd_benchmarks.sh -- run benchmark.sh for every hash in a benchmark list
#
# Usage: test_gbd_benchmarks.sh [nprocs] [benchmark-list] 
#
# Defaults: `1 test/gbd/benchmarks.in`
#
# If a number less than or equal to '0' is given as the number of processors,
# `nproc` cores are used instead.
#

set -uo pipefail

NPROCS="${1:-1}"
LIST="${2:-$(dirname "$0")/benchmarks.in}"
LIST=$(readlink -f "${LIST}")

# Use the number of available CPUs, if '<= 0' cores are requested
if [ "${NPROCS}" -le 0 ]; then
    NPROCS=$(nproc)
fi

# Change to this script's directory
cd "$(dirname "$0")"

# Add the binary for `dsr-trim`, etc.
export PATH="$PWD/../../bin:$PATH"

# JOBS cannot exceed the number of available processors (via `nproc`)
if [ "${NPROCS}" -gt "$(nproc)" ]; then
    echo "Requested ${NPROCS} jobs, but only $(nproc) available." >&2
    exit 1
fi

# Test that `dsr-trim` and `lsr-check` are available.
if ! command -v dsr-trim >/dev/null 2>&1; then
    echo "dsr-trim not found on PATH" >&2
    echo "$PATH" >&2
    exit 1
fi

if ! command -v lsr-check >/dev/null 2>&1; then
    echo "lsr-check not found on PATH" >&2
    exit 1
fi

echo "Running benchmarks from '${LIST}' with ${NPROCS} core(s)."

# Worker n runs every n-th hash of the LIST, sequentially.
run_worker() {
    local worker="$1" hash status=0
    while read -r hash; do
        [ -n "${hash}" ] || continue
        if ./run_benchmark.sh "${hash}" > /dev/null 2>&1 ; then
            echo "PASS ${hash}"
        else
            echo "FAIL ${hash}"
            status=1
        fi
    done < <(awk -v w="${worker}" -v n="${NPROCS}" 'NF && (NR - 1) % n == w' "${LIST}")
    return "${status}"
}

# Kill child nodes if the parent gets killed
trap 'pkill -P $$' EXIT

status=0
pids=""
w=0
while [ "${w}" -lt "${NPROCS}" ]; do
    run_worker "${w}" &
    pids="${pids} $!"
    w=$((w + 1))
done

for pid in ${pids}; do
    wait "${pid}" || status=1
done

if [ "${status}" -ne 0 ]; then
    echo "Some benchmarks failed."
else
    echo "All benchmarks passed."
fi
exit "${status}"
