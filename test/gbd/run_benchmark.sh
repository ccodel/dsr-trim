#!/usr/bin/env bash
#
# test_gbd_benchmark.sh -- download one Global Benchmark Database instance,
# solve it with CaDiCaL to DRAT, trim it to LSR, and check the result.
#
# Requires network access plus `cadical`, `xz`, and `dsr-trim` / `lsr-check`
# on PATH.

set -euo pipefail

# Require a GBD hash as the first and only argument.
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <benchmark_hash>" >&2
    exit 1
fi

benchmark_hash="${1}"

# Add `dsr-trim` to the path, if it isn't present
if ! command -v dsr-trim >/dev/null 2>&1; then
    SCRIPT_DIR="$(dirname "$0")"
    SCRIPT_DIR="$(readlink -f "$SCRIPT_DIR")"
    export PATH="$SCRIPT_DIR/../../bin:$PATH"
fi

# Work in a temporary directory, removed on any exit.
work_dir=$(mktemp -d)
trap 'rm -rf "${work_dir}"' EXIT
cd "${work_dir}"

# Download and decompress.
curl --silent --show-error --fail --location \
    -o formula.cnf.xz "https://benchmark-database.de/file/${benchmark_hash}"
xz --decompress formula.cnf.xz

# Solve.
status=0
cadical --quiet --unsat --binary=false formula.cnf formula.drat > /dev/null 2>&1 || status=$?
if [ "${status}" -ne 20 ]; then
    echo "solver did not return unsat on ${benchmark_hash}" >&2
    exit 1
fi

# Runs its arguments and requires the output to be exactly `s VERIFIED UNSAT`.
expect_verified_unsat() {
    local output
    output=$("$@" 2>&1)
    if [ "${output}" != "s VERIFIED UNSAT" ]; then
        echo "$1 did not report \`s VERIFIED UNSAT\` on ${benchmark_hash}:" >&2
        echo "${output}" >&2
        exit 1
    fi
}

# Trim, then check.
expect_verified_unsat dsr-trim formula.{cnf,drat,lsr} -q
expect_verified_unsat lsr-check formula.{cnf,lsr} -q

echo "PASS ${benchmark_hash}"