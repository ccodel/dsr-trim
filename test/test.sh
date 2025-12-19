#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
grep -Ev '^#' benchmarks.in | parallel --no-run-if-empty ./test_gbd_benchmark.sh :::: -
