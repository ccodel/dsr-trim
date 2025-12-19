#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
grep -Ev '^#' benchmarks.in | parallel --no-run-if-empty --halt 'soon,fail=1' ./test_gbd_benchmark.sh :::: -
