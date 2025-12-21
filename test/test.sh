#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
parallel --halt 'soon,fail=1' ./test_gbd_benchmark.sh :::: benchmarks.in
