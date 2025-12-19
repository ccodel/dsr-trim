#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"
parallel ./test_gbd_benchmark.sh :::: benchmarks.in
