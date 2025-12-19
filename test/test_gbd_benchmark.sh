#!/usr/bin/env bash

set -euo pipefail

benchmark_hash="${1}"

# Work in a temporary directory.
work_dir=$(mktemp -d)
pushd "${work_dir}"

# Download.
wget --quiet -O formula.cnf.xz "https://benchmark-database.de/file/${benchmark_hash}"

# Decompress.
rm -f formula.cnf
xz --decompress formula.cnf.xz

# Solve.
status=0
cadical --quiet --unsat --binary=false formula.{cnf,drat} || status=$?
if [ "${status}" -ne "20" ]; then
    echo "solver did not return unsat"
    exit 1
fi

# Trim.
dsr-trim formula.{cnf,drat,lsr}

# Check.
lsr-check formula.{cnf,lsr}

# Clean.
popd
rm -rf "${work_dir}"
