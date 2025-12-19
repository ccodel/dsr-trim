#!/usr/bin/env bash

set -euo pipefail

benchmark_hash="${1}"

# Work in a temporary directory.
pushd $(mktemp -d)

# Download.
wget "https://benchmark-database.de/file/${benchmark_hash}" -O formula.cnf.xz

# Decompress.
rm -f formula.cnf
xz --decompress formula.cnf.xz

# Solve.
status=0
cadical --unsat --binary=false formula.{cnf,drat} || status=$?
if [ "${status}" -ne "20" ]; then
    echo "solver did not return unsat"
    exit 1
fi

# Trim.
dsr-trim formula.{cnf,drat,lsr}

# Check.
lsr-check formula.{cnf,lsr}
