#!/bin/sh

# Usage: ./gen.sh <start> <end>
# Generates PHP .cnf/.sr files in the range of the input.
# If `dsr-trim` exists in the parent directory, it will also generate .lsr files.
# The script must be run with `pwd` in the same directory as `gen.sh`.

if ! [ -f ./gen.sh ]; then
  echo "Error: Run this script in the same directory as gen.sh" >&2
  exit 1
fi

echo "Generating php files"

mkdir -p cnf
mkdir -p sr
for i in $(seq $1 $2); do
  ./php $i > cnf/php$i.cnf
  ./php-sr $i > sr/php$i.sr
done

# If sr-trim exists in the parent directory, run it on each file in cnf/

if [ -f ../dsr-trim ]; then
  echo "../dsr-trim detected, generating .lsr files"
  mkdir -p lsr
  for i in $(seq $1 $2); do
    ../dsr-trim cnf/php$i.cnf sr/php$i.sr lsr/php$i.lsr
  done
fi
