#!/usr/bin/env bash
# Validate every .parquet file under the given directory (non‑recursive).
# Usage: ./run-all.sh /path/to/dir [validator_exe]

DIR="${1:-.}"
VALIDATOR="${2:-}"

status=0
shopt -s nullglob
for file in "$DIR"/*.parquet; do
  "$VALIDATOR" "$file" || status=1
done
exit $status
