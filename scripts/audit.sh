#!/usr/bin/env bash
# Reproducible build + audit for ObserverEquivariance.
# Usage: scripts/audit.sh [logfile]     (default: BUILD_LOG_RAW.txt)
# Exit status is non-zero if the build fails, if any `#assert_standard_axioms` check fails,
# or if a forbidden construct occurs in Lean *code* (comments are stripped before the scan).
set -euo pipefail
cd "$(dirname "$0")/.."
LOG="${1:-BUILD_LOG_RAW.txt}"

{
  echo "== environment"
  date -u '+%Y-%m-%d %H:%M UTC'
  uname -sm
  echo "lean-toolchain: $(cat lean-toolchain)"
  lake env lean --version
  lake --version
  echo "mathlib rev: $(sed -n '/"rev"/{s/.*"rev": *"\([0-9a-f]*\)".*/\1/;h;};/"name": *"mathlib"/{x;p;q;}' lake-manifest.json)"
  echo
  echo "== lake build"
} > "$LOG"

set +e
lake build 2>&1 | tee -a "$LOG"
status=${PIPESTATUS[0]}
set -e
echo "lake build exit status: $status" | tee -a "$LOG"

echo "== forbidden-construct scan (comments stripped)" | tee -a "$LOG"
files=$(find ObserverEquivariance ObserverEquivariance.lean -name '*.lean' | sort)
# Strip /- ... -/ block comments (non-nested approximation is enough for this code base) and -- line comments.
hits=$(for f in $files; do
  perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" \
    | grep -nE '\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|\bunsafe\b|implemented_by' \
    | sed "s|^|$f:|"
done || true)
if [ -n "$hits" ]; then
  echo "$hits" | tee -a "$LOG"
  echo "FORBIDDEN CONSTRUCTS FOUND" | tee -a "$LOG"
  exit 1
fi
echo "none" | tee -a "$LOG"

# Count the audit lines of the build output before the summary copies them into the same log.
count=$({ grep -cE "depends? only on standard axioms" "$LOG" || true; })
echo "== axiom audit summary" | tee -a "$LOG"
{ grep -E "depends? only on standard axioms" "$LOG" || true; } | grep -vE "^== " | cut -c1-200 | tee -a "$LOG" >/dev/null
echo "passing #assert_standard_axioms lines: $count" | tee -a "$LOG"
if [ "$status" -eq 0 ] && ! grep -q "depend only on standard axioms" "$LOG"; then
  echo "MODULE-WIDE AXIOM AUDIT DID NOT RUN" | tee -a "$LOG"
  exit 1
fi
exit "$status"
