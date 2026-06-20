#!/usr/bin/env bash
# tooling/audit.sh — the honesty auditor (the Lean analog of "never fudge the oracle").
#
# Comment-aware: strips Lean comments (`/- … -/`, `/-! … -/`, `-- …`) before scanning for the
# keywords `sorry` and `axiom`, so the words may appear freely in prose without false alarms.
# Fails (non-zero exit) if any of:
#   [1] a non-Skeleton .lean file contains a real `sorry`
#   [2] a real `axiom` is declared anywhere
#   [3] a keystone's `#print axioms` output mentions `sorryAx`
# Skeleton.lean files and _TEMPLATE-concept/ are exempt by design.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
PRUNE=( '(' -path ./.lake -o -path ./_TEMPLATE-concept ')' -prune -o )
fail=0

# Remove block comments (non-nested) then line comments.
strip() { perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$1" 2>/dev/null; }

echo "→ [1/3] stray 'sorry' outside Skeleton.lean (comments ignored)…"
hits=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  strip "$f" | grep -qw 'sorry' && hits="$hits  $f"$'\n'
done < <(find . "${PRUNE[@]}" -name '*.lean' ! -name 'Skeleton.lean' -print)
if [ -n "$hits" ]; then printf "  ✗ found 'sorry' in:\n%s" "$hits"; fail=1; else echo "  ✓ none"; fi

echo "→ [2/3] ad-hoc 'axiom' declarations (comments ignored)…"
hits=""
while IFS= read -r f; do
  [ -n "$f" ] || continue
  strip "$f" | grep -qE '^[[:space:]]*axiom[[:space:]]' && hits="$hits  $f"$'\n'
done < <(find . "${PRUNE[@]}" -name '*.lean' -print)
if [ -n "$hits" ]; then printf "  ✗ found 'axiom' in:\n%s" "$hits"; fail=1; else echo "  ✓ none"; fi

echo "→ [3/3] #print axioms of keystones free of sorryAx…"
keyfiles=$(find . "${PRUNE[@]}" -name '*.lean' ! -name 'Skeleton.lean' -exec grep -lE '#print[[:space:]]+axioms' {} + 2>/dev/null)
if [ -z "$keyfiles" ]; then echo "  (no keystones with #print axioms yet)"; else
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    out=$(lake env lean "$f" 2>&1)
    if echo "$out" | grep -q 'sorryAx'; then echo "  ✗ $f → sorryAx in axiom footprint"; fail=1;
    else echo "  ✓ $f"; fi
  done <<< "$keyfiles"
fi

if [ "$fail" -eq 0 ]; then echo "✓ honesty audit clean"; else echo "✗ honesty audit FAILED"; fi
exit "$fail"
