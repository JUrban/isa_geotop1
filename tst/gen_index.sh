#!/bin/bash
# Generate theorem/definition index from all active theory files.
# Run from /project/tst after each session to keep the index current.
# Usage: cd /project/tst && bash gen_index.sh

set -e

THEORIES=(
  i/Top1_Ch2.thy
  i/Top1_Ch3.thy
  i/Top1_Ch4.thy
  i/Top1_Ch5_8.thy
  i/Top1_Ch9_13.thy
  h/AlgTopHelpers.thy
  b0/AlgTop_JCT_Base0.thy
  b/AlgTop_JCT_Base.thy
  a0/AlgTop0.thy
  ac/AlgTopCached.thy
  fib/AlgIsoFixedBase.thy
  fi/AlgIsoFixed.thy
  k5/K5_nonplanar.thy
  ag/AlgTopGroups.thy
  pd/PolygonDisk.thy
  svk/AlgTopSvK.thy
  wh/AlgTopWedgeHelpers.thy
  at/AlgTopChain.thy
  ac2/AlgTopCached2.thy
  ac3/AlgTopCached3.thy
  ac4/AlgTopCached4.thy
  ac5/AlgTopCached5.thy
  ac6/AlgTopCached6.thy
  ac7/AlgTopCached7.thy
  ac8/AlgTopCached8.thy
  algtop_session/AlgTop.thy
  gb0/GeoTopBase0.thy
  gb/GeoTopBase.thy
  gd/GeoTopDeps.thy
  gp/GeoTop_Prefix.thy
  GeoTop.thy
  dev34_prefix/GeoTop_3_4_Prefix.thy
  dev34/GeoTop_3_4.thy
)

TXT=THEOREMS_AND_DEFS.txt
MD=THEOREMS_AND_DEFS.md

# --- Generate machine-readable index ---
> "$TXT"
for f in "${THEORIES[@]}"; do
  [ -f "$f" ] || continue
  session=$(basename "$f" .thy)
  grep -nE '^\s*(lemma|theorem|corollary|definition|fun|abbreviation) ' "$f" | while IFS=: read -r line content; do
    content=$(echo "$content" | sed 's/^[[:space:]]*//')
    name=$(echo "$content" | sed 's/^\(lemma\|theorem\|corollary\|definition\|fun\|abbreviation\) \+\([a-zA-Z0-9_]*\).*/\2/')
    kind=$(echo "$content" | sed 's/^\([a-z]*\) .*/\1/')
    [ -n "$name" ] && echo "$f|$kind|$name|$line"
  done
done | sort -t'|' -k2,2 -k3,3 >> "$TXT"

total=$(wc -l < "$TXT")
ndups=$(awk -F'|' '{print $3}' "$TXT" | sort | uniq -d | wc -l)

# --- Generate human-readable index ---
{
  echo "# Theorem and Definition Index"
  echo "# Generated: $(date -u +%Y-%m-%d)"
  echo "# Format: file | kind | name | line"
  echo "#"
  echo "# Files: $(printf '%s\n' "${THEORIES[@]}" | tr '\n' ', ' | sed 's/,$//')"
  echo "#"
  echo "# Total entries: $total"
  echo "# Duplicate names: $ndups"
  echo ""

  for kind in definition fun abbreviation lemma theorem corollary; do
    count=$(grep "|${kind}|" "$TXT" | wc -l)
    [ "$count" -eq 0 ] && continue
    echo "## ${kind}s ($count)"
    echo ""
    grep "|${kind}|" "$TXT" | awk -F'|' '{printf "%-45s  %-35s  line %s\n", $3, $1, $4}'
    echo ""
  done

  if [ "$ndups" -gt 0 ]; then
    echo "## DUPLICATES ($ndups names appear in multiple locations)"
    echo ""
    awk -F'|' '{print $3}' "$TXT" | sort | uniq -d | while read -r dup; do
      echo "  $dup:"
      grep "|$dup|" "$TXT" | awk -F'|' '{printf "    %-35s  %s  line %s\n", $1, $2, $4}'
    done
    echo ""
  fi
} > "$MD"

echo "Index: $total entries, $ndups duplicates -> $TXT / $MD"
