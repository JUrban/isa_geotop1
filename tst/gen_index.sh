#!/bin/bash
# Generate theorem/definition index from active session theories and local imports.
# Cache invalidation covers ROOT/ROOTS files plus the generated theory list.
# Run from /project/tst after each session to keep the index current.
# Usage: cd /project/tst && bash gen_index.sh [--force]

set -euo pipefail

FORCE=0
if [ "${1:-}" = "--force" ]; then
  FORCE=1
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "Usage: bash gen_index.sh [--force]" >&2
  exit 2
fi

TXT=THEOREMS_AND_DEFS.txt
MD=THEOREMS_AND_DEFS.md
THEORY_LIST=INDEX_THEORIES.txt
CACHE_DIR=.index_cache
SIG_FILE="$CACHE_DIR/gen_index.sig"

mkdir -p "$CACHE_DIR"

mapfile -t THEORIES < <(python3 index_theory_lib.py --list --write-list "$THEORY_LIST")
mapfile -t MISSING < <(python3 index_theory_lib.py --missing)
mapfile -t ROOTS < <(python3 index_theory_lib.py --roots)
mapfile -t SESSION_FILES < <(python3 index_theory_lib.py --session-files)
SIG=$(python3 index_theory_lib.py --signature --extra gen_index.sh)

if [ "$FORCE" -eq 0 ] && [ -f "$SIG_FILE" ] && [ -f "$TXT" ] && [ -f "$MD" ] && [ -f "$THEORY_LIST" ] \
  && [ "$(cat "$SIG_FILE")" = "$SIG" ]; then
  echo "Index: fresh cache (${#THEORIES[@]} theories incl. imports, ${#SESSION_FILES[@]} session files, ${#ROOTS[@]} ROOT files) -> $TXT / $MD"
  echo "Theory list -> $THEORY_LIST"
  exit 0
fi

if [ "${#MISSING[@]}" -gt 0 ]; then
  printf 'Warning: %d indexed theories are missing files:\n' "${#MISSING[@]}" >&2
  printf '  %s\n' "${MISSING[@]}" >&2
fi

python3 - "$TXT" "$MD" "${THEORIES[@]}" <<'PYEND'
import datetime
import re
import sys
from collections import Counter
from pathlib import Path

txt = Path(sys.argv[1])
md = Path(sys.argv[2])
theories = sys.argv[3:]

decl_re = re.compile(
    r"^\s*(lemma|theorem|corollary|definition|fun|abbreviation)\s+([A-Za-z0-9_]*)"
)

entries = []
for theory in theories:
    path = Path(theory)
    if not path.is_file():
        continue
    with path.open(encoding="utf-8", errors="replace") as f:
        for line_no, line in enumerate(f, 1):
            match = decl_re.match(line)
            if not match:
                continue
            kind, name = match.groups()
            if name:
                entries.append((theory, kind, name, line_no))

# Match the old `sort -t'|' -k2,2 -k3,3` behavior, including the full-line
# final comparison for entries with the same kind and name.
entries.sort(key=lambda e: (e[1], e[2], f"{e[0]}|{e[1]}|{e[2]}|{e[3]}"))

with txt.open("w", encoding="utf-8") as out:
    for theory, kind, name, line_no in entries:
        out.write(f"{theory}|{kind}|{name}|{line_no}\n")

name_counts = Counter(name for _, _, name, _ in entries)
duplicates = sorted(name for name, count in name_counts.items() if count > 1)

with md.open("w", encoding="utf-8") as out:
    out.write("# Theorem and Definition Index\n")
    today = datetime.datetime.now(datetime.UTC)
    out.write(f"# Generated: {today:%Y-%m-%d}\n")
    out.write("# Format: file | kind | name | line\n")
    out.write("#\n")
    out.write(f"# Files: {','.join(theories)}\n")
    out.write("#\n")
    out.write(f"# Total entries: {len(entries)}\n")
    out.write(f"# Duplicate names: {len(duplicates)}\n")
    out.write("\n")

    for kind in ["definition", "fun", "abbreviation", "lemma", "theorem", "corollary"]:
        rows = [entry for entry in entries if entry[1] == kind]
        if not rows:
            continue
        out.write(f"## {kind}s ({len(rows)})\n")
        out.write("\n")
        for theory, _, name, line_no in rows:
            out.write(f"{name:<45}  {theory:<35}  line {line_no}\n")
        out.write("\n")

    if duplicates:
        out.write(f"## DUPLICATES ({len(duplicates)} names appear in multiple locations)\n")
        out.write("\n")
        for duplicate in duplicates:
            out.write(f"  {duplicate}:\n")
            for theory, kind, name, line_no in entries:
                if name == duplicate:
                    out.write(f"    {theory:<35}  {kind}  line {line_no}\n")
        out.write("\n")

print(f"Index: {len(entries)} entries, {len(duplicates)} duplicates from {len(theories)} theories incl. imports -> {txt} / {md}")
print("Theory list -> INDEX_THEORIES.txt")
PYEND

echo "Discovered ${#ROOTS[@]} ROOT files"
echo "Discovered ${#SESSION_FILES[@]} session files"

printf '%s\n' "$SIG" > "$SIG_FILE"
