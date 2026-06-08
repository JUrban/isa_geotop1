#!/bin/bash
# Generate theorem/definition index from active session theories and local imports.
# Cache invalidation covers ROOT/ROOTS files, the generated theory list,
# local advice/report notes, and bounded session transcript inputs.
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
mapfile -t SIGNATURE_FILES < <(python3 index_theory_lib.py --signature-files)
mapfile -t ADVICE_FILES < <(python3 index_theory_lib.py --advice-files)
mapfile -t SESSION_LOG_FILES < <(python3 index_theory_lib.py --session-log-files)
SIG=$(python3 index_theory_lib.py --signature --extra gen_index.sh)

if [ "$FORCE" -eq 0 ] && [ -f "$SIG_FILE" ] && [ -f "$TXT" ] && [ -f "$MD" ] && [ -f "$THEORY_LIST" ] \
  && [ "$(cat "$SIG_FILE")" = "$SIG" ]; then
  echo "Index: fresh cache (${#THEORIES[@]} theories incl. imports, ${#SESSION_FILES[@]} session files, ${#SIGNATURE_FILES[@]} signature files, ${#ADVICE_FILES[@]} advice files, ${#SESSION_LOG_FILES[@]} session logs, ${#ROOTS[@]} ROOT files) -> $TXT / $MD"
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

def write_if_changed(path, content):
    if path.exists() and path.read_text(encoding="utf-8", errors="replace") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True

txt_lines = [
    f"{theory}|{kind}|{name}|{line_no}\n"
    for theory, kind, name, line_no in entries
]
write_if_changed(txt, "".join(txt_lines))

name_counts = Counter(name for _, _, name, _ in entries)
duplicates = sorted(name for name, count in name_counts.items() if count > 1)

md_lines = []

def emit(line=""):
    md_lines.append(f"{line}\n")

emit("# Theorem and Definition Index")
today = datetime.datetime.now(datetime.UTC)
emit(f"# Generated: {today:%Y-%m-%d}")
emit("# Format: file | kind | name | line")
emit("#")
emit(f"# Files: {','.join(theories)}")
emit("#")
emit(f"# Total entries: {len(entries)}")
emit(f"# Duplicate names: {len(duplicates)}")
emit()

for kind in ["definition", "fun", "abbreviation", "lemma", "theorem", "corollary"]:
    rows = [entry for entry in entries if entry[1] == kind]
    if not rows:
        continue
    emit(f"## {kind}s ({len(rows)})")
    emit()
    for theory, _, name, line_no in rows:
        emit(f"{name:<45}  {theory:<35}  line {line_no}")
    emit()

if duplicates:
    emit(f"## DUPLICATES ({len(duplicates)} names appear in multiple locations)")
    emit()
    for duplicate in duplicates:
        emit(f"  {duplicate}:")
        for theory, kind, name, line_no in entries:
            if name == duplicate:
                emit(f"    {theory:<35}  {kind}  line {line_no}")
    emit()

write_if_changed(md, "".join(md_lines))

print(f"Index: {len(entries)} entries, {len(duplicates)} duplicates from {len(theories)} theories incl. imports -> {txt} / {md}")
print("Theory list -> INDEX_THEORIES.txt")
PYEND

echo "Discovered ${#ROOTS[@]} ROOT files"
echo "Discovered ${#SESSION_FILES[@]} session files"
echo "Tracked ${#SIGNATURE_FILES[@]} session/signature files"
echo "Tracked ${#ADVICE_FILES[@]} advice files"
echo "Tracked ${#SESSION_LOG_FILES[@]} bounded session logs"

printf '%s\n' "$SIG" > "$SIG_FILE"
