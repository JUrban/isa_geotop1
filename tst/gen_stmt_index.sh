#!/bin/bash
# Generate a searchable theorem statement index from active session theories and local imports.
# Cache invalidation covers ROOT/ROOTS files plus the generated theory list.
# Each entry: file:line KIND name :: statement_fragment
# Usage: cd /project/tst && bash gen_stmt_index.sh [--force]
# Then search: grep "keyword" STMT_INDEX.txt

set -euo pipefail

FORCE=0
if [ "${1:-}" = "--force" ]; then
  FORCE=1
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "Usage: bash gen_stmt_index.sh [--force]" >&2
  exit 2
fi

OUT=STMT_INDEX.txt
THEORY_LIST=INDEX_THEORIES.txt
CACHE_DIR=.index_cache
SIG_FILE="$CACHE_DIR/gen_stmt_index.sig"

mkdir -p "$CACHE_DIR"

mapfile -t THEORIES < <(python3 index_theory_lib.py --list --write-list "$THEORY_LIST")
mapfile -t MISSING < <(python3 index_theory_lib.py --missing)
mapfile -t ROOTS < <(python3 index_theory_lib.py --roots)
mapfile -t SESSION_FILES < <(python3 index_theory_lib.py --session-files)
mapfile -t SIGNATURE_FILES < <(python3 index_theory_lib.py --signature-files)
SIG=$(python3 index_theory_lib.py --signature --extra gen_stmt_index.sh)

if [ "$FORCE" -eq 0 ] && [ -f "$SIG_FILE" ] && [ -f "$OUT" ] && [ -f "$THEORY_LIST" ] \
  && [ "$(cat "$SIG_FILE")" = "$SIG" ]; then
  echo "Statement index: fresh cache (${#THEORIES[@]} theories incl. imports, ${#SESSION_FILES[@]} session files, ${#SIGNATURE_FILES[@]} signature files, ${#ROOTS[@]} ROOT files) -> $OUT"
  echo "Theory list -> $THEORY_LIST"
  exit 0
fi

if [ "${#MISSING[@]}" -gt 0 ]; then
  printf 'Warning: %d indexed theories are missing files:\n' "${#MISSING[@]}" >&2
  printf '  %s\n' "${MISSING[@]}" >&2
fi

python3 - "$OUT" "${THEORIES[@]}" << 'PYEND'
import re
import sys
from pathlib import Path

out_path = Path(sys.argv[1])
theories = sys.argv[2:]

sym_map = {
    'forall': 'ALL ', 'exists': 'EX ', 'nexists': '~EX ',
    'in': ' : ', 'notin': ' ~: ', 'subseteq': ' <= ',
    'subset': ' < ', 'supseteq': ' >= ',
    'union': ' Un ', 'inter': ' Int ', 'Union': 'UN', 'Inter': 'IN',
    'Rightarrow': ' => ', 'Longrightarrow': ' ==> ',
    'longrightarrow': ' --> ', 'longleftrightarrow': ' <-> ',
    'and': ' & ', 'or': ' | ', 'not': '~',
    'lambda': '%', 'Lambda': '%',
    'equiv': ' == ', 'noteq': ' ~= ',
    'le': ' <= ', 'ge': ' >= ', 'times': ' * ',
    'circ': ' o ', 'lbrakk': '[', 'rbrakk': ']',
    'open': '', 'close': '',
    'pi': 'pi', 'sigma': 'sigma', 'tau': 'tau',
    'alpha': 'a', 'beta': 'b', 'gamma': 'g',
    'iota': 'iota', 'phi': 'phi', 'Phi': 'Phi', 'Psi': 'Psi',
}


def replace_sym(match):
    name = match.group(1)
    return sym_map.get(name, name)


def signature_fragment(kind, flat):
    shows_pos = flat.find(' shows ')
    assumes_pos = flat.find(' assumes ')
    if shows_pos >= 0:
        shows_text = flat[shows_pos + 7:]
        sig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', shows_text))
        if not sig:
            sig = shows_text[:600]
        if assumes_pos >= 0 and assumes_pos < shows_pos:
            assumes_text = flat[assumes_pos + 9:shows_pos]
            asig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', assumes_text))
            if asig:
                sig = asig[:300] + ' ==> ' + sig
    elif kind == 'definition':
        where_pos = flat.find(' where')
        if where_pos >= 0:
            where_text = flat[where_pos + 6:]
            sig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', where_text))
            if not sig:
                sig = where_text[:600]
        else:
            type_m = re.search(r'::\s+"([^"]{1,200})', flat)
            sig = type_m.group(1) if type_m else flat[:300]
    else:
        quoted = [m.group(1) for m in re.finditer(r'"([^"]*)"', flat)]
        sig = ' '.join(quoted)[:600] if quoted else flat[:300]
    sig = re.sub(r'\\<(\w+)>', replace_sym, sig)
    sig = re.sub(r'\s+', ' ', sig).strip()
    if len(sig) > 800:
        sig = sig[:797] + '...'
    return sig


with out_path.open("w", encoding="utf-8") as out:
    for f in theories:
        lines = open(f, encoding="utf-8", errors="replace").readlines()
        i = 0
        while i < len(lines):
            m = re.match(r'^(lemma|theorem|corollary|definition|fun|abbreviation)\s+(\S+)', lines[i].strip())
            if m:
                kind, name = m.group(1), m.group(2).rstrip(':')
                stmt = []
                j = i
                while j < min(len(lines), i + 25):
                    line = lines[j].rstrip()
                    stmt.append(line.strip())
                    stripped = line.strip()
                    stops = ['proof', 'sorry', 'oops', 'by ', 'unfolding', 'using',
                             'lemma', 'theorem', 'corollary', 'definition', 'fun',
                             'abbreviation', 'text', 'section', 'subsection', 'end']
                    if any(stripped.startswith(k) for k in stops) and j > i:
                        break
                    j += 1
                flat = ' '.join(stmt)
                sig = signature_fragment(kind, flat)
                out.write(f'{f}:{i+1} {kind} {name} :: {sig}\n')
            i += 1
PYEND

total=$(wc -l < "$OUT")
theory_total=$(wc -l < "$THEORY_LIST")
echo "Statement index: $total entries from $theory_total theories incl. imports -> $OUT"
echo "Theory list -> $THEORY_LIST"
echo "Discovered ${#ROOTS[@]} ROOT files"
echo "Discovered ${#SESSION_FILES[@]} session files"
echo "Tracked ${#SIGNATURE_FILES[@]} session/signature files"

printf '%s\n' "$SIG" > "$SIG_FILE"
