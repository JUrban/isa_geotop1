#!/bin/bash
# Generate a searchable theorem statement index.
# Each entry: file:line KIND name :: statement_fragment
# Usage: cd /project/tst && bash gen_stmt_index.sh
# Then search: grep "keyword" STMT_INDEX.txt

BASE_THEORIES=(
  i/Top1_Ch2.thy i/Top1_Ch3.thy i/Top1_Ch4.thy i/Top1_Ch5_8.thy i/Top1_Ch9_13.thy
  h/AlgTopHelpers.thy b0/AlgTop_JCT_Base0.thy b/AlgTop_JCT_Base.thy
  a0/AlgTop0.thy ac/AlgTopCached.thy fib/AlgIsoFixedBase.thy fi/AlgIsoFixed.thy
  k5/K5_nonplanar.thy ag/AlgTopGroups.thy pd/PolygonDisk.thy svk/AlgTopSvK.thy
  wh/AlgTopWedgeHelpers.thy at/AlgTopChain.thy
  ac2/AlgTopCached2.thy ac3/AlgTopCached3.thy
  ac4/AlgTopCached4.thy ac5/AlgTopCached5.thy ac6/AlgTopCached6.thy
  ac7/AlgTopCached7.thy
  ac8/AlgTopCached8.thy algtop_session/AlgTop.thy
  gb0/GeoTopBase0.thy gb/GeoTopBase.thy gd/GeoTopDeps.thy gp/GeoTop_Prefix.thy GeoTop.thy
)

OUT=STMT_INDEX.txt

DEV34_SESSION_ROOT_HINTS=(
  dev34_pre/ROOT
  dev34_prefix_base/ROOT
  dev34_prefix_graph/ROOT
  dev34_prefix_mid/ROOT
  dev34_prefix/ROOT
  dev34_facts/ROOT
  dev34_workfacts/ROOT
  dev34_linkfacts/ROOT
  dev34_graphfacts/ROOT
  dev34_graphwork/ROOT
  dev34_openstar/ROOT
  dev34_core/ROOT
  dev34/ROOT
)

mapfile -t DEV34_SESSION_ROOTS < <(
  printf '%s\n' "${DEV34_SESSION_ROOT_HINTS[@]}"
  find . -path './dev34*/ROOT' -type f | sed 's#^\./##' | sort
)

mapfile -t DEV34_THEORIES < <(python3 - "${DEV34_SESSION_ROOTS[@]}" <<'PYEND'
import re
import sys
from pathlib import Path

seen = set()
seen_roots = set()

for root_arg in sys.argv[1:]:
    root = Path(root_arg)
    if not root.is_file():
        continue
    root_key = root.as_posix()
    if root_key in seen_roots:
        continue
    seen_roots.add(root_key)
    session_base = root.parent
    theory_dir = Path(".")
    in_theories = False
    for raw in root.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.split("(*", 1)[0].strip()
        if not line or line.startswith("#"):
            continue
        session_match = re.match(r'session\b.*?\bin\s+"([^"]+)"', line)
        if session_match:
            theory_dir = Path(session_match.group(1))
            in_theories = False
            continue
        if line.startswith("session "):
            theory_dir = Path(".")
            in_theories = False
            continue
        if re.match(r"theories\b", line):
            in_theories = True
            continue
        if in_theories:
            if re.match(r"(session|options|sessions|document_files|directories)\b", line):
                in_theories = False
                continue
            theory = line.split()[0].strip('"')
            if not theory:
                continue
            theory_path = session_base / theory_dir / (theory.replace(".", "/") + ".thy")
            theory_name = theory_path.as_posix()
            if theory_name not in seen:
                seen.add(theory_name)
                print(theory_name)
PYEND
)

THEORIES=("${BASE_THEORIES[@]}" "${DEV34_THEORIES[@]}")

> "$OUT"
for f in "${THEORIES[@]}"; do
  [ -f "$f" ] || continue
  python3 - "$f" >> "$OUT" << 'PYEND'
import re, sys
f = sys.argv[1]
lines = open(f).readlines()
i = 0
while i < len(lines):
    m = re.match(r'^(lemma|theorem|corollary|definition)\s+(\S+)', lines[i].strip())
    if m:
        kind, name = m.group(1), m.group(2).rstrip(':')
        # collect statement lines until proof/sorry/oops/by/where/begin
        stmt = []
        j = i
        while j < min(len(lines), i+25):
            l = lines[j].rstrip()
            stmt.append(l.strip())
            ls = l.strip()
            if any(ls.startswith(k) for k in ['proof','sorry','oops','by ','unfolding','using',
                    'lemma','theorem','corollary','definition','text','section','subsection','end']) and j > i:
                break
            j += 1
        # flatten to one line
        flat = ' '.join(stmt)
        # extract shows/assumes or definition body
        # For shows: grab everything after 'shows' up to proof/sorry/oops
        shows_pos = flat.find(' shows ')
        assumes_pos = flat.find(' assumes ')
        if shows_pos >= 0:
            shows_text = flat[shows_pos+7:]
            # Extract all quoted strings from the shows clause
            sig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', shows_text))
            if not sig:
                sig = shows_text[:600]
            if assumes_pos >= 0 and assumes_pos < shows_pos:
                assumes_text = flat[assumes_pos+9:shows_pos]
                asig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', assumes_text))
                if asig:
                    sig = asig[:300] + ' ==> ' + sig
        elif kind == 'definition':
            # For definitions, prefer the where "..." clause (the body)
            where_pos = flat.find(' where')
            if where_pos >= 0:
                where_text = flat[where_pos+6:]
                sig = ' '.join(m.group(1) for m in re.finditer(r'"([^"]*)"', where_text))
                if not sig:
                    sig = where_text[:600]
            else:
                type_m = re.search(r'::\s+"([^"]{1,200})', flat)
                sig = type_m.group(1) if type_m else flat[:300]
        else:
            # Fallback: grab all quoted strings
            quoted = [m.group(1) for m in re.finditer(r'"([^"]*)"', flat)]
            sig = ' '.join(quoted)[:600] if quoted else flat[:300]
        # Map Isabelle unicode escapes to readable ASCII
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
        def replace_sym(m):
            name = m.group(1)
            return sym_map.get(name, name)
        sig = re.sub(r'\\<(\w+)>', replace_sym, sig)
        sig = re.sub(r'\s+', ' ', sig).strip()
        if len(sig) > 800:
            sig = sig[:797] + '...'
        print(f'{f}:{i+1} {kind} {name} :: {sig}')
    i += 1
PYEND
done

total=$(wc -l < "$OUT")
echo "Statement index: $total entries -> $OUT"
