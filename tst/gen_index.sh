#!/bin/bash
# Generate theorem/definition index from all active session theory files.
# Run from /project/tst after each session to keep the index current.
# Usage: cd /project/tst && bash gen_index.sh

set -e

BASE_THEORIES=(
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
)

TXT=THEOREMS_AND_DEFS.txt
MD=THEOREMS_AND_DEFS.md

mapfile -t SESSION_ROOTS < <(
  find . -name ROOT -type f \
    ! -path './.dev34_fast_cache/*' \
    | sed 's#^\./##' \
    | sort
)

mapfile -t ROOT_THEORIES < <(python3 - "${SESSION_ROOTS[@]}" <<'PYEND'
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

mapfile -t THEORIES < <(
  printf '%s\n' "${BASE_THEORIES[@]}" "${ROOT_THEORIES[@]}" | awk 'NF && !seen[$0]++'
)

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

print(f"Index: {len(entries)} entries, {len(duplicates)} duplicates -> {txt} / {md}")
PYEND
