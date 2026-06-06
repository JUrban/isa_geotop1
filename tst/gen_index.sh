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
  dev34_prefix_base/GeoTop_3_4_Prefix_Base.thy
  dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
  dev34_prefix/GeoTop_3_4_Prefix.thy
  dev34_facts/GeoTop_3_4_Facts.thy
  dev34_workfacts/GeoTop_3_4_WorkFacts.thy
  dev34_linkfacts/GeoTop_3_4_LinkFacts.thy
  dev34_graphfacts/GeoTop_3_4_GraphFacts.thy
  dev34_graphwork/GeoTop_3_4_GraphWork.thy
  dev34_openstar/GeoTop_3_4_OpenStar.thy
  dev34_core/GeoTop_3_4_Core.thy
  dev34/GeoTop_3_4.thy
)

TXT=THEOREMS_AND_DEFS.txt
MD=THEOREMS_AND_DEFS.md

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
