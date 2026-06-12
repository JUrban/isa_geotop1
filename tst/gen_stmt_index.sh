#!/bin/bash
# Generate a searchable theorem statement index from active session theories and local imports.
# Cache invalidation covers ROOT/ROOTS files, the generated theory list,
# local advice/report notes. Transcript inputs (`*.cast(.gz)`, `isa*.jsonl`,
# `session*.jsonl`, transcript/conversation JSONL) are indexed only when
# GEOTOP_INDEX_SESSION_LOGS=1 is set, because they otherwise swamp searches.
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
SESSION_LOG_CACHE="$CACHE_DIR/gen_stmt_index.session_logs.txt"
SESSION_LOG_CACHE_SIG="$CACHE_DIR/gen_stmt_index.session_logs.sig"
META_DIR="$CACHE_DIR/gen_stmt_index.meta"

mkdir -p "$CACHE_DIR"

python3 index_theory_lib.py --metadata-dir "$META_DIR" --write-list "$THEORY_LIST" --extra gen_stmt_index.sh
mapfile -t THEORIES < "$META_DIR/theories"
mapfile -t MISSING < "$META_DIR/missing"
mapfile -t ROOTS < "$META_DIR/roots"
mapfile -t SESSION_FILES < "$META_DIR/session_files"
mapfile -t SIGNATURE_FILES < "$META_DIR/signature_files"
mapfile -t ADVICE_FILES < "$META_DIR/advice_files"
mapfile -t SESSION_LOG_FILES < "$META_DIR/session_log_files"
SIG=$(cat "$META_DIR/signature")
SESSION_LOG_SIG=$(cat "$META_DIR/session_log_signature")

if [ "$FORCE" -eq 0 ] && [ -f "$SIG_FILE" ] && [ -f "$OUT" ] && [ -f "$THEORY_LIST" ] \
  && [ "$(cat "$SIG_FILE")" = "$SIG" ]; then
  echo "Statement index: cache hit (${#THEORIES[@]} theories incl. imports, ${#SESSION_FILES[@]} session files, ${#SIGNATURE_FILES[@]} signature files, ${#ADVICE_FILES[@]} advice files, ${#SESSION_LOG_FILES[@]} session logs, ${#ROOTS[@]} ROOT files) -> $OUT"
  echo "Theory list -> $THEORY_LIST"
  exit 0
fi

if [ "${#MISSING[@]}" -gt 0 ]; then
  printf 'Warning: %d indexed theories are missing files:\n' "${#MISSING[@]}" >&2
  printf '  %s\n' "${MISSING[@]}" >&2
fi

SESSION_LOG_ARGS=(--session-logs "${SESSION_LOG_FILES[@]}")
SESSION_LOG_CACHE_ARGS=(--session-log-cache "$SESSION_LOG_CACHE")
SESSION_LOG_CACHE_STATUS=refreshed
if [ "${#SESSION_LOG_FILES[@]}" -eq 0 ]; then
  SESSION_LOG_ARGS=()
  SESSION_LOG_CACHE_ARGS=()
  SESSION_LOG_CACHE_STATUS=off
elif [ "$FORCE" -eq 0 ] && [ -f "$SESSION_LOG_CACHE" ] && [ -f "$SESSION_LOG_CACHE_SIG" ] \
  && [ "$(cat "$SESSION_LOG_CACHE_SIG")" = "$SESSION_LOG_SIG" ]; then
  SESSION_LOG_ARGS=()
  SESSION_LOG_CACHE_STATUS=hit
fi

python3 - "$OUT" --theories "${THEORIES[@]}" --advice "${ADVICE_FILES[@]}" \
  "${SESSION_LOG_ARGS[@]}" "${SESSION_LOG_CACHE_ARGS[@]}" << 'PYEND'
import gzip
import json
import re
import sys
from pathlib import Path

out_path = Path(sys.argv[1])
argv = sys.argv[2:]
markers = ["--theories", "--advice", "--session-logs", "--session-log-cache"]


def marker_values(marker: str) -> list[str]:
    if marker not in argv:
        return []
    start = argv.index(marker) + 1
    end = len(argv)
    for other in markers:
        if other == marker:
            continue
        try:
            pos = argv.index(other, start)
        except ValueError:
            continue
        end = min(end, pos)
    return argv[start:end]


theories = marker_values("--theories")
advice_files = marker_values("--advice")
session_log_files = marker_values("--session-logs")
session_log_cache_values = marker_values("--session-log-cache")
session_log_cache = (
    Path(session_log_cache_values[0]) if session_log_cache_values else None
)

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


out_lines = []

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
            out_lines.append(f'{f}:{i+1} {kind} {name} :: {sig}\n')
        i += 1

for f in advice_files:
    lines = Path(f).read_text(encoding="utf-8", errors="replace").splitlines()
    current_heading = "advice"
    pending: list[str] = []
    start_line = 1

    def emit_advice(parts: list[str], first_line: int) -> None:
        text = " ".join(part.strip() for part in parts if part.strip())
        text = re.sub(r"\s+", " ", text).strip()
        if not text:
            return
        if len(text) > 700:
            text = text[:697] + "..."
        out_lines.append(f"{f}:{first_line} advice {current_heading} :: {text}\n")

    for line_no, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith("#"):
            emit_advice(pending, start_line)
            pending = []
            current_heading = stripped.lstrip("#").strip() or "advice"
            start_line = line_no
            continue
        if not stripped:
            emit_advice(pending, start_line)
            pending = []
            start_line = line_no + 1
            continue
        if not pending:
            start_line = line_no
        pending.append(stripped)
    emit_advice(pending, start_line)


ANSI_RE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\)|[()][A-Za-z0-9]|[=>]|.)"
)
TRANSCRIPT_KEEP_RE = re.compile(
    r"(Try this|No proof|sorry|Sledgehammer|by100|check_dev34_fast|"
    r"geotop_|lemma |theorem |corollary |definition |Failed|Error|exception|"
    r"timeout|timing|holes?)",
    re.IGNORECASE,
)


def transcript_lines(path: Path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8", errors="replace") as handle:
        for line_no, raw in enumerate(handle, 1):
            try:
                event = json.loads(raw)
            except json.JSONDecodeError:
                payload = raw
            else:
                if isinstance(event, list) and len(event) >= 3:
                    payload = str(event[2])
                elif isinstance(event, dict):
                    parts: list[str] = []
                    for key in ("message", "text", "content", "output", "cmd", "command"):
                        value = event.get(key)
                        if isinstance(value, str):
                            parts.append(value)
                    message = event.get("message")
                    if isinstance(message, dict):
                        content = message.get("content")
                        if isinstance(content, str):
                            parts.append(content)
                        elif isinstance(content, list):
                            for item in content:
                                if isinstance(item, str):
                                    parts.append(item)
                                elif isinstance(item, dict):
                                    text = item.get("text")
                                    if isinstance(text, str):
                                        parts.append(text)
                    payload = " ".join(parts)
                    if not payload:
                        continue
                else:
                    continue
            line = ANSI_RE.sub("", payload)
            line = line.replace("\r", " ").replace("\n", " ")
            line = re.sub(r"\s+", " ", line).strip()
            if line:
                yield line_no, line


session_out_lines: list[str] = []

if session_log_files:
    for f in session_log_files:
        path = Path(f)
        emitted = 0
        for line_no, line in transcript_lines(path):
            if not TRANSCRIPT_KEEP_RE.search(line):
                continue
            text = line
            if len(text) > 700:
                text = text[:697] + "..."
            session_out_lines.append(f"{f}:{line_no} session transcript :: {text}\n")
            emitted += 1
            if emitted >= 200:
                session_out_lines.append(
                    f"{f}:{line_no} session transcript :: truncated after 200 matched transcript snippets\n"
                )
                break
    if session_log_cache is not None:
        content = "".join(session_out_lines)
        if (
            not session_log_cache.exists()
            or session_log_cache.read_text(encoding="utf-8", errors="replace") != content
        ):
            session_log_cache.write_text(content, encoding="utf-8")
elif session_log_cache is not None and session_log_cache.exists():
    session_out_lines = session_log_cache.read_text(
        encoding="utf-8", errors="replace"
    ).splitlines(True)

out_lines.extend(session_out_lines)

content = "".join(out_lines)
if not out_path.exists() or out_path.read_text(encoding="utf-8", errors="replace") != content:
    out_path.write_text(content, encoding="utf-8")
PYEND

total=$(wc -l < "$OUT")
theory_total=$(wc -l < "$THEORY_LIST")
echo "Statement index: $total entries from $theory_total theories incl. imports -> $OUT"
echo "Theory list -> $THEORY_LIST"
echo "Discovered ${#ROOTS[@]} ROOT files"
echo "Discovered ${#SESSION_FILES[@]} session files"
echo "Tracked ${#SIGNATURE_FILES[@]} session/signature files"
echo "Tracked ${#ADVICE_FILES[@]} advice files"
echo "Tracked ${#SESSION_LOG_FILES[@]} bounded session logs (${SESSION_LOG_CACHE_STATUS} snippets)"

printf '%s\n' "$SIG" > "$SIG_FILE"
printf '%s\n' "$SESSION_LOG_SIG" > "$SESSION_LOG_CACHE_SIG"
