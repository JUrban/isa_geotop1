#!/usr/bin/env python3
"""Shared helpers for the GeoTop generated search indexes."""

from __future__ import annotations

import argparse
import hashlib
import re
import shlex
import sys
from pathlib import Path


BASE_THEORIES = [
    "i/Top1_Ch2.thy",
    "i/Top1_Ch3.thy",
    "i/Top1_Ch4.thy",
    "i/Top1_Ch5_8.thy",
    "i/Top1_Ch9_13.thy",
    "h/AlgTopHelpers.thy",
    "b0/AlgTop_JCT_Base0.thy",
    "b/AlgTop_JCT_Base.thy",
    "a0/AlgTop0.thy",
    "ac/AlgTopCached.thy",
    "fib/AlgIsoFixedBase.thy",
    "fi/AlgIsoFixed.thy",
    "k5/K5_nonplanar.thy",
    "ag/AlgTopGroups.thy",
    "pd/PolygonDisk.thy",
    "svk/AlgTopSvK.thy",
    "wh/AlgTopWedgeHelpers.thy",
    "at/AlgTopChain.thy",
    "ac2/AlgTopCached2.thy",
    "ac3/AlgTopCached3.thy",
    "ac4/AlgTopCached4.thy",
    "ac5/AlgTopCached5.thy",
    "ac6/AlgTopCached6.thy",
    "ac7/AlgTopCached7.thy",
    "ac8/AlgTopCached8.thy",
    "algtop_session/AlgTop.thy",
    "gb0/GeoTopBase0.thy",
    "gb/GeoTopBase.thy",
    "gd/GeoTopDeps.thy",
    "gp/GeoTop_Prefix.thy",
    "GeoTop.thy",
]

CONTROL_RE = re.compile(r"(session|options|sessions|document_files|directories)\b")
SESSION_RE = re.compile(
    r'session\s+(?:"([^"]+)"|([^\s=]+))(?:\s+in\s+(?:"([^"]+)"|([^\s=]+)))?'
)
SESSION_FILE_NAMES = {"ROOT", "ROOTS"}
GENERATED_SESSION_FILE_NAMES = {"INDEX_THEORIES.txt"}
ADVICE_FILE_PATTERNS = [
    "PLAN_zero_sorry-expert*.md",
]


def theory_tokens(raw_line: str) -> list[str]:
    tokens = re.findall(r'"[^"]+"|\S+', raw_line)
    kept: list[str] = []
    bracket_depth = 0
    for token in tokens:
        if token.startswith("#"):
            break
        bracket_depth += token.count("[")
        if bracket_depth > 0:
            bracket_depth -= token.count("]")
            continue
        if any(part in token for part in "[]=+"):
            continue
        token = token.strip('"')
        if token:
            kept.append(token)
    return kept


def is_ignored_generated_path(base: Path, path: Path) -> bool:
    rel_parts = path.relative_to(base).parts
    return ".dev34_fast_cache" in rel_parts or path.name.endswith("~")


def is_indexed_session_file(base: Path, path: Path) -> bool:
    return path.name in SESSION_FILE_NAMES and not is_ignored_generated_path(base, path)


def is_generated_session_file(base: Path, path: Path) -> bool:
    return (
        path.name in GENERATED_SESSION_FILE_NAMES
        and not is_ignored_generated_path(base, path)
    )


def iter_generated_session_files(base: Path) -> list[Path]:
    session_files: list[Path] = []
    for name in sorted(GENERATED_SESSION_FILE_NAMES):
        session_files.extend(
            path
            for path in base.rglob(name)
            if path.is_file() and is_generated_session_file(base, path)
        )
    return sorted(session_files, key=lambda p: p.relative_to(base).as_posix())


def iter_signature_session_files(base: Path) -> list[Path]:
    return (
        iter_session_files(base) + iter_generated_session_files(base)
    )


def iter_advice_files(base: Path) -> list[Path]:
    advice_files: list[Path] = []
    for pattern in ADVICE_FILE_PATTERNS:
        advice_files.extend(
            path
            for path in base.glob(pattern)
            if path.is_file() and not is_ignored_generated_path(base, path)
        )
    return sorted(
        dict.fromkeys(advice_files),
        key=lambda p: p.relative_to(base).as_posix(),
    )


def iter_session_files(base: Path) -> list[Path]:
    session_files: list[Path] = []
    for name in sorted(SESSION_FILE_NAMES):
        session_files.extend(
            path
            for path in base.rglob(name)
            if path.is_file() and is_indexed_session_file(base, path)
        )
    session_files.extend(iter_roots_referenced_by_roots_files(base))
    return sorted(
        dict.fromkeys(session_files),
        key=lambda p: p.relative_to(base).as_posix(),
    )


def iter_session_roots(base: Path) -> list[Path]:
    return [path for path in iter_session_files(base) if path.name == "ROOT"]


def roots_file_entries(raw_line: str) -> list[str]:
    line = raw_line.split("#", 1)[0].strip()
    if not line:
        return []
    try:
        return shlex.split(line)
    except ValueError:
        return line.split()


def iter_roots_referenced_by_roots_files(base: Path) -> list[Path]:
    base_resolved = base.resolve()
    found: list[Path] = []
    seen_roots_files: set[Path] = set()

    def local_file(path: Path) -> Path | None:
        try:
            resolved = path.resolve()
            resolved.relative_to(base_resolved)
        except ValueError:
            return None
        return resolved if resolved.is_file() else None

    def visit_roots_file(roots_file: Path) -> None:
        roots_file = roots_file.resolve()
        if roots_file in seen_roots_files:
            return
        seen_roots_files.add(roots_file)
        for raw in roots_file.read_text(encoding="utf-8", errors="replace").splitlines():
            for entry in roots_file_entries(raw):
                target = (roots_file.parent / entry).resolve()
                if target.is_dir():
                    for candidate in (target / "ROOT", target / "ROOTS"):
                        local = local_file(candidate)
                        if local is None or is_ignored_generated_path(base_resolved, local):
                            continue
                        found.append(local)
                        if local.name == "ROOTS":
                            visit_roots_file(local)
                else:
                    local = local_file(target)
                    if local is None or is_ignored_generated_path(base_resolved, local):
                        continue
                    found.append(local)
                    if local.name == "ROOTS":
                        visit_roots_file(local)

    for roots_file in base.rglob("ROOTS"):
        local = local_file(roots_file)
        if local is not None and not is_ignored_generated_path(base_resolved, local):
            visit_roots_file(local)

    return found


def strip_isabelle_comment_prefix(line: str) -> str:
    return line.split("(*", 1)[0].strip()


def parse_root_theories(base: Path) -> tuple[list[str], list[str], dict[str, tuple[Path, Path]]]:
    root_theories: list[str] = []
    missing_root_theories: list[str] = []
    seen: set[str] = set()
    seen_roots: set[str] = set()
    session_dirs: dict[str, tuple[Path, Path]] = {}

    def emit(session_base: Path, theory_dir: Path, theory: str) -> None:
        theory_path = session_base / theory_dir / (theory.replace(".", "/") + ".thy")
        theory_name = theory_path.relative_to(base).as_posix()
        if theory_name not in seen:
            seen.add(theory_name)
            if theory_path.is_file():
                root_theories.append(theory_name)
            else:
                missing_root_theories.append(theory_name)

    for root in iter_session_roots(base):
        root_key = root.relative_to(base).as_posix()
        if root_key in seen_roots:
            continue
        seen_roots.add(root_key)
        session_base = root.parent
        theory_dir = Path(".")
        in_theories = False

        for raw in root.read_text(encoding="utf-8", errors="replace").splitlines():
            line = strip_isabelle_comment_prefix(raw)
            if not line or line.startswith("#"):
                continue
            session_match = SESSION_RE.match(line)
            if session_match:
                session_name = session_match.group(1) or session_match.group(2)
                session_dir_raw = session_match.group(3) or session_match.group(4)
                theory_dir = Path(session_dir_raw) if session_dir_raw else Path(".")
                session_dirs[session_name] = (session_base, theory_dir)
                in_theories = False
                continue
            if re.match(r"theories\b", line):
                in_theories = True
                rest = re.sub(r"^theories\b", "", line, count=1).strip()
                for theory in theory_tokens(rest):
                    emit(session_base, theory_dir, theory)
                continue
            if in_theories:
                if CONTROL_RE.match(line):
                    in_theories = False
                    continue
                for theory in theory_tokens(line):
                    emit(session_base, theory_dir, theory)

    return root_theories, missing_root_theories, session_dirs


def parse_theory_imports(path: Path) -> list[str]:
    imports: list[str] = []
    in_imports = False
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines()[:200]:
        line = strip_isabelle_comment_prefix(raw)
        if not line:
            continue
        if re.match(r"begin\b", line):
            break
        if re.match(r"imports\b", line):
            in_imports = True
            line = re.sub(r"^imports\b", "", line, count=1).strip()
        elif not in_imports:
            continue
        imports.extend(theory_tokens(line))
    return imports


def resolve_import(
    base: Path,
    current_theory: Path,
    session_dirs: dict[str, tuple[Path, Path]],
    theory: str,
) -> str | None:
    theory = theory.strip('"')
    if not theory:
        return None

    if theory.startswith("$"):
        return None

    if "." in theory:
        session, theory_name = theory.split(".", 1)
        if session in session_dirs:
            session_base, theory_dir = session_dirs[session]
            path = session_base / theory_dir / (theory_name.replace(".", "/") + ".thy")
            if path.is_file():
                return path.relative_to(base).as_posix()

    candidates: list[Path] = []
    if "/" in theory or theory.startswith("."):
        candidates.append((current_theory.parent / f"{theory}.thy").resolve())
        candidates.append((base / f"{theory}.thy").resolve())
    else:
        candidates.append(current_theory.parent / f"{theory}.thy")
        candidates.append(base / f"{theory}.thy")

    for path in candidates:
        try:
            rel = path.resolve().relative_to(base.resolve()).as_posix()
        except ValueError:
            continue
        if (base / rel).is_file():
            return rel
    return None


def close_local_imports(
    base: Path,
    theories: list[str],
    session_dirs: dict[str, tuple[Path, Path]],
) -> list[str]:
    ordered = list(theories)
    seen = set(ordered)
    i = 0
    while i < len(ordered):
        theory = ordered[i]
        i += 1
        path = base / theory
        if not path.is_file():
            continue
        for imported in parse_theory_imports(path):
            resolved = resolve_import(base, path, session_dirs, imported)
            if resolved and resolved not in seen:
                seen.add(resolved)
                ordered.append(resolved)
    return ordered


def discover_theories(base: Path) -> tuple[list[str], list[str]]:
    root_theories, missing_root_theories, session_dirs = parse_root_theories(base)

    ordered: list[str] = []
    for theory in BASE_THEORIES + root_theories:
        if theory not in ordered:
            ordered.append(theory)
    ordered = close_local_imports(base, ordered, session_dirs)

    existing: list[str] = []
    missing: list[str] = []
    for theory in ordered:
        if (base / theory).is_file():
            existing.append(theory)
        else:
            missing.append(theory)
    for theory in missing_root_theories:
        if theory not in missing:
            missing.append(theory)
    return existing, missing


def file_signature(base: Path, theories: list[str], extra_files: list[str]) -> str:
    h = hashlib.sha256()
    session_files = [
        path.relative_to(base).as_posix() for path in iter_signature_session_files(base)
    ]
    advice_files = [
        path.relative_to(base).as_posix() for path in iter_advice_files(base)
    ]
    for name in extra_files + session_files + advice_files + theories:
        path = base / name
        h.update(name.encode("utf-8"))
        if not path.exists():
            h.update(b"\0missing")
            continue
        st = path.stat()
        h.update(str(st.st_size).encode("ascii"))
        h.update(b":")
        h.update(str(st.st_mtime_ns).encode("ascii"))
        h.update(b"\n")
    return h.hexdigest()


def write_if_changed(path: Path, content: str) -> bool:
    if path.exists() and path.read_text(encoding="utf-8", errors="replace") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list", action="store_true", help="print existing theories")
    parser.add_argument("--missing", action="store_true", help="print missing theories")
    parser.add_argument("--roots", action="store_true", help="print discovered ROOT files")
    parser.add_argument(
        "--session-files",
        action="store_true",
        help="print discovered ROOT/ROOTS session files",
    )
    parser.add_argument(
        "--signature-files",
        action="store_true",
        help="print session/generated files included in the cache signature",
    )
    parser.add_argument(
        "--advice-files",
        action="store_true",
        help="print Markdown advice/report files included in the cache signature",
    )
    parser.add_argument("--signature", action="store_true", help="print input signature")
    parser.add_argument(
        "--write-list",
        metavar="PATH",
        help="write existing theories to PATH, preserving mtime if unchanged",
    )
    parser.add_argument(
        "--extra",
        action="append",
        default=[],
        help="extra file to include in the signature",
    )
    args = parser.parse_args()

    base = Path.cwd()
    theories, missing = discover_theories(base)
    roots = [path.relative_to(base).as_posix() for path in iter_session_roots(base)]
    session_files = [
        path.relative_to(base).as_posix() for path in iter_session_files(base)
    ]
    signature_files = [
        path.relative_to(base).as_posix() for path in iter_signature_session_files(base)
    ]
    advice_files = [
        path.relative_to(base).as_posix() for path in iter_advice_files(base)
    ]

    if args.write_list:
        content = "".join(f"{theory}\n" for theory in theories)
        write_if_changed(base / args.write_list, content)
    if args.list:
        sys.stdout.write("".join(f"{theory}\n" for theory in theories))
    if args.missing:
        sys.stdout.write("".join(f"{theory}\n" for theory in missing))
    if args.roots:
        sys.stdout.write("".join(f"{root}\n" for root in roots))
    if args.session_files:
        sys.stdout.write("".join(f"{path}\n" for path in session_files))
    if args.signature_files:
        sys.stdout.write("".join(f"{path}\n" for path in signature_files))
    if args.advice_files:
        sys.stdout.write("".join(f"{path}\n" for path in advice_files))
    if args.signature:
        extra = ["index_theory_lib.py"] + args.extra
        print(file_signature(base, theories, extra))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
