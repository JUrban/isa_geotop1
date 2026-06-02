#!/usr/bin/env bash
# Export GeoTop-chain theorem/lemma facts as TFF ATP problems using the named
# theorem dependencies recorded in Isabelle proof terms.
#
# Usage:
#   cd /project/tst
#   tptp_exp/export_geotop_used_tff.sh [OUT_DIR]
#
# Environment:
#   GEOTOP_USED_TPTP_LIMIT  optional target limit for quick probes, default 0 = all
#   GEOTOP_USED_TPTP_SCOPE  geotop or all_geotop, default all_geotop

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT_DIR="${1:-$PROJECT_DIR/tptp_probs_geotop_used}"
LIMIT="${GEOTOP_USED_TPTP_LIMIT:-0}"
SCOPE="${GEOTOP_USED_TPTP_SCOPE:-all_geotop}"

mkdir -p "$OUT_DIR"
OUT_DIR="$(cd "$OUT_DIR" && pwd)"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geotop_used_tff_export.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

SOURCE_DECLS="$(
python3 - "$PROJECT_DIR" "$SCOPE" <<'PY'
import re
import sys
from pathlib import Path

project = Path(sys.argv[1])
scope = sys.argv[2]

theories = {
    "geotop": [
        ("GeoTop", "GeoTop.thy", "CHUNK_OUT_3PLUS_START"),
    ],
    "all_geotop": [
        ("GeoTopBase0", "gb0/GeoTopBase0.thy", None),
        ("GeoTopBase", "gb/GeoTopBase.thy", None),
        ("GeoTopDeps", "gd/GeoTopDeps.thy", None),
        ("GeoTop_Prefix", "gp/GeoTop_Prefix.thy", None),
        ("GeoTop", "GeoTop.thy", "CHUNK_OUT_3PLUS_START"),
    ],
}

if scope not in theories:
    raise SystemExit(f"Unknown GEOTOP_USED_TPTP_SCOPE={scope!r}; expected geotop or all_geotop")

for theory, rel, stop_marker in theories[scope]:
    for line in (project / rel).read_text(encoding="utf-8").splitlines():
        if stop_marker and stop_marker in line:
            break
        match = re.match(r"\s*(lemma|theorem|corollary)\s+([A-Za-z0-9_]+)", line)
        if match:
            print(f'    ("{theory}", "{match.group(2)}"),')
PY
)"

cat > "$TMP_DIR/GeoTop_Used_TFF_Export.thy" <<EOF
theory GeoTop_Used_TFF_Export
  imports "GeoTop.GeoTop"
begin

ML \<open>
let
  val export_dir = Path.explode "$OUT_DIR"
  val manifest = export_dir + Path.basic "manifest.tsv"
  val failures = export_dir + Path.basic "failures.tsv"
  val missing_deps_file = export_dir + Path.basic "missing_deps.tsv"
  val oracles_file = export_dir + Path.basic "oracles.tsv"
  val limit = $LIMIT
  val source_decls = [
$SOURCE_DECLS
    ("__end_marker__", "__end_marker__")
  ]
  val source_decls = filter_out (fn decl => decl = ("__end_marker__", "__end_marker__")) source_decls

  val _ = Isabelle_System.make_directory export_dir
  val _ =
    File.write manifest
      "file\\ttheorem\\tproof_deps\\tresolved_deps\\tmissing_deps\\toracles\\thas_skip_proof\\n"
  val _ = File.write failures "theorem\\terror\\n"
  val _ = File.write missing_deps_file "theorem\\tdependency\\n"
  val _ = File.write oracles_file "theorem\\toracle\\n"

  val ctxt = @{context}
  val thy = @{theory GeoTop}
  val format = ATP_Problem.TFF (ATP_Problem.Monomorphic, ATP_Problem.Without_FOOL)
  val type_enc =
    ATP_Problem_Generate.type_enc_of_string ATP_Problem_Generate.Strict "mono_native"
  val lam_trans = ATP_Problem_Generate.liftingN

  fun clean_name s =
    s
    |> String.map (fn c =>
      if Char.isAlphaNum c orelse c = #"_" then c else #"_")

  fun manifest_field s =
    String.map (fn c =>
      if c = #"\\t" orelse c = #"\\n" orelse c = #"\\r" then #" " else c) s

  fun first_line s =
    (case String.tokens (fn c => c = #"\\n" orelse c = #"\\r") s of
      line :: _ => line
    | [] => s)

  fun compact_message s =
    let
      val plain =
        first_line s
        |> String.map (fn c => if Char.ord c < 32 then #" " else c)
    in
      if size plain > 160 then String.substring (plain, 0, 160) ^ " ..." else plain
    end

  fun thm_message msg =
    if String.isPrefix "infer_instantiate_types" msg then
      "THM: infer_instantiate_types"
    else
      "THM: " ^ compact_message msg

  fun is_generated_timestamp_line s =
    let
      fun is_digit_at i = i < size s andalso Char.isDigit (String.sub (s, i))
      fun char_at i c = i < size s andalso String.sub (s, i) = c
    in
      size s >= 23 andalso
      List.all is_digit_at [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18] andalso
      char_at 4 #"-" andalso char_at 7 #"-" andalso char_at 10 #" " andalso
      char_at 13 #":" andalso char_at 16 #":" andalso char_at 19 #"."
    end

  fun strip_numeric_suffix s =
    (case rev (space_explode "_" s) of
      last :: rev_prefix =>
        if is_some (Int.fromString last) andalso not (null rev_prefix) then
          space_implode "_" (rev rev_prefix)
        else
          s
    | [] => s)

  fun split_theory_name short_name =
    (case first_field "." short_name of
      SOME pair => pair
    | NONE => ("", short_name))

  fun is_source_fact name =
    let
      val (theory_name, base) = split_theory_name (Thm_Name.short name)
      val stripped = strip_numeric_suffix base
    in
      member (op =) source_decls (theory_name, base) orelse
      member (op =) source_decls (theory_name, stripped)
    end

  val all_theorems = Global_Theory.all_thms_of thy true
  val thm_table = Thm_Name.Table.build (all_theorems |> fold_rev Thm_Name.Table.update)

  val raw_targets = all_theorems |> filter (is_source_fact o fst)
  val targets = if limit > 0 then take limit raw_targets else raw_targets

  fun lookup_dep dep_name =
    (case Thm_Name.Table.lookup thm_table dep_name of
      SOME dep_th => SOME (dep_name, dep_th)
    | NONE => NONE)

  fun is_missing_dep dep_name = is_none (Thm_Name.Table.lookup thm_table dep_name)

  fun oracle_label ((oracle_name, _), _) =
    Pretty.string_of (Thm.pretty_oracle ctxt oracle_name)

  fun append_missing target_name dep_name =
    File.append missing_deps_file
      (manifest_field target_name ^ "\\t" ^ manifest_field (Thm_Name.short dep_name) ^ "\\n")

  fun append_oracle target_name oracle =
    File.append oracles_file
      (manifest_field target_name ^ "\\t" ^ manifest_field (oracle_label oracle) ^ "\\n")

  fun append_failure target_name message =
    File.append failures
      (manifest_field target_name ^ "\\t" ^ manifest_field (compact_message message) ^ "\\n")

  fun export_one (name, th) =
    let
      val target_name = Thm_Name.short name
      val hyp_ts = []
      val concl_t = Thm.prop_of th
      val dep_names =
        Thm_Deps.thm_deps thy [th]
        |> map #2
        |> filter (fn dep_name => Thm_Name.ord (dep_name, name) <> EQUAL)
        |> sort_distinct Thm_Name.ord
      val resolved_deps = map_filter lookup_dep dep_names
      val missing_deps = filter is_missing_dep dep_names
      val oracles = Thm_Deps.all_oracles [th]
      val has_skip = Thm_Deps.has_skip_proof [th]
      val _ = app (append_missing target_name) missing_deps
      val _ = app (append_oracle target_name) oracles
      val atp_facts =
        resolved_deps |> map (fn (dep_name, dep_th) =>
          ((Thm_Name.short dep_name, (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)),
            Thm.prop_of dep_th))
      val (problem, _, _, _) =
        ATP_Problem_Generate.generate_atp_problem ctxt false format ATP_Problem.Hypothesis
          type_enc ATP_Problem_Generate.Sledgehammer lam_trans false true true hyp_ts concl_t
          atp_facts
      val lines =
        ATP_Problem.lines_of_atp_problem format
          (fn () => ATP_Problem_Generate.atp_problem_term_order_info problem) problem
        |> filter_out is_generated_timestamp_line
      val file_name = clean_name target_name ^ ".p"
      val file = export_dir + Path.basic file_name
      val _ = File.write_list file (map (fn s => s ^ "\\n") lines)
      val _ =
        File.append manifest
          (file_name ^ "\\t" ^ manifest_field target_name ^ "\\t" ^
            string_of_int (length dep_names) ^ "\\t" ^
            string_of_int (length resolved_deps) ^ "\\t" ^
            string_of_int (length missing_deps) ^ "\\t" ^
            string_of_int (length oracles) ^ "\\t" ^
            Bool.toString has_skip ^ "\\n")
    in
      writeln ("exported " ^ target_name ^ " with " ^
        string_of_int (length resolved_deps) ^ " proof deps to " ^ Path.print file)
    end
    handle
      THM (msg, _, _) => append_failure (Thm_Name.short name) (thm_message msg)
    | TERM (msg, _) => append_failure (Thm_Name.short name) ("TERM: " ^ msg)
    | TYPE (msg, _, _) => append_failure (Thm_Name.short name) ("TYPE: " ^ msg)
    | ERROR msg => append_failure (Thm_Name.short name) ("ERROR: " ^ msg)
    | Fail msg => append_failure (Thm_Name.short name) ("Fail: " ^ msg)

  val _ = app export_one targets
  val _ =
    writeln ("Used-dependency TFF export completed: " ^ string_of_int (length targets) ^
      " targets from " ^ string_of_int (length source_decls) ^
      " active source declarations in scope $SCOPE")
in
  ()
end
\<close>

end
EOF

cd "$PROJECT_DIR"
/project/bin/isabelle process_theories -d . -l GeoTop -o quick_and_dirty -O \
  -f "$TMP_DIR/GeoTop_Used_TFF_Export.thy"
