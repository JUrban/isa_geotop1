#!/usr/bin/env bash
# Export active top-level GeoTop-chain theorem/lemma facts as TF0/TFF ATP problems.
#
# Usage:
#   cd /project/tst
#   tptp_exp/export_geotop_tff.sh [OUT_DIR]
#
# Environment:
#   GEOTOP_TPTP_MAX_FACTS  premise limit per problem, default 64
#   GEOTOP_TPTP_LIMIT      optional target limit for quick probes, default 0 = all
#   GEOTOP_TPTP_SCOPE      geotop or all_geotop, default all_geotop

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT_DIR="${1:-$PROJECT_DIR/tptp_probs}"
MAX_FACTS="${GEOTOP_TPTP_MAX_FACTS:-64}"
LIMIT="${GEOTOP_TPTP_LIMIT:-0}"
SCOPE="${GEOTOP_TPTP_SCOPE:-all_geotop}"

mkdir -p "$OUT_DIR"
OUT_DIR="$(cd "$OUT_DIR" && pwd)"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geotop_tff_export.XXXXXX")"
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
    raise SystemExit(f"Unknown GEOTOP_TPTP_SCOPE={scope!r}; expected geotop or all_geotop")

for theory, rel, stop_marker in theories[scope]:
    for line in (project / rel).read_text(encoding="utf-8").splitlines():
        if stop_marker and stop_marker in line:
            break
        match = re.match(r"\s*(lemma|theorem|corollary)\s+([A-Za-z0-9_]+)", line)
        if match:
            print(f'    ("{theory}", "{match.group(2)}"),')
PY
)"

cat > "$TMP_DIR/GeoTop_TFF_Export.thy" <<EOF
theory GeoTop_TFF_Export
  imports "GeoTop.GeoTop"
begin

ML \<open>
let
  val export_dir = Path.explode "$OUT_DIR"
  val manifest = export_dir + Path.basic "manifest.tsv"
  val max_facts = $MAX_FACTS
  val limit = $LIMIT
  val source_decls = [
$SOURCE_DECLS
    ("__end_marker__", "__end_marker__")
  ]
  val source_decls = filter_out (fn decl => decl = ("__end_marker__", "__end_marker__")) source_decls

  val _ = Isabelle_System.make_directory export_dir
  val _ = File.write manifest "file\\ttheorem\\tfacts\\n"

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

  val raw_targets =
    Global_Theory.all_thms_of thy true
    |> filter (is_source_fact o fst)

  val targets =
    if limit > 0 then take limit raw_targets else raw_targets

  val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
  val keywords = Thy_Header.get_keywords' ctxt
  val all_lazy_facts =
    Sledgehammer_Fact.all_facts ctxt false keywords [] [] css

  val params =
    Sledgehammer_Commands.default_params thy
      [("provers", "e"), ("type_enc", "mono_native"), ("lam_trans", "lifting"),
       ("fact_filter", "mepo"), ("max_facts", string_of_int max_facts), ("timeout", "1")]

  fun export_one (name, th) =
    let
      val target_name = Thm_Name.short name
      val hyp_ts = []
      val concl_t = Thm.prop_of th
      val usable_facts =
        all_lazy_facts
        |> filter_out (fn (_, th') => Thm.eq_thm_prop (th', th))
      val facts =
        Sledgehammer_MePo.mepo_suggested_facts ctxt params max_facts NONE hyp_ts concl_t usable_facts
      val atp_facts =
        facts |> map (fn ((fact_name, stature), fact_th) =>
          ((fact_name, stature), Thm.prop_of fact_th))
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
          (file_name ^ "\\t" ^ target_name ^ "\\t" ^ string_of_int (length facts) ^ "\\n")
    in
      writeln ("exported " ^ target_name ^ " with " ^ string_of_int (length facts) ^
        " facts to " ^ Path.print file)
    end

  val _ = app export_one targets
  val _ =
    writeln ("TFF export completed: " ^ string_of_int (length targets) ^
      " problems from " ^ string_of_int (length source_decls) ^
      " active source declarations in scope $SCOPE")
in
  ()
end
\<close>

end
EOF

cd "$PROJECT_DIR"
/project/bin/isabelle process_theories -d . -l GeoTop -o quick_and_dirty -O \
  -f "$TMP_DIR/GeoTop_TFF_Export.thy"
