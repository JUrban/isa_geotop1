#!/usr/bin/env bash
# Export active top-level Top0/general-topology theorem/lemma facts as TF0/TFF ATP problems.
#
# Usage:
#   cd /project/tst
#   tptp_exp/export_top0_tff.sh [OUT_DIR]
#
# Environment:
#   TOP0_TPTP_MAX_FACTS  premise limit per problem, default 64
#   TOP0_TPTP_LIMIT      optional target limit for quick probes, default 0 = all

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT_DIR="${1:-$PROJECT_DIR/tptp_probs_top0}"
MAX_FACTS="${TOP0_TPTP_MAX_FACTS:-64}"
LIMIT="${TOP0_TPTP_LIMIT:-0}"

mkdir -p "$OUT_DIR"
OUT_DIR="$(cd "$OUT_DIR" && pwd)"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/top0_tff_export.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

SOURCE_DECLS="$(
python3 - "$PROJECT_DIR" <<'PY'
import re
import sys
from pathlib import Path

project = Path(sys.argv[1])

theories = [
    ("Top1_Ch2", "i/Top1_Ch2.thy"),
    ("Top1_Ch3", "i/Top1_Ch3.thy"),
    ("Top1_Ch4", "i/Top1_Ch4.thy"),
    ("Top1_Ch5_8", "i/Top1_Ch5_8.thy"),
    ("Top1_Ch9_13", "i/Top1_Ch9_13.thy"),
]

for theory, rel in theories:
    for line in (project / rel).read_text(encoding="utf-8").splitlines():
        match = re.match(r"\s*(lemma|theorem|corollary|proposition)\s+([A-Za-z0-9_]+)", line)
        if match:
            print(f'    ("{theory}", "{match.group(2)}"),')
PY
)"

cat > "$TMP_DIR/Top0_TFF_Export.thy" <<EOF
theory Top0_TFF_Export
  imports "Top0.Top1_Ch9_13"
begin

ML \<open>
let
  val export_dir = Path.explode "$OUT_DIR"
  val manifest = export_dir + Path.basic "manifest.tsv"
  val failures = export_dir + Path.basic "failures.tsv"
  val max_facts = $MAX_FACTS
  val limit = $LIMIT
  val source_decls = [
$SOURCE_DECLS
    ("__end_marker__", "__end_marker__")
  ]
  val source_decls = filter_out (fn decl => decl = ("__end_marker__", "__end_marker__")) source_decls

  val _ = Isabelle_System.make_directory export_dir
  val _ = File.write manifest "file\\ttheorem\\tfacts\\n"
  val _ = File.write failures "theorem\\terror\\n"

  val ctxt = @{context}
  val thy = @{theory Top1_Ch9_13}
  val format = ATP_Problem.TFF (ATP_Problem.Monomorphic, ATP_Problem.Without_FOOL)
  val type_enc =
    ATP_Problem_Generate.type_enc_of_string ATP_Problem_Generate.Strict "mono_native"
  val lam_trans = ATP_Problem_Generate.liftingN

  fun clean_name s =
    s
    |> String.map (fn c =>
      if Char.isAlphaNum c orelse c = #"_" then c else #"_")

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
      val (hyp_ts, concl_t) = Logic.strip_horn (Thm.prop_of th)
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

  fun manifest_field s =
    String.map (fn c => if c = #"\t" orelse c = #"\n" orelse c = #"\r" then #" " else c) s

  fun first_line s =
    (case String.tokens (fn c => c = #"\n" orelse c = #"\r") s of
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

  val succeeded = Unsynchronized.ref 0
  val failed = Unsynchronized.ref 0

  fun record_failure target message =
    let
      val target_name = Thm_Name.short (fst target)
      val _ = failed := ! failed + 1
      val _ =
        File.append failures
          (manifest_field target_name ^ "\\t" ^ manifest_field message ^ "\\n")
    in
      writeln ("skipped " ^ target_name ^ " due to TFF export error: " ^ message)
    end

  fun export_target target =
    (export_one target; succeeded := ! succeeded + 1)
    handle THM (msg, _, _) => record_failure target (thm_message msg)
         | TERM (msg, _) => record_failure target ("TERM: " ^ compact_message msg)
         | TYPE (msg, _, _) => record_failure target ("TYPE: " ^ compact_message msg)
         | ERROR msg => record_failure target ("ERROR: " ^ compact_message msg)
         | Fail msg => record_failure target ("Fail: " ^ compact_message msg)

  val _ = app export_target targets
  val _ =
    writeln ("TFF export completed: " ^ string_of_int (! succeeded) ^
      " problems; skipped " ^ string_of_int (! failed) ^
      " of " ^ string_of_int (length targets) ^
      " targets from " ^ string_of_int (length source_decls) ^
      " active source declarations")
in
  ()
end
\<close>

end
EOF

cd "$PROJECT_DIR"
/project/bin/isabelle process_theories -d . -l Top0 -o quick_and_dirty -O \
  -f "$TMP_DIR/Top0_TFF_Export.thy"
