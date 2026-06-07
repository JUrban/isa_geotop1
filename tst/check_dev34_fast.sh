#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

isabelle=${ISABELLE:-/project/bin/isabelle}
limit=${TIMEOUT:-90s}
isabelle_options=(-o system_heaps=true)
proof_options=()
if [ "${FORCE_PROOFS:-0}" = 1 ]; then
  proof_options=(-o skip_proofs=false)
fi
process_options=("${proof_options[@]}")
if [ "${FORCE_PROOFS:-0}" != 1 ] && [ "${SKIP_PROOFS:-0}" = 1 ]; then
  process_options=(-o skip_proofs=true)
fi

usage() {
  cat >&2 <<'EOF'
usage: ./check_dev34_fast.sh MODE [ARGS...]

Fast modes:
  quick        no-build snapshot: target holes plus dirty dev34 layers (default)
  holes        rg for target sorry/sledgehammer markers in all dev34 layers
  index PAT    rg PAT in THEOREMS_AND_DEFS.txt and STMT_INDEX.txt
  names PAT    rg PAT in THEOREMS_AND_DEFS.txt only
  stmts PAT    rg PAT in STMT_INDEX.txt only
  grep PAT     rg PAT in target dev34 theories and indexes
  scan PAT     alias for grep; use this before proof attempts
  dirty [FILES] show dirty/explicit dev34 layer files and the auto build target
  plan [FILES]  show hot-loop parent heaps for changed/explicit files
  warm [FILES]  build and store hot-loop parent heaps for changed/explicit files
  cache-plan [FILES]
               show all cache layers through the dirty/explicit target
  cache-through [FILES]
               build/store all layers through the dirty/explicit target, skipping fresh
  cache-parents [FILES]
               build/store only reusable parent layers for dirty/explicit files
  proc [FILES] process changed/explicit theories against their parent heap
  hot [FILES]  alias for proc; skips fresh target/process caches, auto-warms parents
  outline [FILES]
               fast scaffold check: process with skip_proofs=true
  split-hot FILE PAT
               cache FILE before the first PAT line, then process the remaining tail
  slice-hot FILE PAT
               cache FILE before PAT, then process only the next top-level theorem/lemma slice
  split-warm FILE PAT
               cache FILE before the first PAT line, but do not process the tail
  focus-list   list named proof-focus targets
  focus NAME [PAT]
               full-index scan PAT, then slice-hot the named target
  focus-full NAME [PAT]
               full-index scan PAT, then split-hot the named target through file end
  focus-warm NAME
               cache parent layers and the completed prefix before a named target
  focus-warm-all
               cache parent layers and completed prefixes before all named remaining targets
  focus-parents NAME
               cache only reusable parent layers for a named target
  focus-outline NAME [PAT]
               focus with skip_proofs=true for scaffold iteration
  graph-focus [PAT]
               full-index scan PAT, then split-hot the active graph theorem
  graph-outline [PAT]
               graph-focus with skip_proofs=true for fast scaffold iteration
  graph-warm   build/cache the active graph split prefix only
  loop [--hot] PAT [FILES]
               cheap proof loop: full-index grep PAT, holes, dirty plan
               with --hot, also run hot [FILES]
  loop-hot PAT [FILES]
               compatibility alias for loop --hot PAT [FILES]
  layer [FILES] build the smallest dirty/explicit dev34 layer only
  cache [FILES] build and store the smallest dirty/explicit dev34 layer heap
  cache-status [FILES]
               show whether the smallest dirty/explicit dev34 layer heap is fresh
  cache-all    build missing/stale heaps for every dev34 layer, skipping fresh ones
  cache-clean  remove local dev34 heap freshness stamps

Milestone modes:
  auto [FILES]  build the smallest dirty/explicit dev34 layer detected
  prove [FILES] build the smallest dirty/explicit dev34 layer with proofs forced

Build modes:
  pre          build GeoTopPre3Dirty
  prefix-base  build GeoTop34PrefixBaseDirty only
  prefix-graph-cache
               build GeoTop34PrefixGraphCacheDirty only
  prefix-graph build GeoTop34PrefixGraphDirty only
  prefix-mid   build GeoTop34PrefixMidDirty only
  prefix       build GeoTop34PrefixDirty
  pre-heap, prefix-base-heap, prefix-graph-cache-heap, prefix-graph-heap,
  prefix-mid-heap, prefix-heap
               build and store the named layer heap for later hot loops
  facts-heap, workfacts-heap, linkfacts-heap, graphfacts-heap, graphwork-heap,
  openstar-heap, core-heap, dev34-heap
               build and store later dev34 layer heaps
  facts        build GeoTop34FactsDirty
  workfacts    build GeoTop34WorkFactsDirty
  linkfacts    build GeoTop34LinkFactsDirty
  graphfacts   build GeoTop34GraphFactsDirty
  graphwork    build GeoTop34GraphWorkDirty
  openstar     build GeoTop34OpenStarDirty
  core         build GeoTop34CoreDirty
  dev34        build GeoTop34Dev
EOF
}

build_pre() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre \
    GeoTopPre3Dirty
}

build_prefix() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix \
    GeoTop34PrefixDirty
}

build_prefix_base() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base \
    GeoTop34PrefixBaseDirty
}

build_prefix_graph_cache() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph \
    GeoTop34PrefixGraphCacheDirty
}

build_prefix_graph() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph \
    GeoTop34PrefixGraphDirty
}

build_prefix_mid() {
  exec timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid \
    GeoTop34PrefixMidDirty
}

build_dev34() {
  exec timeout "${TIMEOUT:-240s}" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
    -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
    -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
    GeoTop34Dev
}

dirty_layers() {
  git diff --relative --name-only HEAD -- \
    dev34_pre dev34_prefix_base dev34_prefix_graph dev34_prefix_mid dev34_prefix dev34_facts dev34_workfacts dev34_linkfacts \
    dev34_graphfacts dev34_graphwork dev34_openstar dev34_core dev34
}

layer_files() {
  if [ "$#" -gt 0 ]; then
    printf '%s\n' "$@" | sed 's#^\./##'
  else
    dirty_layers
  fi
}

auto_target() {
  files=${1:-$(dirty_layers)}
  if printf '%s\n' "$files" | rg -q '^dev34/'; then
    printf '%s\n' dev34
  elif printf '%s\n' "$files" | rg -q '^dev34_core/'; then
    printf '%s\n' core
  elif printf '%s\n' "$files" | rg -q '^dev34_openstar/'; then
    printf '%s\n' openstar
  elif printf '%s\n' "$files" | rg -q '^dev34_graphwork/'; then
    printf '%s\n' graphwork
  elif printf '%s\n' "$files" | rg -q '^dev34_graphfacts/'; then
    printf '%s\n' graphfacts
  elif printf '%s\n' "$files" | rg -q '^dev34_linkfacts/'; then
    printf '%s\n' linkfacts
  elif printf '%s\n' "$files" | rg -q '^dev34_workfacts/'; then
    printf '%s\n' workfacts
  elif printf '%s\n' "$files" | rg -q '^dev34_facts/'; then
    printf '%s\n' facts
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix/'; then
    printf '%s\n' prefix
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix_mid/'; then
    printf '%s\n' prefix-mid
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix_graph/(ROOT|GeoTop_3_4_Prefix_Graph\.thy)$'; then
    printf '%s\n' prefix-graph
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache\.thy$'; then
    printf '%s\n' prefix-graph-cache
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix_graph/'; then
    printf '%s\n' prefix-graph
  elif printf '%s\n' "$files" | rg -q '^dev34_prefix_base/'; then
    printf '%s\n' prefix-base
  elif printf '%s\n' "$files" | rg -q '^dev34_pre/'; then
    printf '%s\n' pre
  else
    printf '%s\n' none
  fi
}

target_theories=(
  dev34_pre/GeoTop.thy
  dev34_prefix_base/GeoTop_3_4_Prefix_Base.thy
  dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy
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

hole_theories=(
  dev34_prefix_base/GeoTop_3_4_Prefix_Base.thy
  dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy
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

layer_rank() {
  case "$1" in
    dev34_pre/*) printf '%s\n' 1 ;;
    dev34_prefix_base/*) printf '%s\n' 2 ;;
    dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy) printf '%s\n' 3 ;;
    dev34_prefix_graph/*) printf '%s\n' 4 ;;
    dev34_prefix_mid/*) printf '%s\n' 5 ;;
    dev34_prefix/*) printf '%s\n' 6 ;;
    dev34_facts/*) printf '%s\n' 7 ;;
    dev34_workfacts/*) printf '%s\n' 8 ;;
    dev34_linkfacts/*) printf '%s\n' 9 ;;
    dev34_graphfacts/*) printf '%s\n' 10 ;;
    dev34_graphwork/*) printf '%s\n' 11 ;;
    dev34_openstar/*) printf '%s\n' 12 ;;
    dev34_core/*) printf '%s\n' 13 ;;
    dev34/*) printf '%s\n' 14 ;;
    *) printf '%s\n' 99 ;;
  esac
}

target_rank() {
  case "$1" in
    pre) printf '%s\n' 1 ;;
    prefix-base) printf '%s\n' 2 ;;
    prefix-graph-cache) printf '%s\n' 3 ;;
    prefix-graph) printf '%s\n' 4 ;;
    prefix-mid) printf '%s\n' 5 ;;
    prefix) printf '%s\n' 6 ;;
    facts) printf '%s\n' 7 ;;
    workfacts) printf '%s\n' 8 ;;
    linkfacts) printf '%s\n' 9 ;;
    graphfacts) printf '%s\n' 10 ;;
    graphwork) printf '%s\n' 11 ;;
    openstar) printf '%s\n' 12 ;;
    core) printf '%s\n' 13 ;;
    dev34) printf '%s\n' 14 ;;
    *) printf '%s\n' 99 ;;
  esac
}

target_layer_dir() {
  case "$1" in
    pre) printf '%s\n' dev34_pre ;;
    prefix-base) printf '%s\n' dev34_prefix_base ;;
    prefix-graph-cache) printf '%s\n' dev34_prefix_graph ;;
    prefix-graph) printf '%s\n' dev34_prefix_graph ;;
    prefix-mid) printf '%s\n' dev34_prefix_mid ;;
    prefix) printf '%s\n' dev34_prefix ;;
    facts) printf '%s\n' dev34_facts ;;
    workfacts) printf '%s\n' dev34_workfacts ;;
    linkfacts) printf '%s\n' dev34_linkfacts ;;
    graphfacts) printf '%s\n' dev34_graphfacts ;;
    graphwork) printf '%s\n' dev34_graphwork ;;
    openstar) printf '%s\n' dev34_openstar ;;
    core) printf '%s\n' dev34_core ;;
    dev34) printf '%s\n' dev34 ;;
    *) return 2 ;;
  esac
}

target_session() {
  case "$1" in
    pre) printf '%s\n' GeoTopPre3Dirty ;;
    prefix-base) printf '%s\n' GeoTop34PrefixBaseDirty ;;
    prefix-graph-cache) printf '%s\n' GeoTop34PrefixGraphCacheDirty ;;
    prefix-graph) printf '%s\n' GeoTop34PrefixGraphDirty ;;
    prefix-mid) printf '%s\n' GeoTop34PrefixMidDirty ;;
    prefix) printf '%s\n' GeoTop34PrefixDirty ;;
    facts) printf '%s\n' GeoTop34FactsDirty ;;
    workfacts) printf '%s\n' GeoTop34WorkFactsDirty ;;
    linkfacts) printf '%s\n' GeoTop34LinkFactsDirty ;;
    graphfacts) printf '%s\n' GeoTop34GraphFactsDirty ;;
    graphwork) printf '%s\n' GeoTop34GraphWorkDirty ;;
    openstar) printf '%s\n' GeoTop34OpenStarDirty ;;
    core) printf '%s\n' GeoTop34CoreDirty ;;
    dev34) printf '%s\n' GeoTop34Dev ;;
    *) return 2 ;;
  esac
}

layer_targets=(
  pre
  prefix-base
  prefix-graph-cache
  prefix-graph
  prefix-mid
  prefix
  facts
  workfacts
  linkfacts
  graphfacts
  graphwork
  openstar
  core
  dev34
)

target_timeout() {
  case "$1" in
    pre|prefix-base|prefix-graph-cache|prefix-graph|prefix-mid|prefix) printf '%s\n' "$limit" ;;
    facts) printf '%s\n' "${TIMEOUT:-120s}" ;;
    workfacts|linkfacts) printf '%s\n' "${TIMEOUT:-150s}" ;;
    graphfacts|graphwork) printf '%s\n' "${TIMEOUT:-180s}" ;;
    openstar|core) printf '%s\n' "${TIMEOUT:-210s}" ;;
    dev34) printf '%s\n' "${TIMEOUT:-240s}" ;;
    *) return 2 ;;
  esac
}

target_dirs_args() {
  rank=$(target_rank "$1")
  printf '%s\n' -d .
  last_dir=
  for target in pre prefix-base prefix-graph-cache prefix-graph prefix-mid prefix facts workfacts linkfacts graphfacts graphwork openstar core dev34; do
    if [ "$(target_rank "$target")" -le "$rank" ]; then
      dir=$(target_layer_dir "$target")
      if [ "$dir" != "$last_dir" ]; then
        printf '%s\n' -d
        printf '%s\n' "$dir"
        last_dir=$dir
      fi
    fi
  done
}

target_source_files() {
  rank=$(target_rank "$1")
  if [ "$rank" -ge 1 ]; then
    printf '%s\n' GeoTop.thy
  fi
  for target in pre prefix-base prefix-graph-cache prefix-graph prefix-mid prefix facts workfacts linkfacts graphfacts graphwork openstar core dev34; do
    if [ "$(target_rank "$target")" -le "$rank" ]; then
      dir=$(target_layer_dir "$target")
      case "$target" in
        prefix-graph-cache)
          printf '%s\n' "$dir/ROOT" "$dir/cache/GeoTop_3_4_Prefix_Graph_Cache.thy"
          ;;
        prefix-graph)
          printf '%s\n' "$dir/GeoTop_3_4_Prefix_Graph.thy"
          ;;
        *)
          find "$dir" -maxdepth 1 -type f \( -name ROOT -o -name '*.thy' \) -print
          ;;
      esac
    fi
  done | LC_ALL=C sort -u
}

cache_dir=.dev34_fast_cache

cache_digest() {
  target=$1
  {
    printf 'target=%s\n' "$target"
    printf 'session=%s\n' "$(target_session "$target")"
    printf 'force_proofs=%s\n' "${FORCE_PROOFS:-0}"
    target_source_files "$target" | while IFS= read -r file; do
      sha256sum "$file"
    done
  } | sha256sum | awk '{print $1}'
}

cache_stamp() {
  printf '%s/%s.sha256\n' "$cache_dir" "$1"
}

proc_stamp() {
  key=$(printf '%s' "$1" | sha256sum | awk '{print $1}')
  printf '%s/proc-%s.sha256\n' "$cache_dir" "$key"
}

split_stamp() {
  key=$(printf '%s' "$1" | sha256sum | awk '{print $1}')
  printf '%s/split-%s.sha256\n' "$cache_dir" "$key"
}

write_if_changed() {
  out=$1
  tmp=$out.tmp.$$
  cat >"$tmp"
  if [ -f "$out" ] && cmp -s "$tmp" "$out"; then
    rm -f "$tmp"
  else
    mv "$tmp" "$out"
  fi
}

cache_is_fresh() {
  target=$1
  stamp=$(cache_stamp "$target")
  [ -s "$stamp" ] && [ "$(cat "$stamp")" = "$(cache_digest "$target")" ]
}

proc_digest() {
  file=$1
  parent_target=$2
  logic=$3
  layer_root=$(dirname "$file")/ROOT
  {
    printf 'mode=process_theories\n'
    printf 'file=%s\n' "$file"
    printf 'logic=%s\n' "$logic"
    printf 'force_proofs=%s\n' "${FORCE_PROOFS:-0}"
    printf 'skip_proofs=%s\n' "${SKIP_PROOFS:-0}"
    sha256sum "$file"
    if [ -f "$layer_root" ]; then
      sha256sum "$layer_root"
    fi
    printf 'parent_target=%s\n' "$parent_target"
    if [ "$parent_target" != none ]; then
      printf 'parent_digest=%s\n' "$(cache_digest "$parent_target")"
    fi
  } | sha256sum | awk '{print $1}'
}

proc_cache_is_fresh() {
  file=$1
  parent_target=$2
  logic=$3
  [ "${DEV34_FAST_PROC_CACHE:-1}" != 0 ] || return 1
  [ "$parent_target" != none ] || return 1
  cache_is_fresh "$parent_target" || return 1
  stamp=$(proc_stamp "$file:$parent_target:$logic:force=${FORCE_PROOFS:-0}:skip=${SKIP_PROOFS:-0}")
  [ -s "$stamp" ] && [ "$(cat "$stamp")" = "$(proc_digest "$file" "$parent_target" "$logic")" ]
}

proc_cache_store() {
  file=$1
  parent_target=$2
  logic=$3
  [ "${DEV34_FAST_PROC_CACHE:-1}" != 0 ] || return 0
  [ "$parent_target" != none ] || return 0
  cache_is_fresh "$parent_target" || return 0
  mkdir -p "$cache_dir"
  proc_digest "$file" "$parent_target" "$logic" \
    >"$(proc_stamp "$file:$parent_target:$logic:force=${FORCE_PROOFS:-0}:skip=${SKIP_PROOFS:-0}")"
}

split_hot_one() {
  local file=$1
  local pattern=$2
  local chain_pattern=${3:-}
  local logic dirs
  local start_line begin_line end_line next_top_line tail_end_line
  local chain_dir chain_session chain_theory chain_digest chain_start_line
  local chain_key chain_base chain_stamp_file
  local key base split_dir prefix_theory prefix_session prefix_file prefix_parent_session
  local parent_target split_key split_digest split_stamp_file
  local tail_mode tail_suffix tail_theory tail_file tail_key tail_digest tail_stamp_file
  parent_context "$file" split-hot || return $?

  if [ ! -f "$file" ]; then
    printf 'split-hot: %s does not exist\n' "$file" >&2
    return 2
  fi

  start_line=$(rg -n -- "$pattern" "$file" | head -n 1 | cut -d: -f1 || true)
  if [ -z "$start_line" ]; then
    printf 'split-hot: pattern not found in %s: %s\n' "$file" "$pattern" >&2
    return 2
  fi

  begin_line=$(awk '/^begin[[:space:]]*$/ { print NR; exit }' "$file")
  end_line=$(awk '/^end[[:space:]]*$/ { line = NR } END { print line }' "$file")
  if [ -z "$begin_line" ] || [ -z "$end_line" ] || [ "$start_line" -le "$begin_line" ] || [ "$end_line" -le "$start_line" ]; then
    printf 'split-hot: cannot split %s at line %s\n' "$file" "$start_line" >&2
    return 2
  fi

  chain_dir=
  chain_session=
  chain_theory=
  chain_digest=
  chain_start_line=
  if [ -n "$chain_pattern" ]; then
    chain_start_line=$(rg -n -- "$chain_pattern" "$file" | head -n 1 | cut -d: -f1 || true)
    if [ -z "$chain_start_line" ]; then
      printf 'split-hot: chain pattern not found in %s: %s\n' "$file" "$chain_pattern" >&2
      return 2
    fi
    if [ "$chain_start_line" -le "$begin_line" ] || [ "$start_line" -le "$chain_start_line" ]; then
      printf 'split-hot: chain pattern must be before target in %s: %s\n' "$file" "$chain_pattern" >&2
      return 2
    fi

    printf 'split-hot: warming chained prefix for %s before line %s\n' "$file" "$chain_start_line"
    DEV34_FAST_PREFIX_ONLY=1 split_hot_one "$file" "$chain_pattern"
    parent_context "$file" split-hot || return $?

    chain_key=$(printf '%s\n%s\n%s\n' "$file" "$chain_pattern" "$logic" | sha256sum | awk '{print substr($1, 1, 12)}')
    chain_base=$(basename "$file" .thy)
    chain_dir="$cache_dir/split-$chain_key"
    chain_theory="${chain_base}_Split_${chain_key}_Prefix"
    chain_session="${chain_base}_Split_${chain_key}_Prefix_Session"
    chain_stamp_file=$(split_stamp "$file:$chain_pattern:prefix:force=${FORCE_PROOFS:-0}")
    if [ -s "$chain_stamp_file" ]; then
      chain_digest=$(cat "$chain_stamp_file")
    else
      printf 'split-hot: missing chained prefix stamp for %s before line %s\n' "$file" "$chain_start_line" >&2
      return 1
    fi
  fi

  mkdir -p "$cache_dir"
  key=$(printf '%s\n%s\n%s\n' "$file" "$pattern" "$logic" | sha256sum | awk '{print substr($1, 1, 12)}')
  base=$(basename "$file" .thy)
  split_dir="$cache_dir/split-$key"
  prefix_theory="${base}_Split_${key}_Prefix"
  prefix_session="${base}_Split_${key}_Prefix_Session"
  prefix_file="$split_dir/$prefix_theory.thy"
  prefix_parent_session=${chain_session:-$logic}

  mkdir -p "$split_dir"
  write_if_changed "$split_dir/ROOT" <<EOF2
session $prefix_session = $prefix_parent_session +
  options [system_heaps, quick_and_dirty, skip_proofs, timeout = 240]
  theories
    $prefix_theory
EOF2

  if [ -n "$chain_pattern" ]; then
    {
      printf 'theory %s\n' "$prefix_theory"
      printf '  imports "%s.%s"\n' "$chain_session" "$chain_theory"
      printf 'begin\n\n'
      sed -n "${chain_start_line},$((start_line - 1))p" "$file"
      printf '\nend\n'
    } | write_if_changed "$prefix_file"
  else
    awk -v name="$prefix_theory" -v begin_line="$begin_line" -v start_line="$start_line" '
      NR == 1 { print "theory " name; next }
      NR <= begin_line { print; next }
      NR < start_line { print; next }
      END { print ""; print "end" }
    ' "$file" | write_if_changed "$prefix_file"
  fi

  if [ "${DEV34_FAST_VERBOSE:-0}" = 1 ]; then
    printf 'session %s = %s +\n' "$prefix_session" "$prefix_parent_session"
    printf '  options [system_heaps, quick_and_dirty, skip_proofs, timeout = 240]\n'
    printf '  theories\n'
    printf '    %s\n' "$prefix_theory"
  fi

  parent_target=$(parent_target_for_file "$file")
  if [ "${DEV34_FAST_AUTOWARM:-1}" != 0 ] && [ "$parent_target" != none ]; then
    cache_warm_parent_target "$parent_target"
  fi

  split_key=$(printf 'split-prefix\n%s\n%s\nforce_proofs=%s\n%s\n' \
    "$file" "$pattern" "${FORCE_PROOFS:-0}" \
    "$(sha256sum "$prefix_file" "$split_dir/ROOT")")
  if [ "$parent_target" != none ]; then
    split_key=$(printf '%s\nparent=%s\n%s\n' "$split_key" "$parent_target" "$(cache_digest "$parent_target")")
  fi
  if [ -n "$chain_pattern" ]; then
    split_key=$(printf '%s\nchain=%s\n%s\n' "$split_key" "$chain_pattern" "$chain_digest")
  fi
  split_digest=$(printf '%s' "$split_key" | sha256sum | awk '{print $1}')
  split_stamp_file=$(split_stamp "$file:$pattern:prefix:force=${FORCE_PROOFS:-0}")

  if [ -n "$chain_pattern" ]; then
    mapfile -t dirs < <(printf '%s\n' "${dirs[@]}"; printf '%s\n' -d "$chain_dir"; printf '%s\n' -d "$split_dir")
  else
    mapfile -t dirs < <(printf '%s\n' "${dirs[@]}"; printf '%s\n' -d "$split_dir")
  fi
  if [ -s "$split_stamp_file" ] && [ "$(cat "$split_stamp_file")" = "$split_digest" ]; then
    printf 'split-hot: skipped prefix cache for %s before line %s\n' "$file" "$start_line"
  else
    printf 'split-hot: building prefix cache for %s before line %s\n' "$file" "$start_line"
    timeout "$limit" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      "${dirs[@]}" \
      -b "$prefix_session"
    printf '%s' "$split_digest" >"$split_stamp_file"
  fi

  if [ "${DEV34_FAST_PREFIX_ONLY:-0}" = 1 ]; then
    printf 'split-hot: prefix cache ready for %s before line %s\n' "$file" "$start_line"
    return 0
  fi

  tail_mode=tail
  tail_suffix=Tail
  tail_end_line=$((end_line - 1))
  if [ "${DEV34_FAST_SLICE_ONLY:-0}" = 1 ]; then
    tail_mode=slice
    tail_suffix=Slice
    next_top_line=$(awk -v start_line="$start_line" '
      NR > start_line &&
      /^(lemma|theorem|corollary|proposition)[[:space:]]/ {
        print NR
        exit
      }
    ' "$file")
    if [ -n "$next_top_line" ]; then
      tail_end_line=$((next_top_line - 1))
    fi
  fi
  tail_theory="${base}_Split_${key}_${tail_suffix}"
  tail_file="$split_dir/$tail_theory.thy"

  {
    printf 'theory %s\n' "$tail_theory"
    printf '  imports "%s.%s"\n' "$prefix_session" "$prefix_theory"
    printf 'begin\n\n'
    sed -n "${start_line},${tail_end_line}p" "$file"
    printf '\nend\n'
  } | write_if_changed "$tail_file"

  tail_key=$(printf 'split-%s\n%s\n%s\nforce_proofs=%s\nskip_proofs=%s\n%s\n%s\n' \
    "$tail_mode" \
    "$file" "$pattern" "${FORCE_PROOFS:-0}" "${SKIP_PROOFS:-0}" \
    "$split_digest" "$(sha256sum "$tail_file")")
  tail_digest=$(printf '%s' "$tail_key" | sha256sum | awk '{print $1}')
  tail_stamp_file=$(split_stamp "$file:$pattern:$tail_mode:force=${FORCE_PROOFS:-0}:skip=${SKIP_PROOFS:-0}")
  if [ "${DEV34_FAST_PROC_CACHE:-1}" != 0 ] && [ -s "$tail_stamp_file" ] && [ "$(cat "$tail_stamp_file")" = "$tail_digest" ]; then
    printf 'split-hot: skipped %s process for %s from line %s through %s\n' \
      "$tail_mode" "$file" "$start_line" "$tail_end_line"
    return 0
  fi

  printf 'split-hot: processing %s for %s from line %s through %s\n' \
    "$tail_mode" "$file" "$start_line" "$tail_end_line"
  timeout "$limit" "$isabelle" process_theories \
    "${isabelle_options[@]}" \
    "${process_options[@]}" \
    "${dirs[@]}" -l "$prefix_session" -o quick_and_dirty -f "$tail_file"
  printf '%s' "$tail_digest" >"$tail_stamp_file"
}

active_graph_file=dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy
active_graph_pattern=geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix

focus_target_names() {
  cat <<'EOF2'
graph-branch
graph-cycle-cut
mid-split-free
mid-fold
mid-support
mid-d42
prefix-d44
dev34-cycle
dev34-fan
dev34-semicircle
EOF2
}

focus_target() {
  case "$1" in
    graph-branch)
      printf '%s\t%s\t%s\n' \
        dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy \
        geotop_branch_vertex_deletion_disconnects_finite_linear_graph_prefix \
        'branch vertex deletion disconnects finite linear graph'
      ;;
    graph-cycle-cut|graph-split|graph)
      printf '%s\t%s\t%s\n' \
        "$active_graph_file" \
        "$active_graph_pattern" \
        'cycle cut graph orbit nonadjacent reversed intersection'
      ;;
    mid-split-free)
      printf '%s\t%s\t%s\n' \
        dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
        geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix \
        'subdisk induction transfer nonfree boundary triangle split free count'
      ;;
    mid-fold)
      printf '%s\t%s\t%s\n' \
        dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
        'theorem Theorem_GT_3_4' \
        'Theorem_GT_3_4 ind_step free triangle fold elimination'
      ;;
    mid-support)
      printf '%s\t%s\t%s\n' \
        dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
        'theorem Theorem_GT_3_7' \
        'Theorem_GT_3_7 support in U supported folds'
      ;;
    mid-d42)
      printf '%s\t%s\t%s\n' \
        dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
        'theorem Theorem_GT_4_2' \
        'Theorem_GT_4_2 hD42_disjoint arc separation components'
      ;;
    prefix-d44)
      printf '%s\t%s\t%s\n' \
        dev34_prefix/GeoTop_3_4_Prefix.thy \
        'theorem Theorem_GT_4_4' \
        'Theorem_GT_4_4 brick regular neighborhood component frontier'
      ;;
    dev34-cycle)
      printf '%s\t%s\t%s\n' \
        dev34/GeoTop_3_4.thy \
        geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34 \
        'finite connected nonisolated linear graph boundary cycle model'
      ;;
    dev34-fan)
      printf '%s\t%s\t%s\n' \
        dev34/GeoTop_3_4.thy \
        geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34 \
        'endpoint degree one chain boundary arc fan target'
      ;;
    dev34-semicircle)
      printf '%s\t%s\t%s\n' \
        dev34/GeoTop_3_4.thy \
        geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34 \
        'semicircle one side simplex local separates domain sphere arc'
      ;;
    *)
      printf 'focus: unknown target %s\n' "$1" >&2
      printf 'focus: known targets are:\n' >&2
      focus_target_names >&2
      return 2
      ;;
  esac
}

focus_target_parts() {
  entry=$(focus_target "$1") || return $?
  focus_file=${entry%%$'\t'*}
  rest=${entry#*$'\t'}
  focus_pattern=${rest%%$'\t'*}
  focus_scan=${rest#*$'\t'}
}

focus_chain_pattern() {
  case "$1" in
    mid-support)
      printf '%s\n' 'theorem Theorem_GT_3_4'
      ;;
    mid-d42)
      printf '%s\n' 'theorem Theorem_GT_3_7'
      ;;
    dev34-fan)
      printf '%s\n' geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34
      ;;
    dev34-semicircle)
      printf '%s\n' geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
      ;;
    *)
      printf '%s\n' ''
      ;;
  esac
}

focus_list() {
  while IFS= read -r name; do
    focus_target_parts "$name"
    printf '%-18s %s  ::  %s\n' "$name" "$focus_file" "$focus_pattern"
  done <<EOF2
$(focus_target_names)
EOF2
}

focus_one() {
  mode=$1
  name=$2
  shift 2
  focus_target_parts "$name" || return $?
  chain_pattern=$(focus_chain_pattern "$name")
  if [ "$mode" != warm ]; then
    scan_pat=${*:-$focus_scan}
    if [ -n "$scan_pat" ]; then
      printf 'full-index/source scan: %s\n' "$scan_pat"
      rg -n -i -- "$scan_pat" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}" || true
      printf '\n'
    fi
  fi
  case "$mode" in
    slice)
      DEV34_FAST_SLICE_ONLY=1 split_hot_one "$focus_file" "$focus_pattern" "$chain_pattern"
      ;;
    full)
      split_hot_one "$focus_file" "$focus_pattern" "$chain_pattern"
      ;;
    warm)
      DEV34_FAST_PREFIX_ONLY=1 split_hot_one "$focus_file" "$focus_pattern" "$chain_pattern"
      ;;
    *)
      printf 'focus: bad mode %s\n' "$mode" >&2
      return 2
      ;;
  esac
}

focus_parents_one() {
  name=$1
  focus_target_parts "$name" || return $?
  parent_target=$(parent_target_for_file "$focus_file")
  if [ "$parent_target" = none ]; then
    printf 'focus-parents: %s has no reusable dev34 parent layer\n' "$name"
    return 0
  fi
  cache_warm_parent_target "$parent_target"
}

cache_status_line() {
  target=$1
  if [ "$target" = none ]; then
    printf 'cache: none (no dev34 layer target)\n'
  elif cache_is_fresh "$target"; then
    printf 'cache: fresh %s (%s)\n' "$target" "$(target_session "$target")"
  else
    printf 'cache: stale/missing %s (%s)\n' "$target" "$(target_session "$target")"
  fi
}

cache_build_target() {
  target=$1
  if [ "$target" = none ]; then
    "$0" holes
    return $?
  fi
  mkdir -p "$cache_dir"
  if [ "${FORCE_CACHE:-0}" != 1 ] && cache_is_fresh "$target"; then
    cache_status_line "$target"
    return 0
  fi
  mapfile -t dirs < <(target_dirs_args "$target")
  session=$(target_session "$target")
  build_timeout=$(target_timeout "$target")
  printf 'cache build: %s (%s)\n' "$target" "$session"
  timeout "$build_timeout" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    "${dirs[@]}" \
    -b "$session"
  cache_digest "$target" >"$(cache_stamp "$target")"
  cache_status_line "$target"
}

cache_plan_through() {
  target=$1
  if [ "$target" = none ]; then
    printf 'cache: none (no dev34 layer target)\n'
    return 0
  fi
  rank=$(target_rank "$target")
  for layer in "${layer_targets[@]}"; do
    if [ "$(target_rank "$layer")" -le "$rank" ]; then
      cache_status_line "$layer"
    fi
  done
}

cache_build_through() {
  target=$1
  if [ "$target" = none ]; then
    "$0" holes
    return $?
  fi
  status=0
  rank=$(target_rank "$target")
  for layer in "${layer_targets[@]}"; do
    if [ "$(target_rank "$layer")" -le "$rank" ]; then
      if cache_build_target "$layer"; then
        :
      else
        status=$?
        break
      fi
    fi
  done
  return "$status"
}

cache_warm_parent_target() {
  target=$1
  if [ "$target" = none ]; then
    return 0
  fi
  if cache_is_fresh "$target"; then
    cache_status_line "$target"
    return 0
  fi
  if [ "${DEV34_FAST_DEEP_AUTOWARM:-1}" != 0 ]; then
    printf 'cache warm-through: parent chain to %s\n' "$target"
    cache_build_through "$target"
  else
    cache_build_target "$target"
  fi
}

cache_build_parents() {
  files=$1
  if [ -z "$files" ]; then
    printf '(no dirty/explicit dev34 layer files)\n'
    return 0
  fi
  status=0
  seen=
  while IFS="$(printf '\t')" read -r _ file; do
    [ -z "$file" ] && continue
    parent=$(parent_target_for_file "$file" 2>/dev/null || printf '%s\n' none)
    [ "$parent" != none ] || continue
    case " $seen " in
      *" $parent "*) continue ;;
    esac
    seen="$seen $parent"
    if cache_warm_parent_target "$parent"; then
      :
    else
      status=$?
      break
    fi
  done <<EOF2
$(ordered_layer_files "$files" | sort -n -k1,1)
EOF2
  return "$status"
}

parent_context() {
  file=$1
  case "$file" in
    dev34_pre/*)
      logic=GeoTopPrefix
      dirs=(-d . -d dev34_pre)
      ;;
    dev34_prefix_base/*)
      logic=GeoTopPre3Dirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base)
      ;;
    dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy)
      logic=GeoTop34PrefixBaseDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph)
      ;;
    dev34_prefix_graph/*)
      logic=GeoTop34PrefixGraphCacheDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph)
      ;;
    dev34_prefix_mid/*)
      logic=GeoTop34PrefixGraphDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid)
      ;;
    dev34_prefix/*)
      logic=GeoTop34PrefixMidDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix)
      ;;
    dev34_facts/*)
      logic=GeoTop34PrefixDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts)
      ;;
    dev34_workfacts/*)
      logic=GeoTop34FactsDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts)
      ;;
    dev34_linkfacts/*)
      logic=GeoTop34WorkFactsDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts)
      ;;
    dev34_graphfacts/*)
      logic=GeoTop34LinkFactsDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts)
      ;;
    dev34_graphwork/*)
      logic=GeoTop34GraphFactsDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork)
      ;;
    dev34_openstar/*)
      logic=GeoTop34GraphWorkDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork -d dev34_openstar)
      ;;
    dev34_core/*)
      logic=GeoTop34OpenStarDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork -d dev34_openstar -d dev34_core)
      ;;
    dev34/*)
      logic=GeoTop34CoreDirty
      dirs=(-d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34)
      ;;
    *)
      printf '%s: %s is not in a dev34 layer\n' "${2:-hot}" "$file" >&2
      return 2
      ;;
  esac
}

parent_target_for_file() {
  case "$1" in
    dev34_pre/*) printf '%s\n' none ;;
    dev34_prefix_base/*) printf '%s\n' pre ;;
    dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy) printf '%s\n' prefix-base ;;
    dev34_prefix_graph/*) printf '%s\n' prefix-graph-cache ;;
    dev34_prefix_mid/*) printf '%s\n' prefix-graph ;;
    dev34_prefix/*) printf '%s\n' prefix-mid ;;
    dev34_facts/*) printf '%s\n' prefix ;;
    dev34_workfacts/*) printf '%s\n' facts ;;
    dev34_linkfacts/*) printf '%s\n' workfacts ;;
    dev34_graphfacts/*) printf '%s\n' linkfacts ;;
    dev34_graphwork/*) printf '%s\n' graphfacts ;;
    dev34_openstar/*) printf '%s\n' graphwork ;;
    dev34_core/*) printf '%s\n' openstar ;;
    dev34/*) printf '%s\n' core ;;
    *) return 2 ;;
  esac
}

proc_one() {
  file=$1
  parent_context "$file" proc || return $?
  target=$(auto_target "$file")
  if [ "${DEV34_FAST_SKIP_FRESH_TARGET:-1}" != 0 ] && cache_is_fresh "$target"; then
    cache_status_line "$target"
    printf 'process_theories: skipped %s (fresh target cache)\n' "$file"
    return 0
  fi

  parent_target=$(parent_target_for_file "$file")

  if [ "${DEV34_FAST_AUTOWARM:-1}" != 0 ] && [ "$parent_target" != none ]; then
    cache_warm_parent_target "$parent_target"
  fi

  if proc_cache_is_fresh "$file" "$parent_target" "$logic"; then
    printf 'process_theories: skipped %s (fresh process cache)\n' "$file"
    return 0
  fi

  printf 'process_theories: %s with parent %s\n' "$file" "$logic"
  timeout "$limit" "$isabelle" process_theories \
    "${isabelle_options[@]}" \
    "${process_options[@]}" \
    "${dirs[@]}" -l "$logic" -o quick_and_dirty -f "$file"
  proc_cache_store "$file" "$parent_target" "$logic"
}

plan_one() {
  file=$1
  parent_context "$file" plan || return $?
  parent_target=$(parent_target_for_file "$file")
  if [ "$parent_target" = none ]; then
    printf '%s\tparent=%s\tcache=external\n' "$file" "$logic"
  elif cache_is_fresh "$parent_target"; then
    printf '%s\tparent=%s\tcache=fresh:%s\n' "$file" "$logic" "$parent_target"
  else
    printf '%s\tparent=%s\tcache=stale:%s\n' "$file" "$logic" "$parent_target"
  fi
}

warm_one() {
  file=$1
  parent_context "$file" warm || return $?
  parent_target=$(parent_target_for_file "$file")
  if [ "$parent_target" != none ]; then
    cache_build_target "$parent_target"
    return $?
  fi
  printf 'build parent heap: %s for %s\n' "$logic" "$file"
  timeout "$limit" "$isabelle" build \
    "${isabelle_options[@]}" \
    "${proof_options[@]}" \
    "${dirs[@]}" -b "$logic"
}

ordered_layer_files() {
  while IFS= read -r file; do
    [ -z "$file" ] && continue
    printf '%s\t%s\n' "$(layer_rank "$file")" "$file"
  done <<EOF2
$1
EOF2
}

case "${1:-quick}" in
  quick)
    files=$(dirty_layers)
    printf 'target holes:\n'
    rg -n '\bsorry\b|sledgehammer' "${hole_theories[@]}" || true
    printf '\ndirty dev34 layer files:\n'
    if [ -n "$files" ]; then
      printf '%s\n' "$files"
      target=$(auto_target "$files")
      printf '\nauto would run: %s\n' "$target"
      cache_status_line "$target"
    else
      printf '(none)\n'
      printf '\nauto would run: holes\n'
    fi
    ;;
  holes|sorries)
    exec rg -n '\bsorry\b|sledgehammer' "${hole_theories[@]}"
    ;;
  index|idx)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    exec rg -n -i -- "$*" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
    ;;
  names)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    exec rg -n -i -- "$*" THEOREMS_AND_DEFS.txt
    ;;
  stmts)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    exec rg -n -i -- "$*" STMT_INDEX.txt
    ;;
  grep|scan|search)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    exec rg -n -i -- "$*" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}"
    ;;
  loop|look)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    run_hot=0
    if [ "${1:-}" = "--hot" ]; then
      run_hot=1
      shift
    fi
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    pat=$1
    shift
    files=$(layer_files "$@")
    printf 'full-index/source scan: %s\n' "$pat"
    rg -n -i -- "$pat" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}" || true
    printf '\ntarget holes:\n'
    rg -n '\bsorry\b|sledgehammer' "${hole_theories[@]}" || true
    printf '\ndirty/hot plan:\n'
    if [ -n "$files" ]; then
      while IFS="$(printf '\t')" read -r _ file; do
        [ -z "$file" ] && continue
        plan_one "$file"
      done <<EOF2
$(ordered_layer_files "$files" | sort -n -k1,1)
EOF2
      if [ "$run_hot" = 1 ]; then
        printf '\nhot check:\n'
        "$0" hot "$@"
      else
        printf '\n(skipping hot check; use loop --hot or loop-hot when proof validation is needed)\n'
      fi
    else
      printf '(no dirty/explicit dev34 layer files)\n'
    fi
    ;;
  loop-hot)
    shift
    exec "$0" loop --hot "$@"
    ;;
  dirty)
    shift
    files=$(layer_files "$@")
    if [ -n "$files" ]; then
      printf '%s\n' "$files"
      printf '\nauto would run: %s\n' "$(auto_target "$files")"
    else
      printf '(no dirty dev34 layer files)\n'
      printf 'auto would run: holes\n'
    fi
    ;;
  plan)
    shift
    files=$(layer_files "$@")
    if [ -z "$files" ]; then
      printf '(no dirty dev34 layer files)\n'
      exit 0
    fi
    while IFS="$(printf '\t')" read -r _ file; do
      [ -z "$file" ] && continue
      plan_one "$file"
    done <<EOF2
$(ordered_layer_files "$files" | sort -n -k1,1)
EOF2
    ;;
  warm)
    shift
    files=$(layer_files "$@")
    if [ -z "$files" ]; then
      printf '(no dirty dev34 layer files)\n'
      exit 0
    fi
    status=0
    last_logic=
    while IFS="$(printf '\t')" read -r _ file; do
      [ -z "$file" ] && continue
      parent_context "$file" warm || exit $?
      if [ "$logic" = "$last_logic" ]; then
        continue
      fi
      last_logic=$logic
      if warm_one "$file"; then
        :
      else
        status=$?
        break
      fi
    done <<EOF2
$(ordered_layer_files "$files" | sort -n -k1,1)
EOF2
    exit "$status"
    ;;
  cache-plan)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    if [ "$target" = none ] && [ -z "$files" ]; then
      printf '(no dirty/explicit dev34 layer files)\n'
      exit 0
    fi
    printf 'cache target: %s\n' "$target"
    cache_plan_through "$target"
    ;;
  cache-through)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    if [ "$target" = none ] && [ -z "$files" ]; then
      printf '(no dirty/explicit dev34 layer files)\n'
      exit 0
    fi
    cache_build_through "$target"
    ;;
  cache-parents)
    shift
    files=$(layer_files "$@")
    cache_build_parents "$files"
    ;;
  proc|process|hot)
    shift
    files=$(layer_files "$@")
    if [ -z "$files" ]; then
      exec "$0" holes
    fi
    status=0
    while IFS="$(printf '\t')" read -r _ file; do
      [ -z "$file" ] && continue
      if proc_one "$file"; then
        :
      else
        status=$?
        break
      fi
    done <<EOF2
$(ordered_layer_files "$files" | sort -n -k1,1)
EOF2
    exit "$status"
    ;;
  outline)
    shift
    exec env SKIP_PROOFS=1 "$0" proc "$@"
    ;;
  split-hot)
    shift
    if [ "$#" -lt 2 ]; then
      usage
      exit 2
    fi
    file=$1
    shift
    pattern=$*
    split_hot_one "$file" "$pattern"
    ;;
  slice-hot)
    shift
    if [ "$#" -lt 2 ]; then
      usage
      exit 2
    fi
    file=$1
    shift
    pattern=$*
    DEV34_FAST_SLICE_ONLY=1 split_hot_one "$file" "$pattern"
    ;;
  split-warm)
    shift
    if [ "$#" -lt 2 ]; then
      usage
      exit 2
    fi
    file=$1
    shift
    pattern=$*
    DEV34_FAST_PREFIX_ONLY=1 split_hot_one "$file" "$pattern"
    ;;
  focus-list)
    shift
    focus_list
    ;;
  focus)
    shift
    if [ "$#" -lt 1 ]; then
      usage
      exit 2
    fi
    name=$1
    shift
    focus_one slice "$name" "$@"
    ;;
  focus-full)
    shift
    if [ "$#" -lt 1 ]; then
      usage
      exit 2
    fi
    name=$1
    shift
    focus_one full "$name" "$@"
    ;;
  focus-warm)
    shift
    if [ "$#" -lt 1 ]; then
      usage
      exit 2
    fi
    focus_one warm "$1"
    ;;
  focus-parents)
    shift
    if [ "$#" -lt 1 ]; then
      usage
      exit 2
    fi
    focus_parents_one "$1"
    ;;
  focus-warm-all)
    shift
    status=0
    while IFS= read -r name; do
      [ -n "$name" ] || continue
      printf '\n== %s ==\n' "$name"
      if focus_one warm "$name"; then
        :
      else
        status=$?
        break
      fi
    done <<EOF2
$(focus_target_names)
EOF2
    exit "$status"
    ;;
  focus-outline)
    shift
    exec env SKIP_PROOFS=1 "$0" focus "$@"
    ;;
  graph-focus|focus-graph)
    shift
    if [ "$#" -gt 0 ]; then
      printf 'full-index/source scan: %s\n' "$*"
      rg -n -i -- "$*" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}" || true
      printf '\n'
    fi
    split_hot_one "$active_graph_file" "$active_graph_pattern"
    ;;
  graph-outline|focus-graph-outline)
    shift
    exec env SKIP_PROOFS=1 "$0" graph-focus "$@"
    ;;
  graph-warm|focus-graph-warm)
    shift
    if [ "$#" -gt 0 ]; then
      printf 'full-index/source scan: %s\n' "$*"
      rg -n -i -- "$*" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}" || true
      printf '\n'
    fi
    DEV34_FAST_PREFIX_ONLY=1 split_hot_one "$active_graph_file" "$active_graph_pattern"
    ;;
  layer|exact|auto)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    if [ "$target" = dev34 ]; then
      build_dev34
    elif [ "$target" = core ]; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar -d dev34_core \
        GeoTop34CoreDirty
    elif [ "$target" = openstar ]; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar \
        GeoTop34OpenStarDirty
    elif [ "$target" = graphwork ]; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork \
        GeoTop34GraphWorkDirty
    elif [ "$target" = graphfacts ]; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        GeoTop34GraphFactsDirty
    elif [ "$target" = linkfacts ]; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts \
        GeoTop34LinkFactsDirty
    elif [ "$target" = workfacts ]; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts \
        GeoTop34WorkFactsDirty
    elif [ "$target" = facts ]; then
      exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
        "${isabelle_options[@]}" \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
        GeoTop34FactsDirty
    elif [ "$target" = prefix ]; then
      build_prefix
    elif [ "$target" = prefix-mid ]; then
      build_prefix_mid
    elif [ "$target" = prefix-graph ]; then
      build_prefix_graph
    elif [ "$target" = prefix-graph-cache ]; then
      build_prefix_graph_cache
    elif [ "$target" = prefix-base ]; then
      build_prefix_base
    elif [ "$target" = pre ]; then
      build_pre
    else
      exec "$0" holes
    fi
    ;;
  cache)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    cache_build_target "$target"
    ;;
  cache-status)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    cache_status_line "$target"
    ;;
  cache-all)
    shift
    status=0
    for target in "${layer_targets[@]}"; do
      if cache_build_target "$target"; then
        :
      else
        status=$?
        break
      fi
    done
    exit "$status"
    ;;
  cache-clean)
    shift
    rm -rf "$cache_dir"
    printf 'removed %s\n' "$cache_dir"
    ;;
  prove|proof)
    shift
    export FORCE_PROOFS=1
    exec "$0" auto "$@"
    ;;
  pre)
    build_pre
    ;;
  prefix-base)
    build_prefix_base
    ;;
  prefix-graph)
    build_prefix_graph
    ;;
  prefix-graph-cache)
    build_prefix_graph_cache
    ;;
  prefix-mid)
    build_prefix_mid
    ;;
  prefix)
    build_prefix
    ;;
  pre-heap)
    cache_build_target pre
    ;;
  prefix-heap)
    cache_build_target prefix
    ;;
  prefix-base-heap)
    cache_build_target prefix-base
    ;;
  prefix-graph-heap)
    cache_build_target prefix-graph
    ;;
  prefix-graph-cache-heap)
    cache_build_target prefix-graph-cache
    ;;
  prefix-mid-heap)
    cache_build_target prefix-mid
    ;;
  facts)
    exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      GeoTop34FactsDirty
    ;;
  facts-heap)
    cache_build_target facts
    ;;
  workfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts \
      GeoTop34WorkFactsDirty
    ;;
  workfacts-heap)
    cache_build_target workfacts
    ;;
  linkfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts \
      GeoTop34LinkFactsDirty
    ;;
  linkfacts-heap)
    cache_build_target linkfacts
    ;;
  graphfacts)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      GeoTop34GraphFactsDirty
    ;;
  graphfacts-heap)
    cache_build_target graphfacts
    ;;
  graphwork)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork \
      GeoTop34GraphWorkDirty
    ;;
  graphwork-heap)
    cache_build_target graphwork
    ;;
  openstar)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar \
      GeoTop34OpenStarDirty
    ;;
  openstar-heap)
    cache_build_target openstar
    ;;
  core)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
      "${isabelle_options[@]}" \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix_base -d dev34_prefix_graph -d dev34_prefix_mid -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar -d dev34_core \
      GeoTop34CoreDirty
    ;;
  core-heap)
    cache_build_target core
    ;;
  dev34)
    build_dev34
    ;;
  dev34-heap)
    cache_build_target dev34
    ;;
  *)
    usage
    exit 2
    ;;
esac
