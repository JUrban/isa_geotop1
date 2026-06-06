#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

isabelle=${ISABELLE:-/project/bin/isabelle}
limit=${TIMEOUT:-90s}
proof_options=()
if [ "${FORCE_PROOFS:-0}" = 1 ]; then
  proof_options=(-o skip_proofs=false)
fi

usage() {
  cat >&2 <<'EOF'
usage: ./check_dev34_fast.sh MODE [ARGS...]

Fast modes:
  quick        no-build snapshot: target holes plus dirty dev34 layers (default)
  holes        rg for target sorry/sledgehammer markers
  index PAT    rg PAT in THEOREMS_AND_DEFS.txt and STMT_INDEX.txt
  names PAT    rg PAT in THEOREMS_AND_DEFS.txt only
  stmts PAT    rg PAT in STMT_INDEX.txt only
  grep PAT     rg PAT in target dev34 theories and indexes
  dirty [FILES] show dirty/explicit dev34 layer files and the auto build target
  auto [FILES]  build the smallest dirty/explicit dev34 layer detected
  prove [FILES] build the smallest dirty/explicit dev34 layer with proofs forced

Build modes:
  pre          build GeoTopPre3Dirty
  prefix       build GeoTop34PrefixDirty
  prefix-heap  build and store GeoTop34PrefixDirty heap
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
    "${proof_options[@]}" \
    -d . -d dev34_pre \
    GeoTopPre3Dirty
}

build_prefix() {
  exec timeout "$limit" "$isabelle" build \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix \
    GeoTop34PrefixDirty
}

build_dev34() {
  exec timeout "${TIMEOUT:-240s}" "$isabelle" build \
    "${proof_options[@]}" \
    -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
    -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
    -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
    GeoTop34Dev
}

dirty_layers() {
  git diff --relative --name-only HEAD -- \
    dev34_pre dev34_prefix dev34_facts dev34_workfacts dev34_linkfacts \
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
  elif printf '%s\n' "$files" | rg -q '^dev34_pre/'; then
    printf '%s\n' pre
  else
    printf '%s\n' none
  fi
}

target_theories=(
  dev34_pre/GeoTop.thy
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

case "${1:-quick}" in
  quick)
    files=$(dirty_layers)
    printf 'target holes:\n'
    rg -n '\bsorry\b|sledgehammer' dev34_prefix dev34_core dev34 || true
    printf '\ndirty dev34 layer files:\n'
    if [ -n "$files" ]; then
      printf '%s\n' "$files"
      printf '\nauto would run: %s\n' "$(auto_target "$files")"
    else
      printf '(none)\n'
      printf '\nauto would run: holes\n'
    fi
    ;;
  holes|sorries)
    exec rg -n '\bsorry\b|sledgehammer' dev34_prefix dev34_core dev34
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
  grep)
    shift
    if [ "$#" -eq 0 ]; then
      usage
      exit 2
    fi
    exec rg -n -i -- "$*" THEOREMS_AND_DEFS.txt STMT_INDEX.txt "${target_theories[@]}"
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
  auto)
    shift
    files=$(layer_files "$@")
    target=$(auto_target "$files")
    if [ "$target" = dev34 ]; then
      build_dev34
    elif [ "$target" = core ]; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar -d dev34_core \
        GeoTop34CoreDirty
    elif [ "$target" = openstar ]; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar \
        GeoTop34OpenStarDirty
    elif [ "$target" = graphwork ]; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork \
        GeoTop34GraphWorkDirty
    elif [ "$target" = graphfacts ]; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        GeoTop34GraphFactsDirty
    elif [ "$target" = linkfacts ]; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts \
        GeoTop34LinkFactsDirty
    elif [ "$target" = workfacts ]; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts \
        GeoTop34WorkFactsDirty
    elif [ "$target" = facts ]; then
      exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
        "${proof_options[@]}" \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        GeoTop34FactsDirty
    elif [ "$target" = prefix ]; then
      build_prefix
    elif [ "$target" = pre ]; then
      build_pre
    else
      exec "$0" holes
    fi
    ;;
  prove|proof)
    shift
    export FORCE_PROOFS=1
    exec "$0" auto "$@"
    ;;
  pre)
    build_pre
    ;;
  prefix)
    build_prefix
    ;;
  prefix-heap)
    exec timeout "$limit" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix \
      -b GeoTop34PrefixDirty
    ;;
  facts)
    exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      GeoTop34FactsDirty
    ;;
  workfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts \
      GeoTop34WorkFactsDirty
    ;;
  linkfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts \
      GeoTop34LinkFactsDirty
    ;;
  graphfacts)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      GeoTop34GraphFactsDirty
    ;;
  graphwork)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork \
      GeoTop34GraphWorkDirty
    ;;
  openstar)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar \
      GeoTop34OpenStarDirty
    ;;
  core)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
      "${proof_options[@]}" \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar -d dev34_core \
      GeoTop34CoreDirty
    ;;
  dev34)
    build_dev34
    ;;
  *)
    usage
    exit 2
    ;;
esac
