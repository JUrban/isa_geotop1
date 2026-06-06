#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

isabelle=${ISABELLE:-/project/bin/isabelle}
limit=${TIMEOUT:-90s}

usage() {
  cat >&2 <<'EOF'
usage: ./check_dev34_fast.sh MODE [ARGS...]

Fast modes:
  holes        rg for target sorry/sledgehammer markers
  index PAT    rg PAT in THEOREMS_AND_DEFS.txt and STMT_INDEX.txt
  auto         build the smallest dirty dev34 layer detected by git diff

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
    -d . -d dev34_pre \
    GeoTopPre3Dirty
}

build_prefix() {
  exec timeout "$limit" "$isabelle" build \
    -d . -d dev34_pre -d dev34_prefix \
    GeoTop34PrefixDirty
}

build_dev34() {
  exec timeout "${TIMEOUT:-240s}" "$isabelle" build \
    -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
    -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
    -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
    GeoTop34Dev
}

dirty_layers() {
  git diff --name-only -- \
    dev34_pre dev34_prefix dev34_facts dev34_workfacts dev34_linkfacts \
    dev34_graphfacts dev34_graphwork dev34_openstar dev34_core dev34
}

case "${1:-prefix}" in
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
  auto)
    files=$(dirty_layers)
    if printf '%s\n' "$files" | rg -q '^dev34/'; then
      build_dev34
    elif printf '%s\n' "$files" | rg -q '^dev34_core/'; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar -d dev34_core \
        GeoTop34CoreDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_openstar/'; then
      exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork -d dev34_openstar \
        GeoTop34OpenStarDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_graphwork/'; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        -d dev34_graphwork \
        GeoTop34GraphWorkDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_graphfacts/'; then
      exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
        GeoTop34GraphFactsDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_linkfacts/'; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts -d dev34_linkfacts \
        GeoTop34LinkFactsDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_workfacts/'; then
      exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        -d dev34_workfacts \
        GeoTop34WorkFactsDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_facts/'; then
      exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
        -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
        GeoTop34FactsDirty
    elif printf '%s\n' "$files" | rg -q '^dev34_prefix/'; then
      build_prefix
    elif printf '%s\n' "$files" | rg -q '^dev34_pre/'; then
      build_pre
    else
      exec "$0" holes
    fi
    ;;
  pre)
    build_pre
    ;;
  prefix)
    build_prefix
    ;;
  prefix-heap)
    exec timeout "$limit" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix \
      -b GeoTop34PrefixDirty
    ;;
  facts)
    exec timeout "${TIMEOUT:-120s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      GeoTop34FactsDirty
    ;;
  workfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts \
      GeoTop34WorkFactsDirty
    ;;
  linkfacts)
    exec timeout "${TIMEOUT:-150s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts \
      GeoTop34LinkFactsDirty
    ;;
  graphfacts)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      GeoTop34GraphFactsDirty
    ;;
  graphwork)
    exec timeout "${TIMEOUT:-180s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork \
      GeoTop34GraphWorkDirty
    ;;
  openstar)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar \
      GeoTop34OpenStarDirty
    ;;
  core)
    exec timeout "${TIMEOUT:-210s}" "$isabelle" build \
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
