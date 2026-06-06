#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

isabelle=${ISABELLE:-/project/bin/isabelle}
limit=${TIMEOUT:-120s}

case "${1:-prefix}" in
  prefix)
    exec timeout "$limit" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix \
      GeoTop34PrefixDirty
    ;;
  prefix-heap)
    exec timeout "$limit" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix \
      -b GeoTop34PrefixDirty
    ;;
  dev34)
    exec timeout "${TIMEOUT:-240s}" "$isabelle" build \
      -d . -d dev34_pre -d dev34_prefix -d dev34_facts \
      -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
      -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
      GeoTop34Dev
    ;;
  sorries)
    exec rg -n 'sorry|sledgehammer' dev34_prefix dev34_core dev34
    ;;
  *)
    echo "usage: $0 [prefix|prefix-heap|dev34|sorries]" >&2
    exit 2
    ;;
esac
