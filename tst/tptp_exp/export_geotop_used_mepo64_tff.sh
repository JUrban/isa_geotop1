#!/usr/bin/env bash
# Export GeoTop-chain TFF ATP problems using proof dependencies padded with
# up to 64 MePo-selected facts.
#
# Usage:
#   cd /project/tst
#   tptp_exp/export_geotop_used_mepo64_tff.sh [OUT_DIR]
#
# Environment:
#   GEOTOP_USED_MEPO_TPTP_LIMIT  optional target limit for quick probes, default 0 = all
#   GEOTOP_USED_MEPO_TPTP_SCOPE  geotop or all_geotop, default all_geotop

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT_DIR="${1:-$PROJECT_DIR/tptp_probs_geotop_used_mepo64}"

GEOTOP_USED_MEPO_TPTP_EXTRA_FACTS=64 \
  "$SCRIPT_DIR/export_geotop_used_mepo32_tff.sh" "$OUT_DIR"
