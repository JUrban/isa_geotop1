# GeoTop Sections 3-4 Cycle Realization Checkpoint

Date: 2026-06-09

## Status

The active Figure 4.10 boundary-cycle target package is now closed:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The focused check passed:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
```

The target hole scan now reports 7 remaining `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34/GeoTop_3_4.thy:12872
dev34/GeoTop_3_4.thy:14090
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

## What Closed It

The proof now uses the oriented successor cycle on the source graph and the oriented successor cycle on the constructed target boundary subdivision.

The key bridge is the successor-index vertex map:

```text
source successor vertex at index j  |->  target successor vertex at index j
```

The proof establishes:

```text
source successor vertex projection is injective on the period
target successor vertex projection is injective on the period
source and target successor periods match
the induced vertex map is a bijection
the induced target listing has the right vertex image
source listed edges map onto exactly the target successor edge set
the induced listing satisfies geotop_standard_boundary_cycle_listing_data_dev34
```

This follows the expert3/book advice: use the target successor orbit as the ordered boundary cycle instead of the earlier arbitrary boundary vertex list.

## Next Best Target

Reuse the same ordered listing machinery for:

```text
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
```

The remaining non-graph packages are still substantial: branch-vertex local cutpoint, Section 3 subdisk/fold packages, D42 arc separation, D44 brick transfer, and the one-sided semicircle separator.
