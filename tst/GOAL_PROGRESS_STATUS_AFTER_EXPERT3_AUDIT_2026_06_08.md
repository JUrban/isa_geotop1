# GeoTop Sections 3-4 Progress Status After Expert3 Audit, 2026-06-08

## Status

The zero-sorry goal is not complete.

I refreshed `CLAUDE.md`, reread the expert audit files
`PLAN_zero_sorry-expert.md` through `PLAN_zero_sorry-expert3.md`, and checked
the current local target state. A fresh `./check_dev34_fast.sh holes` reports 8
visible target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:1586
dev34/GeoTop_3_4.thy:9662
dev34/GeoTop_3_4.thy:10864
```

A marker scan over the checked target layers found no visible `sledgehammer` or
`try0` calls. I did not run a full Isabelle session build for this report.

## Stable Open Packages

The current 8 open packages are stable by theorem name:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

Line numbers have drifted between reports, but the package names match the
post-audit state. The branch is structurally much closer than the older
17-sorry reports, but it is not in a "routine tactic cleanup" phase.

## Progress Assessment

The project is approaching the goal structurally: the remaining work is isolated
into named packages, focused checker targets exist, and the full indexes are
usable for frequent whole-project grep. Recent work has narrowed Figure 4.10
substantially: source singleton/edge cases, source cardinal decompositions, and
seed boundary-subdivision facts are now staged inside the active target
realization proof.

The remaining Figure 4.10 hole is now the target construction: upgrade the
standard boundary seed subdivision into an exact cyclic listing with the needed
periodic map and source-target bijection. This is real geometric/combinatorial
work, but it is narrower than the earlier isomorphism/source-case problem.

The graph-prefix cycle split identified in earlier audits is no longer the main
blocker. The remaining graph-cache hole is the branch-vertex local cutpoint
bridge: turn the connected punctured graph data into a local component touching
all three selected edge germs, then use the already staged local radial-sector
contradiction.

Expert3's most important correction is the one-sided semicircle package. The
current low-level radius lemma is under-assumed: it uses data at radius `r` while
placing the crosscut on `sphere p r`, so the arc need not be contained in `U`
and `U` may reconnect outside the small ball. The wrapper already has the right
collar data with `0 < r`, `r < s`, local equality on `ball p s`, and
`geotop_polyhedron K ∩ ball p s ⊆ U`. The low-level theorem should be changed
to that collar form before proof effort is spent there.

The Section 3 and Section 4 prefix holes remain package-sized Moise arguments:
subdisk induction transfer, support-controlled free-triangle fold
normalization, D42 theta/arc separation, and D44 brick/regular-neighborhood
transfer. These should not be treated as one-line proof holes.

## Speed And Indexing

The current iteration path should be:

```bash
rg "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
./check_dev34_fast.sh focus <target>
./check_dev34_fast.sh holes
rg -n "sledgehammer|try0" dev34/GeoTop_3_4.thy dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34_prefix_graph/cache dev34_core
```

The index scripts already include local advice/report/status files and bounded
session transcript inputs through `index_theory_lib.py`. This new report uses a
`*PROGRESS*.md` name, so it is covered by the existing advice-file patterns. I
do not see a script change needed unless future session files use names outside
the existing `*.cast`, `*.cast.gz`, `isa*.jsonl`, `session*.jsonl`,
`*transcript*.jsonl`, `*conversation*.jsonl`, or `codex*.jsonl` patterns.

## Recommended Next Moves

1. Fix the semicircle statement shape before attempting that proof: replace the
   under-assumed radius-level crosscut lemma by the collar version and let the
   wrapper pass its existing `s`-radius assumptions.
2. Continue the Figure 4.10 target construction using the existing boundary
   subdivision seed and the proved source cases.
3. Reuse the same listing/subdivision machinery for the endpoint boundary-arc
   fan package.
4. Keep D44, D42, Section 3 subdisk transfer, and Section 3 fold normalization
   as separate proof packages with named helper lemmas.

Progress should be measured by closing these 8 named packages, not by moving
the `sorry`s to deeper wrappers.
