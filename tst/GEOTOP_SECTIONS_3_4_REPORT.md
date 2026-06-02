# GeoTop Formalization Report for Sections 3 and 4

Date: 2026-06-02

This report summarizes the current formalization status for Sections 3 and 4
of `geotop.tex`, and records the Isabelle counterparts of the book theorems.

## Status

Sections 3 and 4 are not yet sorry-free. They are isolated in a fast cached
development stack, and the current active session has a successful warm-cache
build.

Evidence checked locally:

- A pull/fetch of colleague `main` over HTTPS left `https/main` at commit
  `3e463c3b` (`Document GeoTop sections 1 and 2 status`).
- Our branch `codex-dev34-cache` already contains all of `https/main`;
  `git rev-list --left-right --count HEAD...https/main` reports `224 0`, so
  no merge was needed for this report update.
- The latest successful section build on this branch was:
  `/project/bin/isabelle build -d . -d dev34_pre -d dev34_prefix -d dev34_facts
  -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork
  -d dev34_openstar -d dev34 GeoTop34Dev`.
- That build passed for the state committed as `ce1df618`
  (`Decompose GeoTop one-sided chart lemma`); the final `GeoTop34Dev`
  theory took about `0:00:09` elapsed, with about `0:00:29` elapsed overall.
- A scan of the target section-specific theories, excluding the intentionally
  dirty `dev34_pre/GeoTop.thy` mirror, finds 15 remaining executable `sorry`s:
  9 in `dev34_prefix/GeoTop_3_4_Prefix.thy` and 6 in
  `dev34/GeoTop_3_4.thy`.

The practical consequence is that Sections 3 and 4 have a working, green
development session, but completion still requires eliminating the listed proof
holes. The main open cluster is now radial cone openness for the link endpoint
projection, the cone-over-link bridge, the edge-incidence chart contradictions,
the boundary equality part of Theorem 4.9, and several larger Section 3/early
Section 4 prefix arguments.

## Layout

The section 3-4 development is split across cached sessions:

- `dev34_pre/GeoTop.thy`: dirty cached import of the original `GeoTop` script;
  it still contains the original later-section sketches and is not used as the
  target sorry count for Sections 3 and 4.
- `dev34_prefix/GeoTop_3_4_Prefix.thy`: Section 3 and early Section 4
  statements and proofs.
- `dev34_facts/GeoTop_3_4_Facts.thy`: Section 4 Jordan-curve facts and local
  manifold helpers.
- `dev34_workfacts`, `dev34_linkfacts`, `dev34_graphfacts`,
  `dev34_graphwork`, and `dev34_openstar`: supporting cached work for links,
  graph/edge facts, and open-star neighborhoods.
- `dev34/GeoTop_3_4.thy`: active Section 4 manifold/star work and the final
  layer of the section-specific stack; it currently contains 6 executable
  `sorry`s.

## Section 3 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 3.1 | Simplexes with matched vertex sets admit a simplicial homeomorphism carrying each vertex to its assigned image. | `Theorem_GT_3_1` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.2 | In the equal-dimensional case, the simplex homeomorphism extends to a homeomorphism of the whole Euclidean space. | `Theorem_GT_3_2` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.3 | A triangulated polygonal disk with more than one 2-simplex has a free 2-simplex. | `Theorem_GT_3_3` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.4 | Every polygon in `R^2` is carried by a plane homeomorphism to the frontier of a 2-simplex. | `Theorem_GT_3_4` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.5 | Any two polygons in `R^2` are equivalent by a plane homeomorphism. | `Theorem_GT_3_5` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.6 | A polygon bounds a topological 2-cell. | `Theorem_GT_3_6` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.7 | The polygon-to-simplex homeomorphism can be chosen fixed outside a prescribed open neighborhood of the polygonal disk. | `Theorem_GT_3_7` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |

## Section 4 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 4.1 | Distinct components of an open Euclidean set are separated by disjoint open subsets containing the chosen points. | `Theorem_GT_4_1` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.2 | An arc across a polygonal disk separates the polygon interior into the two expected open sides. | `Theorem_GT_4_2` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.3 | A topological 1-sphere in `R^2` separates the plane. | `Theorem_GT_4_3` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.4 | Two disjoint arcs from opposite boundary points of a polygonal disk leave `Q` and `S` in the frontier of the same component. | `Theorem_GT_4_4` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.5 | No arc separates `R^2`. | `Theorem_GT_4_5` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.6 | For a 1-sphere `J` and a component `U` of `R^2 - J`, the frontier of `U` is `J`. | `Theorem_GT_4_6` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.7 | A 1-sphere in `R^2` has exactly one bounded complement component. | `Theorem_GT_4_7` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.8 | If the underlying polyhedron of `K` is a 2-manifold, then every vertex star of `K` is a combinatorial 2-cell. | `Theorem_GT_4_8` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.9 | If the underlying polyhedron of `K` is a 2-manifold with boundary, then every vertex star is a combinatorial 2-cell and the manifold boundary is the union of edges incident to exactly one 2-simplex. | `Theorem_GT_4_9` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.10 | For a closed 2-manifold with boundary in `R^2`, the manifold boundary equals the topological frontier. | `Theorem_GT_4_10` | `dev34/GeoTop_3_4.thy` |

## Current Open Proof Holes

The remaining target holes in `dev34_prefix/GeoTop_3_4_Prefix.thy` are:

- `Theorem_GT_3_3`: induction/strong free-simplex claim at line 844.
- `Theorem_GT_3_4`: base case and induction step for reducing a polygonal disk
  to one 2-simplex at lines 892 and 905.
- `Theorem_GT_4_2`: final arc-separation disjointness/decomposition step at
  line 1715.
- `Theorem_GT_4_4`: brick-decomposition and frontier-component construction
  steps at lines 1810, 1818, 1828, 1839, and 1849.

The remaining target holes in `dev34/GeoTop_3_4.thy` are:

- `geotop_link_open_radial_cone_open_in_punctured_star_dev34` at line 117.
- `geotop_vertex_star_cone_equiv_from_link_line_or_polygon_dev34` at line
  1223.
- The semicircle-separation subclaim inside
  `geotop_unique_incident_2simplex_semicircle_separates_chart_dev34` at line
  1306.
- `geotop_three_incident_2simplex_sphere_not_separates_chart_dev34` at line
  1333.
- `geotop_boundary_chart_three_incident_2simplex_contradiction_dev34` at line
  1356.
- The boundary equality half of `Theorem_GT_4_9` at line 3110.

## Recent Progress

The active file now contains proved bridge lemmas for the book Lemma 5 route:

- `geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34`
- `geotop_link_radial_segment_in_star_dev34`
- `geotop_link_point_ne_vertex_dev34`
- `geotop_radial_point_ne_vertex_dev34`
- `geotop_link_radial_tail_in_punctured_star_dev34`
- `geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34`
- `geotop_2_manifold_open_subset_connected_punctured_neighborhood_dev34`
- `geotop_2_manifold_with_boundary_open_subset_connected_punctured_neighborhood_dev34`
- `geotop_2_manifold_vertex_star_punctured_connected_dev34`
- `geotop_2_manifold_with_boundary_vertex_star_punctured_connected_dev34`
- `geotop_punctured_star_radial_endpoint_choice_property_dev34`
- `geotop_radial_endpoint_choice_preimage_eq_cone_dev34`
- `geotop_punctured_star_radial_endpoint_projection_dev34`
- `geotop_openin_norm_polyhedron_contains_relative_ball_dev34`

These formalize the radial and local connected-neighborhood parts of Moise's
Lemma 5 argument: a separation side of the punctured vertex star accumulates at
the vertex, while a manifold chart supplies a connected punctured neighborhood
inside the open star, contradicting such a separation. The radial endpoint
projection is now proved from an explicit cone-openness subclaim.

The chart-local Section 4 statements have also been audited against the book
argument. The edge-incidence contradiction helpers now carry the local
`openin_on` chart-neighborhood hypothesis, and the one-sided chart lemma has
been decomposed so that its remaining hole is the explicit semicircle
separation construction inside that local neighborhood.

## Important Supporting Material

Important cached helpers include:

- `geotop_complex_vertex_star_neighborhood_dev34`
- `geotop_open_star_open_in_subspace_locally_finite_dev34`
- `geotop_star_punctured_point_radial_to_link_dev34`
- `geotop_link_radial_endpoint_unique_dev34`
- `geotop_link_polyhedron_subset_punctured_star_polyhedron`
- `geotop_star_polyhedron_subset_polyhedron`
- `geotop_plane_chart_open_subset_connected_punctured_neighborhood`
- `geotop_plane_chart_point_complement_connected`
- `geotop_2_cell_open_subset_connected_punctured_neighborhood`
- `geotop_2_manifold_no_open_edge_rel_interior`
- `geotop_2_manifold_with_boundary_no_open_edge_rel_interior`
- `geotop_2_manifold_no_open_singleton`
- `geotop_2_manifold_with_boundary_no_open_singleton`

## Notes For Future Work

- The next book-aligned bottleneck for Theorems 4.8 and 4.9 is
  `geotop_link_open_radial_cone_open_in_punctured_star_dev34`, because it is
  the remaining geometric openness subclaim needed by the radial endpoint
  projection.
- After link connectedness is fully established, the cone-over-link bridge at
  line 1223 should be the next bottleneck for turning link shape into
  `geotop_comb_n_cell (geotop_star K v) 2`.
- The local chart contradiction lemmas at lines 1306, 1333, and 1356 now have
  the needed local-open-neighborhood hypothesis. The next step there is to
  formalize the book's small semicircle/small circle constructions in the
  chart.
- The prefix holes in Theorems 3.3, 3.4, 4.2, and 4.4 remain larger book-level
  arguments and should be attacked with the `sorry`-first skeleton workflow
  from `CLAUDE.md`.
- Keep using the cached `GeoTop34Dev` build command from `CLAUDE.md` and the
  development notes; warm-cache final theory time is currently about 10
  seconds.
- If more named helpers are added, regenerate `THEOREMS_AND_DEFS.txt` and
  `STMT_INDEX.txt`.
