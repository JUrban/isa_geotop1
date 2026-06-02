# GeoTop Formalization Report Through Section 2

Date: 2026-06-02

This report summarizes the current formalization status for the material through
the end of Section 2 of `geotop.tex`, and records the Isabelle counterparts of
the book theorems.

## Status

The initial GeoTop material through the end of Section 2 is recursively
sorry-free in the active formalization.

Evidence checked locally:

- `GeoTop.thy` marks the start of Section 3+ at `CHUNK_OUT_3PLUS_START`, line
  23590.
- A scan of `GeoTop.thy` before that boundary finds no executable `sorry`;
  the only matches before the boundary are in explanatory comments.
- The first executable `sorry`s in `GeoTop.thy` are after the Section 3+
  boundary.
- `ROOT` has `quick_and_dirty` only on the `GeoTop` session; non-`GeoTop`
  sessions are clean-session builds.
- `/project/bin/isabelle build -d . AlgTop` passed.
- `/project/bin/isabelle build -d . GeoTopPrefix` passed, including a clean
  rebuild of `GeoTopDeps`.

The practical consequence is that Sections 1 and 2 can now be treated as a
clean cached base. Later sections of `GeoTop.thy` still contain intentional
proof sketches with `sorry`, so the full `GeoTop` session still retains
`quick_and_dirty`.

## Layout

The formalization is split across sessions:

- Section 1 connectivity results are in `gb/GeoTopBase.thy`.
- Section 2 polygon-complement infrastructure is split between
  `gp/GeoTop_Prefix.thy` and `GeoTop.thy`.
- `GeoTopPrefix` is the clean prefix session that caches the recursively
  sorry-free material needed before Section 3.

## Section 1 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 1.1 | Union of pathwise connected sets with a common point is pathwise connected. | `Theorem_GT_1_1` | `gb/GeoTopBase.thy` |
| Theorem 1.2 | Pathwise connectivity is preserved by surjective mappings. | `Theorem_GT_1_2` | `gb/GeoTopBase.thy` |
| Theorem 1.3 | Every simplex is pathwise connected. | `Theorem_GT_1_3` | `gb/GeoTopBase.thy` |
| Theorem 1.4 | If a complex `K` is connected, then `|K|` is pathwise connected. | `Theorem_GT_1_4` | `gb/GeoTopBase.thy` |
| Theorem 1.5 | For `M = H union K`, separatedness is equivalent to both sides being open in the subspace and disjoint. | `Theorem_GT_1_5` | `gb/GeoTopBase.thy` |
| Theorem 1.6 | A set is connected iff it is not a union of two nonempty separated sets. | `Theorem_GT_1_6` | `gb/GeoTopBase.thy` |
| Theorem 1.7 | Connectivity of spaces is preserved by surjective mappings. | `Theorem_GT_1_7` | `gb/GeoTopBase.thy` |
| Theorem 1.8 | Connectivity of subsets is preserved by surjective mappings. | `Theorem_GT_1_8` | `gb/GeoTopBase.thy` |
| Theorem 1.9 | Every closed interval in `R` is connected. | `Theorem_GT_1_9` | `gb/GeoTopBase.thy` |
| Theorem 1.10 | A connected subset of a union of two separated sets lies in one side. | `Theorem_GT_1_10` | `gb/GeoTopBase.thy` |
| Theorem 1.11 | Every pathwise connected set is connected. | `Theorem_GT_1_11` | `gb/GeoTopBase.thy` |
| Theorem 1.12 | For a complex `K`, combinatorial connectedness, pathwise connectedness of `|K|`, and connectedness of `|K|` are equivalent. | `Theorem_GT_1_12` | `gb/GeoTopBase.thy` |
| Theorem 1.13 | Every connected open set in Euclidean space is broken-line-wise connected. | `Theorem_GT_1_13` | `gb/GeoTopBase.thy` |
| Theorem 1.14 | Union of connected sets with a common point is connected. | `Theorem_GT_1_14` | `gb/GeoTopBase.thy` |
| Theorem 1.15 | If `M` is connected and `M subset L subset closure M`, then `L` is connected. | `Theorem_GT_1_15` | `gb/GeoTopBase.thy` |
| Theorem 1.16 | Distinct components of the same set are disjoint. | `Theorem_GT_1_16` | `gb/GeoTopBase.thy` |
| Theorem 1.17 | If `M subset N`, then every component of `M` lies in a component of `N`. | `Theorem_GT_1_17` | `gb/GeoTopBase.thy` |

## Section 2 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 2.1 | If `J` is a polygon in `R^2`, then `R^2 - J` has exactly two components. | `Theorem_GT_2_1`; supporting `Lemma_GT_2_1a`, `Lemma_GT_2_1b` | `gp/GeoTop_Prefix.thy` |
| Theorem 2.2 | The closure of the polygon interior is a finite polyhedron. | `Theorem_GT_2_2` | `GeoTop.thy` |
| Theorem 2.3 | No broken line separates `R^2`. | `Theorem_GT_2_3` | `gp/GeoTop_Prefix.thy` |
| Theorem 2.4 | For an open set `U`, `Fr U = closure U - U`. | `Theorem_GT_2_4` | `gp/GeoTop_Prefix.thy` |
| Theorem 2.5 | Every point of a polygon is a limit point of both its interior and exterior. | `Theorem_GT_2_5` | `gp/GeoTop_Prefix.thy` |
| Theorem 2.6 | For polygon `J` with interior `I` and exterior `E`, `J = Fr I = Fr E`. | `Theorem_GT_2_6` | `gp/GeoTop_Prefix.thy` |
| Theorem 2.7 | For a polyhedral theta graph, every complement component has a pair-polygon as frontier, and exactly one arc is the middle arc. | `Theorem_GT_2_7` | `GeoTop.thy` |
| Theorem 2.8 | If the middle arc lies inside the pair-polygon, then it cuts that interior into the two adjacent polygon interiors, with the stated closure and separation properties. | `Theorem_GT_2_8` | `GeoTop.thy` |

## Important Supporting Material

The main Section 2 theorems rely on a substantial clean support layer. The most
important named helpers include:

- `geotop_polygon_components_set_eq`, `polygon_components_card`,
  `polygon_components_eq`
- `geotop_polygon_interior`, `geotop_polygon_exterior`
- `polygon_interior_is_HOL_component`, `polygon_exterior_is_HOL_component`
- `polygon_interior_unique`, `polygon_exterior_unique`
- `geotop_polygon_finite_triangulation`
- `geotop_is_theta_graph`, `geotop_is_polyhedral_theta_graph`
- `theta_graph_pair_is_polygon`, `theta_graph_M_decomposition`
- `theta_graph_complement_has_two_components`
- `theta_graph_unique_unbounded_component`
- `theta_arc_in_one_side_of_pair_polygon`
- `theta_middle_arc_unique_excludes_3`
- `gt28_closures_helper`, `gt28_separated_helper`

## Notes For Future Work

- Section 3 starts at `CHUNK_OUT_3PLUS_START` in `GeoTop.thy`; executable
  `sorry`s resume there.
- The clean `GeoTopPrefix` session should be used as the cached base for future
  work so Section 1 and Section 2 do not need to be rechecked through the full
  later-section `GeoTop` script.
- If new theorems are added to the clean prefix, regenerate `THEOREMS_AND_DEFS.txt`
  and `STMT_INDEX.txt` using the scripts described in `CLAUDE.md`.
