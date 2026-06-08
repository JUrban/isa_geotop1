# Updated GeoTop / Moise Sections 3–4 report for `codex-dev34-cache`

I re-inspected the current pushed branch and the June 8 progress/status reports, especially `GOAL_PROGRESS_STATUS_2026_06_08.md`, `GOAL_PROGRESS_CURRENT_REPORT_2026_06_08.md`, `GOAL_PROGRESS_POST_AUDIT_REPORT_2026_06_08.md`, `GOAL_PROGRESS_BRIEF_2026_06_08.md`, and `GOAL_STATUS_2026_06_08.md`. I did **not** run Isabelle locally, so I cannot independently certify the build; this report is based on the repository contents and the worker’s checked status files.

## 1. Executive assessment

The project has made real progress. The best current summary is:

> The target is down to **8 verified `sorry`s**, with no visible `sledgehammer` or `try0` markers in the checked target layers, but the remaining holes are still **package-sized Moise picture arguments**, not routine tactic cleanup.

The June 8 reports consistently say the zero-`sorry` goal is not complete and list 8 remaining target holes. The exact line numbers drift between reports because the active files have continued to move, but the named packages are stable: D44 brick/regular-neighborhood transfer, Section 3 subdisk transfer, Section 3 fold normalization, D42 theta/arc separation, graph branch local cutpoint, Figure 4.10 boundary-cycle subdivision, endpoint-chain boundary-arc fan realization, and one-sided semicircle separation. ([GitHub][1])

The most important positive change since the previous review is that `tst/dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy` now appears to have **no raw `sorry`**. The earlier open cycle-split facts about non-adjacent reversed orbit edges and two cut path carriers meeting only at `P,Q` are now filled in that file. ([GitHub][2])

That changes the strategic picture. Previously, the finite graph sprint included the graph-prefix cycle split. Now the remaining finite graph sprint is narrower:

1. close the **branch-vertex local cutpoint** cache package;
2. close the active **Figure 4.10 cyclic boundary-subdivision model**;
3. reuse the same listing/subdivision machinery for the **endpoint-chain boundary-arc fan** package.

The worker’s status reports are right that the project is structurally close but not temporally “almost done.” The remaining 8 holes are few in number, but several are whole book arguments compressed into one `sorry`. ([GitHub][3])

---

## 2. What has improved recently

### 2.1 The graph-prefix cycle split is no longer an open target

The old two holes in `dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy` were around `horbit_no_nonadjacent_reversed_book` and `hpoly_inter_subset_book`. The current raw file has no `sorry`, and the corresponding proof bodies are now present: the non-adjacent reverse exclusions are proved, the edge-index intersection is handled, and the carrier intersection is reduced through simplex-intersection/face-closure facts to `{P,Q}`. ([GitHub][2])

This is meaningful progress. It means the active Figure 4.10 problem no longer has to wait for the abstract cycle-cut proof. The remaining issue is the **standard-boundary realization**, not the cycle-order split.

### 2.2 The endpoint fan target was corrected

The reports say the endpoint fan package was retargeted to a **boundary-arc fan**, rather than an incorrect full boundary-cycle isomorphism. That is an important statement-shape fix, not merely a proof edit. ([GitHub][1])

This matters because a finite graph with an endpoint is path-like, not cycle-like. Forcing it to realize the whole triangle boundary would create artificial obligations and likely false or awkward statements. The current target is now the correct path analogue of Figure 4.10.

### 2.3 Figure 4.10 has new helper infrastructure

The post-audit report says recent commits added helpers for boundary subdivision: one helper puts finitely many boundary points into a finite 1-complex with the same boundary carrier, and another produces a finite subdivision of the 2-simplex boundary with prescribed boundary points as vertices. The latest named helper is `geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34`. ([GitHub][4])

The active file confirms this helper exists. Its statement says, for a 2-simplex boundary and a finite set of points lying in that boundary polyhedron, there is a subdivision `F` of the boundary complex such that the prescribed points are vertices and the original boundary vertices are preserved. ([GitHub][5])

The remaining problem is not lack of any boundary-subdivision infrastructure. It is connecting that infrastructure to the **cyclic listing/isomorphism** theorem in the right theory order.

### 2.4 The focused checker workflow is now central

The branch now has focused layers: `dev34_prefix_base`, `dev34_prefix_graph/cache`, `dev34_prefix_graph`, `dev34_prefix_mid`, `dev34_prefix`, and active `dev34`, among other later support layers. The `tst` directory listing confirms this split. ([GitHub][6])

The checker script supports hole scans, index/name searches, focused warm/prime/status modes, split/slice hot modes, and individual dirty-layer builds. The reports also say the current focus status makes `dev34-cycle-realization` and `dev34-fan` relatively hot, while the graph long slice and semicircle slice may need targeted refreshes. ([GitHub][7])

This is a real process improvement. The worker should now avoid broad builds for every edit and iterate on one named package at a time.

---

## 3. Current 8-hole map

The most useful current list is by **stable theorem/package name**, not line number. The June 8 brief gives the exact open named packages: ([GitHub][8])

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

Grouped by mathematical content, these are:

| Package                      |     File layer | Mathematical content                                                 |                               Risk |
| ---------------------------- | -------------: | -------------------------------------------------------------------- | ---------------------------------: |
| Branch vertex local cutpoint |    graph cache | finite linear graph + simple closed curve local branch contradiction |                        medium/high |
| Figure 4.10 boundary cycle   | active `dev34` | cyclic listing to standard 2-simplex boundary subdivision            |                             medium |
| Endpoint fan                 | active `dev34` | endpoint chain to boundary-arc fan                                   |                             medium |
| One-sided semicircle         | active `dev34` | local Euclidean crosscut separation                                  | medium, but statement hygiene risk |
| Section 3 subdisk transfer   |     mid prefix | chord subdisk induction/free-triangle transfer                       |                               high |
| Section 3 fold normalization |     mid prefix | support-controlled free-triangle fold induction                      |                               high |
| Theorem 4.2                  |     mid prefix | opposite boundary arc decomposition via theta contradiction          |                               high |
| Theorem 4.4                  |   final prefix | brick/regular-neighborhood/component transfer                        |                          very high |

The remaining work should therefore be measured by **closed packages**, not by moving `sorry`s deeper into wrappers. The current reports explicitly make the same point. ([GitHub][9])

---

## 4. Best next sprint: finite graph and Figure 4.10

I agree with the worker’s report that the best next milestone is still the finite-graph/Figure 4.10 sprint. But the reason has changed slightly: the graph-prefix split is now done, so the sprint should concentrate on the **branch cutpoint cache hole**, the **standard boundary subdivision model**, and then the **endpoint fan**.

### 4.1 Branch vertex local cutpoint

The remaining graph-cache hole is `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`. The raw cache file shows the missing internal step as a local-star bridge: from the connected split-side package, one must obtain a component of `ball w r - (e₁ ∪ e₂ ∪ e₃)` whose closure meets all three selected incident edge germs. Immediately after that, the file already has a radial-sector/cardinality contradiction saying no such local component can meet all three selected germs. ([GitHub][10])

That means the worker should **not** restart the whole branch-vertex proof. The hard local contradiction is already mostly staged. The exact missing lemma should be:

```isabelle
connected_punctured_graph_three_germs_yields_local_component_touching_all:
  assumes "top1_connected_on (geotop_polyhedron L - {w}) ..."
      and "small star ball around w contains exactly the selected incident germs"
      and "e1,e2,e3 are distinct incident edges at w"
  shows "∃C S T U.
          C ∈ components (ball w r - (e1 ∪ e2 ∪ e3)) ∧
          {S,T,U} = {e1,e2,e3} ∧
          each selected germ touches closure C"
```

Then the existing `hno_local_component_meets_selected_three_edges` should finish the contradiction.

The conceptual proof should be:

1. Pick small points `x₁,x₂,x₃` on the three punctured edge germs inside `ball w r`.
2. If `geotop_polyhedron L - {w}` is connected, use the existing graph/path/broken-line infrastructure to connect the selected germs in the punctured carrier.
3. Intersect those connecting paths with the small ball and use first-exit/last-entry arguments to obtain a component of the punctured local ball whose closure touches all three germs.
4. Apply the already-proved radial-sector bound: a local component can touch at most two of the three selected germs.

Do **not** try to prove “degree > 2 implies cutpoint” for arbitrary finite graphs. The status report correctly warns that this is false in general; the proof needs the simple-closed-curve/local-one-manifold hypothesis. ([GitHub][11])

### 4.2 Figure 4.10 cyclic boundary-subdivision model

The active open package is `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`. Its own comment says the task is to subdivide the three boundary edges of one 2-simplex so that the resulting frontier complex has the same cyclic incidence as `L`, then send the listed vertices of `L` to the corresponding boundary subdivision vertices. ([GitHub][5])

The current obstacle is not the cyclic listing itself. The active code already has the graph put into a cyclic vertex listing and then calls this named book-step package. ([GitHub][5])

The practical problem noted in the progress report is **theory order**: recent boundary-subdivision helpers live after the current book-step theorem, so the theorem cannot use them directly unless the helper is moved earlier, duplicated in earlier-compatible form, or the book-step theorem is moved later. ([GitHub][4])

My recommendation is:

1. Move the boundary-subdivision helpers needed by Figure 4.10 **above** `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`, if their dependencies allow it.
2. If moving them causes dependency trouble, introduce a smaller earlier helper with exactly the needed statement:

   ```isabelle
   standard_2simplex_boundary_cycle_subdivision_with_n_vertices:
     assumes "geotop_simplex_dim σ 2" and "2 < p"
     shows "∃F u. geotop_is_subdivision F (geotop_comb_boundary {...σ...} 2)
              ∧ cyclic_vertex_listing F u p
              ∧ edge/simplex membership exactly matches adjacent indices"
   ```
3. Then prove the isomorphism by reducing `geotop_isomorphism` to two cases:

   * singleton vertex simplexes;
   * adjacent edge simplexes.

Do **not** let the proof reason about arbitrary finite vertex subsets for too long. Since `L` is a finite linear graph with a listing decomposition, any `geotop_convex_hull W ∈ L` should reduce to either `W = {vᵢ}` or `W = {vᵢ,vᵢ₊₁}`. Make that a helper:

```isabelle
cyclic_listing_convex_hull_in_L_cases:
  assumes "geotop_convex_hull W ∈ L"
      and "W ⊆ geotop_complex_vertices L"
  shows "∃i. W = {v i} ∨ W = {v i, v (Suc i)}"
```

Once this case split exists, `geotop_isomorphism L F φ` should become mostly bookkeeping.

### 4.3 Endpoint-chain boundary-arc fan

The endpoint package is now correctly stated as the path analogue of the cycle realization. The raw active file shows `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`; its assumptions include a finite linear graph, broken-line carrier, endpoint data, first edge data, arc parametrization data, and endpoint conditions. The wrapper then uses this book-step to prove the degree-one endpoint fan target. ([GitHub][5])

This should reuse the Figure 4.10 machinery, but with a **boundary arc**, not the whole boundary cycle.

Recommended proof shape:

```isabelle
endpoint_chain_listing_to_boundary_arc_subdivision:
  assumes "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "∃F B φ. F is a subdivision of one boundary arc of a standard 2-simplex
              ∧ bij_betw φ (geotop_complex_vertices L) B
              ∧ adjacent chain edges map to adjacent boundary subdivision edges"
```

Then cone from the adjacent standard boundary vertex:

```isabelle
boundary_arc_subdivision_cone_fan_target:
  assumes "F realizes the endpoint chain on a boundary arc"
      and "c is the opposite/adjacent boundary vertex not in the arc image"
  shows "∃L'. geotop_is_subdivision L' T
           ∧ singleton and cone-simplex clauses hold"
```

The endpoint proof has one recurring danger: arbitrary finite `W` clauses. As in the cycle case, prove an early reduction lemma:

```isabelle
endpoint_chain_convex_hull_in_L_cases:
  assumes "geotop_convex_hull W ∈ L"
      and "W ⊆ geotop_complex_vertices L"
  shows "W is a listed singleton or a listed adjacent pair"
```

Then all cone/fan obligations reduce to singleton and edge cases. That is much safer than trying to reason directly about arbitrary finite nonempty vertex subsets in the fan theorem.

---

## 5. One-sided semicircle separator: check the statement carefully

This is the remaining active local Euclidean package. The raw file shows `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`, followed by a radius-selection wrapper and then the local chart theorem. The visible assumptions include an edge `e`, a point `p` in its relative interior, a 2-simplex `σ` with `e` as a face, a local equality between the polyhedron and `σ`, and domain inclusions involving `U`. The intended conclusion is an arc `A` on `sphere p r ∩ σ` such that `U - A` is not connected. ([GitHub][5])

The worker’s reports already warn that the semicircle statement may be too strong unless `U` is localized enough to prevent reconnection outside the small ball. ([GitHub][8])

I would strengthen that warning: as rendered in the raw file, the **radius-level lemma looks under-assumed**. It appears to assume only that `U` contains the local polyhedron inside `ball p r`, while the separating arc is on `sphere p r`. If that is literally the statement, `A` need not even be contained in `U`, and `U` might be just the local open half-ball, in which case removing a boundary-sphere arc outside `U` does not disconnect it. The later wrapper has a stronger setup with `r < s` and `ball p s ∩ polyhedron K ⊆ U`, which is the right kind of assumption. ([GitHub][5])

So the worker should **not** spend time trying to prove the current radius lemma if the assumptions are exactly as displayed. Instead, replace it by a collar version:

```isabelle
geotop_one_side_simplex_semicircle_crosscut_separates_domain_collar:
  assumes "0 < r" "r < s"
      and "ball p s ∩ geotop_polyhedron K = ball p s ∩ σ"
      and "ball p s ∩ geotop_polyhedron K ⊆ U"
      and "U ⊆ geotop_polyhedron K"
      and "p ∈ rel_interior e"
      and "e is a face of σ"
  shows "∃A. A = sphere p r ∩ σ
           ∧ geotop_is_arc A ...
           ∧ ¬ top1_connected_on (U - A) ..."
```

The clean proof is not a heavy Jordan theorem. It is a distance-level separation:

1. Choose `A = sphere p r ∩ σ`.
2. Prove `A ⊆ U` using `r < s`, the local equality in `ball p s`, and the stronger `ball p s ∩ polyhedron K ⊆ U`.
3. Prove every point of `U - A` has `dist p x < r` or `dist p x > r`; equality would imply `x ∈ sphere p r ∩ geotop_polyhedron K`, hence by local equality `x ∈ sphere p r ∩ σ = A`.
4. Show both sides are nonempty:

   * inner side: `p` itself, since `p ∈ e ⊆ σ ⊆ geotop_polyhedron K` and `p ∈ ball p s`;
   * outer side: choose a point of `σ` at distance between `r` and `s`, preferably along the 2-simplex interior normal or along the edge if the edge has enough collar; this is where the proof may need `r` small relative to the distance from `p` to the edge endpoints.
5. The sets `{x∈U-A. dist p x < r}` and `{x∈U-A. dist p x > r}` are disjoint, relatively open, nonempty, and cover `U-A`.

This proof is more robust than a path-first-crossing proof, although the first-crossing argument is a good intuition. The actual Isabelle separation can be packaged as a continuous preimage/open-set separation by the distance function.

---

## 6. Section 3 subdisk/free-triangle transfer

The mid-prefix hole `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix` is the remaining hard point inside Theorem 3.3’s non-free-boundary-triangle argument. The raw file shows that the side complexes `K₁` and `K₂` have already been defined as subcomplexes cut out by the two subdisk closures, and the remaining comment says one must prove each side is a smaller polygonal-disk triangulation, apply the strong induction hypothesis, and transfer selected free 2-simplex witnesses back to the original disk. ([GitHub][12])

This is now well isolated, but it is still a real proof package. I recommend splitting it into four lemmas:

```isabelle
chord_side_complex_polygon_disk_triangulation:
  K_i triangulates closure(polygon_interior J_i)

chord_side_complex_two_simplex_count_strict:
  card two_simplexes(K_i) < card two_simplexes(K)

chord_side_free_triangle_off_cut_exists:
  each side has a free triangle whose selected boundary edge is not only the artificial chord

chord_side_free_triangle_transfers_to_parent:
  if τ is free in side K_i,J_i and its witness edge lies on the original boundary,
  then τ is free in K,J
```

The third lemma is probably the delicate one. The correct strategy is to use the existing “two selected boundary/free triangles” infrastructure: at most one side witness can be spoiled by the artificial chord, so a second selected boundary/free witness must transfer to the parent. Do **not** simply pick an arbitrary free triangle from the side induction hypothesis; arbitrary choice may select the artificial cut triangle and make the transfer fail.

The worker should also verify that the induction is genuinely on a smaller 2-simplex count. The strict decrease must be explicit and independent for both `K₁` and `K₂`; otherwise Isabelle will not accept the intended strong-induction transfer.

---

## 7. Section 3 fold normalization with support

The remaining fold package is `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`. It is now support-parametric and is used both for Theorem 3.4 with `U = UNIV` and for Theorem 3.7 with the given support set `U`. This is the correct architecture. The raw file’s comment says exactly that the induction should choose a free 2-simplex by Theorem 3.3, perform the Figure 3.3 fold or inverse with support in `U`, reduce the number of 2-simplexes, and compose supported homeomorphisms. ([GitHub][12])

The worker should keep this support-parametric lemma. Do **not** prove an unsupported Theorem 3.4 separately and then redo the work for Theorem 3.7.

Recommended decomposition:

```isabelle
free_triangle_boundary_contact_case_split:
  a free 2-simplex has either the one-edge or two-edge boundary-contact form,
  with the all-three-edge case reduced to the single-triangle base case.

free_triangle_one_edge_supported_fold:
  constructs the Figure 3.3 fold, identity outside a local carrier contained in U.

free_triangle_two_edge_supported_inverse_fold:
  constructs the inverse fold/corner-removal case, identity outside U.

fold_reduces_two_simplex_count:
  the transformed triangulation has strictly fewer 2-simplexes.

fold_preserves_polygon_disk_boundary_target:
  the new polygon/disk data are exactly what the induction hypothesis needs.

supported_homeomorphism_composition:
  if f and g are identity outside U, then f ∘ g is identity outside U.
```

The fold map itself should be local PL data, not a global topological construction. Use the selected triangle plus its immediate adjacent quadrilateral/triangle carrier, extend by identity, and then use existing PL-homeomorphism/subdivision facts. Trying to build an arbitrary plane homeomorphism directly at each induction step will be too expensive.

The base case is already largely staged in Theorem 3.4: one 2-simplex should give the identity map and the polygon frontier should match the simplex frontier. The raw file shows the Theorem 3.4 wrapper now obtains a triangulation and delegates the hard part to the support-parametric fold package. ([GitHub][12])

---

## 8. Theorem 4.2: theta/arc separation

The open D42 package is `geotop_polygon_arc_opposite_boundary_decomposition_prefix`. The raw file’s comment says the proof should use the Moise argument: if the `Q`-side and `S`-side are not separated in `I - A`, extract a broken line from near `Q` to near `S` inside `I - A`, then use Theorem 2.8 to get a forbidden theta graph. ([GitHub][12])

This should be proved as a named theorem, not as in-place component algebra. A good internal lemma is:

```isabelle
polygon_arc_QS_same_component_yields_theta_contradiction:
  assumes "A is an arc from P to R in closure I"
      and "A ∩ J = {P,R}"
      and "P,Q,R,S occur cyclically on J"
      and "Q and S lie in the same component of I - A"
  shows False
```

Then the decomposition theorem should be a standard component construction:

1. Let `U_Q` be the component/open side of `I - A` whose frontier contains `Q`.
2. Let `U_S` be the component/open side whose frontier contains `S`.
3. Use the theta contradiction to prove `U_Q ∩ U_S = {}`.
4. Use connectedness/separation facts to prove `I - A = U_Q ∪ U_S`.
5. Transfer the frontier-point statements for `Q` and `S`.

The endpoint hygiene is likely the main formal burden. If the component/path extraction only works for interior points, prove a small perturbation lemma once:

```isabelle
frontier_boundary_point_has_nearby_interior_points_in_component:
  boundary point Q on J gives interior witnesses approaching Q
```

Then use those witnesses to extract the broken line and recover `Q ∈ frontier U_Q`.

Do not try to prove D42 by `simp`/`blast` over component definitions. The mathematical content is the theta contradiction.

---

## 9. Theorem 4.4: brick / regular-neighborhood transfer

The final prefix file now consists essentially of Theorem 4.3, the brick-decomposition definition, and the D44 package. The raw file shows the single open `hD44_book_steps` conjunction bundling a fine brick decomposition, a regular-neighborhood/manifold step for `N'`, a frontier broken-line/1-sphere step, a component-frontier step for endpoints `V,W`, and the cyclic-order transfer to `Q,S`. ([GitHub][13])

This remains the largest conceptual package. It is only one visible `sorry`, but it represents most of Moise Theorem 4.4.

The worker should avoid expanding it into five unrelated ad hoc `have ... sorry` claims inside the theorem. Instead, use one regular-neighborhood theorem:

```isabelle
polygon_endpoint_arc_regular_neighborhood_component_transfer:
  assumes "J is a polygon"
      and "A1,A2 are disjoint arcs in closure I"
      and "A1 ∩ J = {P}" "A2 ∩ J = {R}"
      and "P,Q,R,S are cyclic on J"
  shows "∃C. Q ∈ frontier C ∧ S ∈ frontier C
           ∧ C is the component of I - (A1 ∪ A2) at each of its points"
```

Internally this theorem can still follow Moise’s brick proof:

1. Use compactness of `A1` and `A2` plus disjointness to choose a sufficiently fine brick decomposition.
2. Let `N` be the union of bricks meeting `A1`, and `N' = N ∩ closure I`.
3. Prove `N'` is a polygonal disk / 2-manifold with boundary.
4. Take the relevant frontier component through `P`.
5. Extract the broken line `B` with endpoints `V,W` on `J`.
6. Prove `V,W` lie in the frontier of one component of `I - (A1 ∪ A2)`.
7. Use cyclic order to transfer the frontier statement from `V,W` to `Q,S`.

The reports call this a brick or regular-neighborhood package, and that is exactly the right mental model. ([GitHub][9])

If the existing brick infrastructure is too thin, prefer a triangulated regular-neighborhood proof over a literal rectangular-grid proof. A literal grid/brick construction will require many low-level lemmas about mesh, cells, intersections, and frontiers. A regular-neighborhood theorem for polygonal arcs in a polygonal disk is closer to the rest of the complex/subdivision infrastructure.

---

## 10. Recommended finishing order

The best current order is:

### Phase 1: Close the finite graph sprint

Finish:

```isabelle
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
```

The graph-prefix split is now closed, and the cycle/fan focused targets are currently among the best iteration targets. The reports say the next useful milestone is a closed finite-graph / Figure 4.10 package. ([GitHub][3])

### Phase 2: Close the endpoint-chain fan

Finish:

```isabelle
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
```

Do this immediately after the cycle model, while the boundary-subdivision and finite-listing machinery is fresh.

### Phase 3: Fix and prove the one-sided semicircle package

Before proving it, check whether the radius-level lemma is under-assumed. If so, strengthen/localize the statement and prove the collar version directly.

### Phase 4: Finish Section 3 subdisk transfer

Finish:

```isabelle
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
```

This unlocks the remaining Theorem 3.3 subdisk induction machinery.

### Phase 5: Finish Section 3 fold normalization

Finish:

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
```

This should close both Theorem 3.4 and Theorem 3.7 wrappers.

### Phase 6: Finish D42 theta separation

Finish:

```isabelle
geotop_polygon_arc_opposite_boundary_decomposition_prefix
```

Do it through a reusable theta-contradiction lemma.

### Phase 7: Finish D44 last

Finish:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

This is likely the largest remaining package and should be approached as a regular-neighborhood theorem.

---

## 11. Process recommendations

The reports repeatedly emphasize the index workflow: grep both `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` before adding or restating facts, and regenerate indexes after theory/cache/report changes. ([GitHub][3])

Use the focused checker modes aggressively. The checker script has modes for `holes`, `index`, `names`, `stmts`, `focus`, `focus-warm`, `focus-prime`, `focus-status`, `slice-hot`, `split-hot`, and individual layer builds. ([GitHub][7])

For each remaining package, use this loop:

```bash
./check_dev34_fast.sh index PATTERN
./check_dev34_fast.sh focus-warm TARGET
./check_dev34_fast.sh focus TARGET PATTERN
```

Then replace only a small batch of `sorry`s or proof skeletons at a time. The reports explicitly warn that repeated single-goal prover probes are unlikely to solve these package holes by themselves. ([GitHub][11])

Line numbers should not be used as the main tracker anymore. The June 8 reports list the same 8 packages but with shifting active-file line numbers. Track by theorem name.

---

## 12. Direct message to the worker

The recent progress is substantial. Closing the graph-prefix cycle split and correcting the endpoint fan target were the right moves. The current branch is now much better organized, and the 8-hole count is credible.

The next best milestone is a completed finite-graph/Figure 4.10 package. The graph-prefix split is already done, so focus on the branch-vertex local cutpoint bridge and the cyclic boundary-subdivision book step. Move or refactor the new boundary-subdivision helpers so the active Figure 4.10 theorem can use them. Then reuse the same machinery for the endpoint-chain boundary-arc fan.

Do not treat the remaining 8 as local automation failures. The Section 3 subdisk transfer, Section 3 fold normalization, D42 theta separation, and D44 brick package each need named intermediate lemmas. The semicircle package should be checked for statement strength before proof work continues; as rendered, the radius-level lemma looks under-assumed unless a larger collar inside `U` is available.

The project is close in the sense that the remaining work is explicitly mapped and isolated. It is not close in the sense of “a few tactics left.” The fastest path to zero target `sorry`s is to close one complete package at a time, starting with finite graph / Figure 4.10, and to avoid moving hard Moise picture arguments into deeper wrappers without proving them.

[1]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_STATUS_2026_06_08.md "raw.githubusercontent.com"
[2]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy "raw.githubusercontent.com"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_AUDIT_BRIEF_2026_06_08.md "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_POST_AUDIT_REPORT_2026_06_08.md "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34/GeoTop_3_4.thy "raw.githubusercontent.com"
[6]: https://github.com/JUrban/isa_geotop1/tree/codex-dev34-cache/tst "isa_geotop1/tst at codex-dev34-cache · JUrban/isa_geotop1 · GitHub"
[7]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/check_dev34_fast.sh "raw.githubusercontent.com"
[8]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_BRIEF_2026_06_08.md "raw.githubusercontent.com"
[9]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_CURRENT_REPORT_2026_06_08.md "raw.githubusercontent.com"
[10]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy "raw.githubusercontent.com"
[11]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_STATUS_2026_06_08.md "raw.githubusercontent.com"
[12]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy "raw.githubusercontent.com"
[13]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy "raw.githubusercontent.com"
