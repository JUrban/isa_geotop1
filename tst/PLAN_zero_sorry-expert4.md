# Fresh GeoTop / Moise Sections 3–4 report for `codex-dev34-cache`

I re-checked the current public branch, recent progress reports, raw theory files, and the recent commit stream. I did **not** run Isabelle locally, so I cannot independently certify the build. The analysis below is based on the pushed branch contents, the worker’s focused status reports, and the current raw `.thy` files.

The high-level diagnosis is:

> The project is much closer structurally, but the remaining work is still real mathematics. The latest useful status is no longer “17 → 10 → 8 holes”; it is now a small set of stable package holes, with the center of gravity having moved strongly into Moise Theorem 3.3.

The worker’s latest Section 3 report is credible: Theorem 3.3 is no longer missing its induction structure. It is missing two hard Moise Figure 3.2 subarguments, and Section 3 as a whole then depends on one shared fold-normalization package for Theorems 3.4 and 3.7. Theorems 3.5 and 3.6 are essentially wrapper consequences once 3.4 is real.

---

## 1. Current status and recent movement

The older project reports are now stale in raw line count. A June 9 live report says the target had moved to **six stable packages**, not the older 8/10/17 maps; it lists the main remaining buckets as D44 bricks, Theorem 3.3 subdisk transfer, fold normalization, D42 theta separation, graph branch local cutpoint, and endpoint boundary-arc fan. It also states that cycle realization and the one-sided semicircle/collar packages were no longer live in that scan. ([GitHub][1])

Since then, the branch’s recent commit stream has become almost entirely Moise 3.3 work: commits are titled “Refine Moise 3.3 side induction packages,” “Decompose Moise 3.3 side-complex core,” “Refine Moise 3.3 side-complex count residual,” “Narrow Moise 3.3 parent-boundary residual,” “Factor Moise 3.3 parent-boundary side residual,” and many more around side witnesses, chord contact, theta residue, and parent contact transfer. That commit pattern strongly supports the worker’s current diagnosis that the active bottleneck is Theorem 3.3’s Figure 3.2 branch, not active `dev34` graph/fan infrastructure. ([GitHub][2])

The active Figure 4.10 boundary-cycle package had already been reported closed on June 9, with the proof using source and target oriented successor cycles and an index-to-index vertex map. That closure matters because the earlier finite graph/cycle realization sprint is no longer the main strategic priority. ([GitHub][3])

The development process also improved significantly. The `.dev34_fast_cache` report explains that the proof stack is now split into layers such as `dev34_prefix_base`, `dev34_prefix_graph/cache`, `dev34_prefix_graph`, `dev34_prefix_mid`, `dev34_prefix`, and active `dev34`; focused commands can build a generated prefix once and then process only the active theorem slice. The report is explicit that this is a proof-loop accelerator, not a replacement for final verification. ([GitHub][4])

---

## 2. Updated hole map by mathematical package

Based on the worker’s latest status plus the raw files, the stable remaining work is best understood as these packages:

1. **Theorem 3.3 side-complex package**
   The two chord-side subcomplexes must be shown to be real smaller polygonal-disk triangulations with enough triangles for induction.

2. **Theorem 3.3 side-witness transfer package**
   A free triangle found in a side disk must be transferred back to the parent disk, ruling out the remaining artificial-chord-spoiled case.

3. **Section 3 fold-normalization package**
   The support-parametric Figure 3.3 fold induction used by both Theorem 3.4 and Theorem 3.7.

4. **Theorem 4.2 D42 theta/component split**
   Opposite boundary points/arcs must be separated by the arc `A`, using the Moise theta-graph contradiction.

5. **Graph-cache branch-vertex local cutpoint package**
   A local branch point on a simple closed curve carrier must contradict the two-sided local 1-manifold behavior.

6. **Theorem 4.4 brick / regular-neighborhood / component-transfer package**
   The largest remaining Section 4 package: fine brick decomposition or regular neighborhood, frontier broken line, and same-component frontier transfer to `Q,S`.

There is one subtle counting issue: the raw mid-prefix file currently displays the side-complex residual as symmetric side-1 and side-2 inner `sorry`s, but mathematically this is one Figure 3.2 side-complex package. The worker’s “Theorem 3.3 has two remaining conceptual holes” framing is the right way to track progress.

---

## 3. Theorem 3.3: current state

The raw theory confirms that Theorem 3.3 is the free-triangle theorem: if `J` is a polygon, `K` is a complex whose polyhedron is the closed polygonal disk, and there is more than one 2-simplex, then there exists a `geotop_free_2_simplex K J σ₂`. The proof comment explicitly says the stronger claim is that there are at least two free 2-simplexes, by induction on the number of 2-simplexes. ([GitHub][5])

The overall induction is now wired. The remaining trouble is inside the non-free boundary-triangle branch, corresponding to Moise Figure 3.2. The raw file shows a named call to `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`, described as the step that defines the two subdisk complexes from the chord decomposition, applies strong induction on both smaller polygonal disks, and transfers one free 2-simplex from each side back to the original triangulation. ([GitHub][5])

The raw `sorry` inventory around that region shows the exact shape of the first residual: side 1 and side 2 each still need a “Figure 3.2 side package” proving the side closed disk is a `K`-subcomplex carrier, omits a parent 2-simplex on the other side, and still has enough 2-simplexes for the induction hypothesis. ([GitHub][5])

### 3.1 First Theorem 3.3 target: the side-complex package

The worker’s first listed residual, around line 10116, is exactly the right next target.

This package should be proved as a **symmetric side lemma**, not as two independent proofs for `J₁/L₁` and `J₂/L₂`. The raw file currently has separate side-1 and side-2 claims, but the proof principle is the same. Proving them separately risks duplicating the same geometry and then having to repair both copies.

A good internal lemma shape would be:

```isabelle
geotop_chord_side_complex_induction_geometry:
  assumes parent_disk_data
      and nonfree_boundary_triangle_data
      and side_decomposition_data
      and "Side i"  (* i = 1 or i = 2, or use two instantiations of same lemma *)
  shows
    "geotop_polyhedron L_i =
       closure_on UNIV geotop_euclidean_topology
         (geotop_polygon_interior J_i)"
    "card {τ∈L_i. geotop_simplex_dim τ 2} < card {τ∈K. geotop_simplex_dim τ 2}"
    "card {τ∈L_i. geotop_simplex_dim τ 2} > 1"
```

The proof should be split into four named facts.

First, prove **carrier restriction**:

```isabelle
x ∈ closure(polygon_interior J_i)
⟹ geotop_K_carrier K x ⊆ closure(polygon_interior J_i)
```

or equivalently the exact `geotop_K_carrier` form already used in the file. This is the heart of “simplexes do not straddle the chord side.” It should use the current theta/chord obstruction facts, not new planar intuition.

Second, prove **polyhedron equality**:

```isabelle
geotop_polyhedron L_i =
closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J_i)
```

after defining `L_i` as the set of simplexes of `K` whose carriers lie in the side closure. The two inclusions should be separate lemmas. The hard inclusion is usually: every point in the side closed disk lies in some parent simplex whose carrier is contained in that side.

Third, prove **strict smaller count**:

```isabelle
card T_i < card T
```

where `T_i = {τ∈L_i. dim τ = 2}` and `T = {τ∈K. dim τ = 2}`. Do this using the already visible pattern in the raw file: show `T_i ⊆ T` and exhibit one parent 2-simplex omitted by side `i`. The raw proof already has a generic finite-subset-cardinality helper in use after obtaining an omitted `rho`. ([GitHub][5])

Fourth, prove **nontrivial side count**:

```isabelle
card T_i > 1
```

This is likely the delicate part. Avoid proving it by arithmetic after the fact. The geometric content is: if a side had only zero or one 2-simplex, then the non-free parent boundary triangle would collapse into one of the already-ruled-out small configurations. Use the existing all-boundary/two-triangle infrastructure and the recent “theta contact / named-edge residue” lemmas. The recent commits strongly suggest this is exactly where the worker has been narrowing the problem: “side count decrease via theta absence,” “side-complex residual,” “side strict-count helper,” and “side-complex count core.” ([GitHub][2])

My concrete recommendation: prove a side-count contradiction lemma:

```isabelle
geotop_chord_side_complex_not_single_triangle:
  assumes parent_nonfree_boundary_triangle_data
      and side_complex_carrier_data
      and "card T_i ≤ 1"
  shows False
```

Then the side package can use `card T_i > 1` without carrying all the Moise picture argument inline.

### 3.2 Second Theorem 3.3 target: final side-witness transfer

The worker’s second Theorem 3.3 residual, around line 12148, is the final transfer geometry: a free triangle obtained by induction on a side disk may have its boundary witness on the artificial chord instead of on the original polygon boundary. That is exactly the subtle part of Moise’s “choose one from each side” argument.

The raw file shows this residual as a “same-dimension reduction” where an uncovered parent-boundary residue would force a proper named-edge face of the cut triangle to account for side witness contact. ([GitHub][5])

The correct strategy is **not** to transfer an arbitrary free triangle from the side disk. The side induction gives at least two free 2-simplexes. Use that strength.

The transfer proof should be organized around this classification:

```isabelle
side_free_witness_boundary_edge_cases:
  assumes "geotop_free_2_simplex L_i J_i τ"
  obtains e where
    "e is the selected/free boundary edge of τ"
    "e ⊆ J"          (* parent boundary: good transfer case *)
  | "e ⊆ chord"      (* artificial side boundary: spoiled case *)
```

Then prove:

```isabelle
side_free_witness_parent_boundary_transfers:
  assumes "τ free in side"
      and "selected boundary edge e ⊆ J"
  shows "τ free in parent K J"
```

The only hard case is when the witness edge lies on the artificial chord. The right proof should use a uniqueness/counting argument:

```isabelle
at_most_one_side_free_witness_can_be_chord_only:
  assumes side decomposition data
  shows "not both selected side witnesses are spoiled only by the chord"
```

or more locally:

```isabelle
two_free_side_witnesses_force_one_parent_boundary_contact:
  assumes "card {τ∈L_i. free_in_side τ} ≥ 2"
  shows "∃τ. free_in_side τ ∧ has_selected_edge_on_parent_boundary τ"
```

The recent commits “Keep off-parent chord witnesses,” “Split nonparent side edges onto the GT3 chord,” “Expose chord contact faces,” “Cover side witnesses off the chord,” and “Record side witness connectedness” indicate that this is already the current direction. Keep going, but compress it into one named lemma whose statement mentions the exact bad case and rules it out. ([GitHub][2])

A useful final transfer theorem would be:

```isabelle
geotop_chord_side_free_witness_transfers_or_contradicts_nonfree:
  assumes side_induction_witnesses
      and nonfree_parent_triangle_data
      and side_decomposition_data
  shows "∃τ∈K. geotop_free_2_simplex K J τ"
```

or, for the stronger version:

```isabelle
shows "card {τ∈K. geotop_free_2_simplex K J τ} ≥ 2"
```

The important point is that the proof should produce the parent witnesses only after filtering out artificial-chord-only witnesses.

---

## 4. Section 3 after Theorem 3.3

The worker’s status summary for Theorems 3.4–3.7 is accurate.

The raw file shows `Theorem_GT_3_4` as the polygon-to-standard-triangle-frontier homeomorphism theorem. Its proof has been reduced to obtaining a triangulation of the closed polygonal disk and then using the shared fold-normalization package. ([GitHub][5])

The raw file also shows `Theorem_GT_3_7`, the supported version, directly using the same support-parametric package `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`. ([GitHub][5])

Theorems 3.5 and 3.6 are downstream wrappers. Theorem 3.5 uses Theorem 3.4 twice to map two polygons to simplex frontiers and compose plane homeomorphisms; Theorem 3.6 uses Theorem 3.4 and pulls back a 2-simplex under the homeomorphism. ([GitHub][5])

### 4.1 The shared fold-normalization package is the right architecture

The open package is:

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
```

The raw file describes it as the induction that chooses a free triangle via Theorem 3.3, performs the Figure 3.3 fold or inverse with support inside `U`, composes with the induction map for the smaller complex, and preserves identity outside `U`. ([GitHub][5])

The worker should **not** prove an unsupported Theorem 3.4 first and later redo support for Theorem 3.7. The current support-parametric package is exactly right.

Recommended internal split:

```isabelle
free_triangle_boundary_contact_cases:
  free 2-simplex ⇒ one-boundary-edge case ∨ two-boundary-edge case ∨ base/all-boundary case

free_triangle_one_edge_supported_fold:
  constructs the local Figure 3.3 fold, identity outside a carrier contained in U

free_triangle_two_edge_supported_corner_fold:
  handles the corner/removal case, identity outside U

free_triangle_fold_reduces_two_simplex_count:
  transformed complex has strictly fewer 2-simplexes

free_triangle_fold_preserves_polygon_disk_target:
  new polygon/disk data match the induction hypothesis

supported_homeomorphism_compose:
  if f and g are identity outside U, then g ∘ f is identity outside U
```

The fold should be built locally on a small PL carrier: the free triangle plus its adjacent triangle/quadrilateral neighborhood, then extended by identity. Do not attempt to build an arbitrary global plane homeomorphism directly at every induction step.

A practical order after 3.3 closes:

1. Prove the boundary-contact case split.
2. Prove the one-edge fold case.
3. Prove the two-edge/corner case.
4. Prove count decrease and preservation of the disk frontier data.
5. Compose with the induction hypothesis.
6. Run the wrapper checks for Theorems 3.4 and 3.7.
7. Verify Theorems 3.5 and 3.6 require no new local proof work.

---

## 5. Theorem 4.2: D42 theta/component split

The current D42 package is:

```isabelle
geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
```

The raw file states the intended theorem: given a polygon `J`, cyclic boundary points `P,Q,R,S`, and an arc `A` from `P` to `R` inside the closed disk with `A ∩ J = {P,R}`, produce disjoint open sets `U_Q` and `U_S` covering `polygon_interior J - A`, with `Q` and `S` in the appropriate frontiers. The comment explicitly says the missing step is Moise’s theta argument: if the sides met, a broken line from the `Q` side to the `S` side in `I - A` together with the boundary arcs forms a forbidden theta graph. ([GitHub][5])

This should be proved as a single reusable theta lemma:

```isabelle
polygon_arc_opposite_boundary_same_component_theta_contradiction:
  assumes "geotop_is_polygon J"
      and "geotop_polygon_cyclic_order J P Q R S"
      and "geotop_is_arc A ..."
      and "A ⊆ closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
      and "A ∩ J = {P,R}"
      and "Q' ∈ geotop_polygon_interior J - A"
      and "S' ∈ geotop_polygon_interior J - A"
      and "S' ∈ geotop_component_at ... (geotop_polygon_interior J - A) Q'"
  shows False
```

Then the component split theorem should only instantiate this lemma and package the open components.

The proof needs three ingredients:

1. **Open-cut facts**: `polygon_interior J - A` is open enough locally to extract arcs/broken lines inside components. The June 9 report says reusable D42 infrastructure such as polygon-interior-minus-arc openness and component openness has already been added. ([GitHub][6])

2. **Broken-line extraction**: same component in an open polygonal region should yield a broken line or polygonal arc between suitable interior witnesses.

3. **Theta contradiction**: the `P`–`R` arc `A`, the extracted `Q`–`S` broken line, and the two boundary arcs determined by cyclic order form the forbidden theta configuration from the earlier Section 2 theorem.

The biggest likely formal headache is endpoint hygiene: `Q` and `S` themselves are on the polygon boundary, while the same-component path usually lives in the interior minus `A`. Use nearby interior witnesses approaching `Q` and `S`; then recover frontier membership. Do not try to prove the theorem by component algebra alone.

---

## 6. Graph-cache branch-vertex local cutpoint

The remaining graph-cache package is:

```isabelle
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
```

The theorem says that a finite linear graph carried by a simple closed curve cannot have a vertex with more than two incident edge germs. The raw proof already has a large local setup and is missing a “first-exit/local-star inference”: from a connected witness meeting three selected germs, produce a component of the local ball complement whose closure touches all three selected incident edge germs. ([GitHub][7])

The expert warning remains essential: do **not** prove the false general lemma “degree > 2 implies cutpoint” for finite graphs. A theta graph has vertices of degree 3 but deleting such a vertex need not disconnect the graph. The simple-closed-curve/local-one-manifold hypothesis is the key extra condition.

The current missing step should not be overgeneralized. A too-broad lemma such as

```isabelle
connected set meeting three local arms ⇒ one local complement component touches all three arms
```

is suspicious unless it carries the exact side/local-star hypotheses. The June 9 status also says the local component bridge is under-specified and needs the third-germ/arc-side split data to be carried from the surrounding branch proof. ([GitHub][8])

Recommended next graph lemma:

```isabelle
branch_vertex_three_germs_same_side_component:
  assumes "top1_simple_closed_curve_on UNIV geotop_euclidean_topology (geotop_polyhedron L)"
      and finite_linear_graph_local_star_data
      and three_distinct_incident_edges_at_w
      and selected_side_split_data
  shows "∃C. C ∈ components (ball w r - (e1 ∪ e2 ∪ e3))
           ∧ germ(e1) ∩ closure C ≠ {}
           ∧ germ(e2) ∩ closure C ≠ {}
           ∧ germ(e3) ∩ closure C ≠ {}"
```

Then use the already staged radial-sector contradiction.

In short: strengthen the missing bridge with exactly the local side data already present in the proof context. Do not add a global graph theorem.

---

## 7. Theorem 4.4: brick / regular-neighborhood package

The final prefix file is now almost entirely Theorem 4.4 infrastructure. The raw file defines `geotop_brick_decomposition`, then states `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`, whose single open book step bundles: fine brick decomposition, regular neighborhood, frontier broken line, component-frontier step for broken-line endpoints, and cyclic-order transfer to `Q,S`. ([GitHub][9])

This is still the largest remaining package. It should be left until after Theorem 3.3, the fold package, and D42 are stable, unless it blocks a dependency.

Do not expand `hD44_book_steps` into five unrelated local `sorry`s. Instead, package it as a regular-neighborhood theorem:

```isabelle
polygon_two_endpoint_arcs_regular_neighborhood_transfer:
  assumes "geotop_is_polygon J"
      and cyclic_order_data
      and "A1" "A2" are disjoint arcs in the closed disk
      and "A1 ∩ J = {P}" "A2 ∩ J = {R}"
  shows "∃C. Q ∈ frontier C
           ∧ S ∈ frontier C
           ∧ (∀P'∈polygon_interior J - (A1 ∪ A2).
                C = component_at (polygon_interior J - (A1 ∪ A2)) P')"
```

Internally this may still follow Moise’s brick proof:

1. Choose a fine brick decomposition.
2. Let `N` be the union of bricks meeting `A1`.
3. Let `N' = N ∩ closure(I)`.
4. Prove `N'` is a polygonal disk or 2-manifold with boundary.
5. Extract the frontier component through `P`.
6. Obtain a broken-line subarc with endpoints `V,W` on `J`.
7. Prove `V,W` are in the frontier of one component of `I - (A1 ∪ A2)`.
8. Use cyclic order and D42-style separation to transfer from `V,W` to `Q,S`.

If existing brick infrastructure is thin, a triangulated regular neighborhood of `A1` inside the polygonal disk may be cheaper than a literal rectangular brick decomposition. The theorem only needs the component-transfer conclusion; it does not need a large reusable theory of arbitrary brick decompositions unless later files depend on it.

---

## 8. Recommended completion order

Given the latest commit stream and the worker’s status, the best order is now:

### Phase 1: Stay on Theorem 3.3 while the context is hot

Close the side-complex residual first. Treat the side-1 and side-2 obligations as one symmetric theorem. Prove carrier equality, strict smaller count, and `>1` side count as separate lemmas.

Then close the side-witness transfer residual. Use the stronger two-free-witness induction result and prove that at least one side witness has real parent-boundary contact rather than only artificial-chord contact.

This is the highest-value closure because Theorem 3.3 feeds the fold induction for Theorems 3.4 and 3.7.

### Phase 2: Close the support-parametric fold package

After Theorem 3.3 is real, finish:

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
```

This should close Theorem 3.4 and Theorem 3.7 wrappers. Theorems 3.5 and 3.6 should then require no new mathematical work.

### Phase 3: Close D42

Finish the theta/component split:

```isabelle
geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
```

This is likely needed conceptually for D44 and should be handled before the brick package.

### Phase 4: Close the branch-vertex local cutpoint

This is isolated and probably smaller than D44. Keep it exact to the simple-closed-curve/local-star setting.

### Phase 5: Finish D44 last

Treat D44 as a regular-neighborhood/component-transfer theorem. It is one visible `sorry`, but it is the largest remaining book argument.

---

## 9. Process recommendations for the worker

The fast-cache workflow is now useful, but every claim must match the check that supports it. A focused slice check is good for “this theorem slice processes”; it is not final certification. The cache report explicitly recommends using focused checks for theorem iteration, then broader `cache-through`/layer checks and final builds at package boundaries. ([GitHub][4])

For the current Theorem 3.3 work, use the focused target described in the cache report:

```bash
TIMEOUT=240s ./check_dev34_fast.sh focus mid-split-free
```

Before adding any helper, search both generated indexes and the live source:

```bash
./check_dev34_fast.sh scan "side witness chord"
./check_dev34_fast.sh index "subdisk carrier"
./check_dev34_fast.sh stmts "free 2 simplex"
```

After each package closure:

```bash
./check_dev34_fast.sh holes
bash gen_index.sh
bash gen_stmt_index.sh
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

Commit messages should keep saying exactly what changed: “closed side-complex carrier equality,” “closed side count >1,” “closed artificial chord witness transfer,” etc. The current commit style is good because it makes the history readable and ties progress to proof packages rather than vague cleanup. ([GitHub][2])

---

## 10. Direct reply to the worker’s latest Section 3 status

I agree with the worker’s diagnosis.

Theorem 3.3 is no longer missing its induction scaffold. The remaining two conceptual holes are exactly the hard Moise Figure 3.2 geometry:

1. the side-complex package: the two chord-side complexes must genuinely triangulate smaller polygonal disks and have the right triangle counts;
2. the side-witness transfer package: a side-disk free triangle must be chosen so that its boundary contact transfers to the original polygon boundary, not merely to the artificial chord.

The best next closure is indeed the first side-complex residual, followed by the transfer residual. After that, the shared fold-normalization package is the only real Section 3 obstacle. Once those three Section 3 packages are closed, Theorems 3.4 and 3.7 should become true wrappers, while 3.5 and 3.6 should fall without new mathematical work.

The remaining Section 4 work is still substantial: D42 is the theta-separation theorem, and D44 is a full regular-neighborhood/brick-transfer theorem. But the branch is now well localized. The fastest route to completion is to close whole named packages in the order above, not to push the same Moise picture arguments into deeper wrappers.

[1]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_CURRENT_2026_06_09_AFTER_EXPERT3.md "raw.githubusercontent.com"
[2]: https://github.com/JUrban/isa_geotop1/commits/codex-dev34-cache/ "Commits · JUrban/isa_geotop1 · GitHub"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_CYCLE_REALIZATION_CLOSED_2026_06_09.md "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/DEV34_FAST_CACHE_APPROACH_REPORT_2026_06_10.md "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy?cb=202606101030 "raw.githubusercontent.com"
[6]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_CURRENT_BRIEF_2026_06_09_6_HOLES.md "raw.githubusercontent.com"
[7]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy?cb=202606101030 "raw.githubusercontent.com"
[8]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/GOAL_PROGRESS_CURRENT_STATUS_AFTER_EXPERT3_2026_06_09.md "raw.githubusercontent.com"
[9]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy?cb=202606101030 "raw.githubusercontent.com"
