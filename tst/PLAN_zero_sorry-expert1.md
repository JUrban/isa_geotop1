# Updated report on `isa_geotop1`, branch `codex-dev34-cache`

I re-examined the public branch and the current raw theory/status files. I did **not** independently run Isabelle in this environment, so the report below is based on the branch contents and the project’s own status/build notes, not on a fresh kernel-certified build.

The important update is that the worker has indeed made meaningful progress. The June 5 status file still says the target stack had **17 executable `sorry`s**: **12 in `tst/dev34_prefix`**, **0 in `tst/dev34_core`**, and **5 in active `tst/dev34`**, with no remaining `sledgehammer` markers. It also gives the completion criterion: eliminate all `sorry`/`sledgehammer` from `tst/dev34_prefix`, `tst/dev34_core`, and `tst/dev34`, rebuild, regenerate indexes, and commit. ([GitHub][1])

But the current raw theory files appear to be ahead of that status report. Several Section 3 two-triangle and all-boundary obligations that were previously highlighted as next targets now look closed in the raw prefix file. My raw-file inspection sees roughly **14 visible target `sorry`s** now: about **9 in `dev34_prefix`** and **5 in active `dev34`**. Please verify this locally with the project’s own command:

```bash
rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34
```

The branch layout remains the same: the project is split into cached and active layers under `tst`, including `dev34`, `dev34_core`, `dev34_pre`, `dev34_prefix`, graph/link/open-star helper layers, and related generated status/index files. ([GitHub][2])

---

## 1. Executive diagnosis

The project is no longer in the “broad infrastructure missing everywhere” phase. It has moved into a much narrower but still difficult finishing phase.

The current remaining work falls into **six conceptual clusters**:

1. **Section 3 ear/free-triangle selection**
   One major finite triangulated disk lemma remains: selecting two boundary 2-simplexes with appropriate selected boundary edges.

2. **Section 3 fold induction and support control**
   Theorem 3.4 still needs the induction-step fold argument, and Theorem 3.7 still needs the support-inside-`U` refinement.

3. **Section 4.2 arc separation**
   The theorem has reached the point where the named components exist; the missing step is the actual disjointness/separation proof.

4. **Section 4.4 brick/regular-neighborhood machinery**
   Five remaining book-step holes are concentrated in the brick decomposition / frontier / manifold / component part.

5. **Figure 4.10 and finite linear graph realization**
   Two active holes remain around converting finite linear graph data into the standard boundary-cycle or boundary-arc fan target.

6. **Local edge-star chart contradictions**
   The active file still has holes for the one-sided semicircle separator, the three-incident-small-circle connectedness argument, and the chart/Jordan-side containment step.

That is good news. These are no longer random proof-search failures. They are exactly the finite list of mathematical pictures from Moise Sections 3 and 4 that still need to be turned into stable Isabelle lemmas.

The worker’s main risk now is not lack of local automation. The risk is **trying to close each remaining `sorry` in place**, thereby re-proving the same geometric facts repeatedly. The fastest path is to package the remaining pictures into a few reusable lemmas, then make the theorem wrappers short.

---

## 2. What has clearly improved since the previous report

### 2.1 The old two-triangle boundary bottlenecks look largely resolved

The current prefix file shows the general all-boundary closure lemma as proved, and it now feeds consequences saying that if all three edges of a triangle are boundary edges, then the relevant polygonal disk is forced into that triangle and no other 2-simplex can remain outside it. ([GitHub][3])

The two-triangle boundary-contact machinery also looks much healthier. The file contains a proved lemma covering the boundary-contact edges of two triangles, and the old “two-triangle all boundary edges force other subset” / “two-triangle not all boundary edges” style obligations now appear filled rather than left as the main blockers. ([GitHub][3])

This is a real change. Previously, the Section 3 base cases looked like they could derail the entire free-triangle induction. Now the remaining Section 3 problem is more focused: prove the selected-boundary-ear lemma and then complete the fold induction.

### 2.2 Theorem 3.3 is closer to being just a wrapper

The current prefix file shows the strong Theorem 3.3-style decomposition/free-count argument calling into a named non-free-boundary-triangle decomposition lemma. The remaining visible Section 3 ear hole is now the selected boundary 2-simplex lemma, not the whole disk decomposition theorem. ([GitHub][3])

This is the right direction. The worker has successfully pushed a large informal book argument down into named infrastructure. The remaining move is to finish the one finite disk boundary-selection lemma cleanly.

### 2.3 Active `dev34` has also progressed

One important local/star result now appears proved: the standard fan target vertex is shown to lie in the HOL interior of the target polyhedron using PL-homeomorphism/star target isomorphism and invariance-of-domain style infrastructure. ([GitHub][4])

The two-sided vertex-link polygon material also appears substantially closed: the active file contains a proved link-component degree-two polygon witness and a proved two-sided vertex-link polygon wrapper. ([GitHub][4])

So the recent work has not merely reduced the raw number of holes. It has also moved the proof architecture closer to the right shape: local chart wrappers are increasingly calling explicit helper lemmas instead of carrying huge informal arguments inline.

---

## 3. Current visible hole map

Based on the current raw files, the remaining visible holes are approximately as follows.

### In `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`

The first major remaining Section 3 hole is:

```isabelle
geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix
```

Its role is to show that, when there are more than two 2-simplexes in the polygonal disk, there are two distinct 2-simplexes with selected boundary edges. The wrapper `geotop_polygon_disk_two_boundary_2simplexes_prefix` then translates this selected-edge fact into the more ordinary “two boundary 2-simplexes” conclusion. ([GitHub][3])

Theorem 3.4 still has an unfinished induction step:

```isabelle
have ind_step : ...
  sorry
```

The surrounding structure already has the nonempty/base setup, so this is specifically the free-triangle fold/elimination step. ([GitHub][3])

Theorem 3.7 still has the support-control hole:

```isabelle
have h_support_in_U : ...
  sorry
```

This is the controlled-support version of the Section 3 folding/homeomorphism argument. ([GitHub][3])

Theorem 4.2 is down to the separation/disjointness point:

```isabelle
have hD42_disjoint : ...
  sorry
```

The proof has already built the candidate components `UQ` and `US`; the missing fact is that the arc separates the appropriate opposite boundary data. ([GitHub][3])

Theorem 4.4 still has five brick-related holes:

```isabelle
hD44_bricks
hD44_N'_manifold
hD44_frontier_broken_line
hD44_VW_component
hD44_QS_component
```

These are exactly the brick decomposition, derived-neighborhood manifoldness, frontier broken-line, and component-separation obligations. ([GitHub][3])

### In active `tst/dev34/GeoTop_3_4.thy`

The active file still has the finite graph cycle model hole:

```isabelle
geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34
```

The comment there says the intended content is to take a finite connected linear graph whose carrier is a polygon and place it as a subdivision of the frontier of a standard 2-simplex. ([GitHub][4])

There is also the endpoint/boundary-arc fan target hole:

```isabelle
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

The nearby comments say the remaining graph step is to recover an ordered edge chain, realize it as a subdivided boundary arc, and choose a matching boundary endpoint. ([GitHub][4])

The one-sided edge semicircle lemma remains open:

```isabelle
geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
```

The lemma is intended to choose a small semicircle in the unique incident 2-simplex and prove that removing it disconnects the relevant local domain. ([GitHub][4])

The three-incident edge small-circle complement lemma remains open:

```isabelle
geotop_three_incident_small_circle_complement_connected_explicit_dev34
```

The surrounding code has already built much of the finite local carrier/radius setup; the missing content is the connectedness of the complement after removing the chosen small circle. ([GitHub][4])

Finally, a chart/Jordan-side step remains open in the 2-cell chart contradiction:

```isabelle
have hchart_image_sep : ...
  sorry
```

The intended result is that the chart image of the chosen 1-sphere has inner and outer sides with the needed containment/intersection behavior. ([GitHub][4])

---

## 4. Section 3: what remains and how to finish it

### 4.1 Finish the selected boundary-ear lemma first

The highest-priority Section 3 target is:

```isabelle
geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix
```

Do not prove this by drawing the triangulated disk inside the theorem. It should be a finite combinatorial lemma about selected boundary edges in a triangulated polygonal disk.

The current statement appears to need two distinct 2-simplexes, each carrying a selected boundary 1-face. The wrapper then obtains the ordinary two-boundary-triangle conclusion. ([GitHub][3])

The most direct proof route seems to be:

1. Define the set of selected boundary edges globally:

   ```isabelle
   B = {e ∈ K. geotop_simplex_dim e 1 ∧ e ⊆ frontier I ∧ selected e}
   ```

2. Prove that this set has at least three elements, or at least enough elements that it cannot be owned by a single 2-simplex.

3. Prove every selected boundary edge is contained in at least one 2-simplex of the disk triangulation.

4. Prove a 2-simplex can own at most three selected boundary edges.

5. Use the already-proved all-boundary obstruction: if a single 2-simplex owned all three of its edges as boundary edges, then the disk would be forced into that triangle, contradicting the assumption that there are more than two 2-simplexes. The current prefix file already has this all-boundary closure/no-other-simplex infrastructure. ([GitHub][3])

6. Conclude that selected boundary edges must be attached to at least two distinct 2-simplexes.

This approach is better aligned with the existing code than a full dual-graph proof. A dual-graph proof is tempting, but triangulation dual graphs of disks can have cycles, and the formal overhead can grow quickly. The current project already has the all-boundary closure machinery; exploit it.

A useful intermediate lemma would be:

```isabelle
polygon_disk_selected_boundary_edges_not_all_on_one_2simplex:
  assumes "polygon_disk_triangulation K I"
      and "card {s ∈ K. geotop_simplex_dim s 2} > 2"
      and "⋀e. e ∈ selected_boundary_edges K I ⟹ e ⊆ t"
      and "geotop_simplex_dim t 2"
  shows False
```

Then the target lemma becomes a cardinality/choice argument.

### 4.2 Then close Theorem 3.3 as a consequence

Once the selected-ear lemma is proved, avoid adding more geometry to Theorem 3.3. The raw file already suggests that Theorem 3.3 has been converted into a strong free-count/decomposition wrapper. ([GitHub][3])

The final Theorem 3.3 proof should look like:

1. handle small-cardinality cases using the now-proved two-triangle/all-boundary lemmas;
2. use the selected-ear lemma for the large-cardinality case;
3. call the non-free-boundary-triangle decomposition/free-count lemma;
4. discharge cardinality inequalities.

Keep the final theorem proof short. If another geometric fact is needed, it belongs beside the ear lemma, not inline.

### 4.3 Theorem 3.4: make the fold step a named lemma

Theorem 3.4’s remaining `ind_step` is the next Section 3 bottleneck. ([GitHub][3])

This should be attacked as a standalone lemma:

```isabelle
free_triangle_fold_elimination_prefix:
  assumes "K triangulates the polygonal disk I"
      and "σ is a free 2-simplex of K"
      and "σ satisfies the required boundary-contact case"
  shows "∃K' h. homeomorphism h ... ∧
                card {τ∈K'. dim τ = 2} < card {τ∈K. dim τ = 2} ∧
                boundary/frontier data are preserved"
```

The exact statement must match the existing predicates, but the architecture should be this: one lemma performs the fold/removal; Theorem 3.4 only performs induction and calls it.

Split the fold lemma into cases:

**Case 1: one boundary edge.**
This is the standard “remove an ear” case. The local fold is supported in the triangle plus its adjacent simplex. The reduced complex has one fewer 2-simplex.

**Case 2: two boundary edges.**
This is often geometrically easier but set-theoretically annoying. The free triangle is a corner of the disk; removing it changes the boundary polygon by replacing two edges with the remaining edge.

**Case 3: three boundary edges.**
This should be impossible in the large case or should collapse to the already-proved all-boundary closure lemma.

**Case 4: no boundary edge.**
This should contradict the “free boundary triangle” assumptions.

The worker should avoid trying to make one overloaded proof handle all cases without named case lemmas. The case split is a feature, not a problem.

### 4.4 Theorem 3.7 should reuse Theorem 3.4’s fold lemma

Theorem 3.7’s remaining hole is the support-control claim `h_support_in_U`. ([GitHub][3])

This should not be a second independent fold proof. It should be a support-refined version of the same fold-elimination lemma used for Theorem 3.4.

The right helper lemma is something like:

```isabelle
free_triangle_fold_elimination_support_prefix:
  assumes "free_triangle_fold_data ..."
      and "closed local fold carrier ⊆ U"
      and "open U"
  shows "∃h. homeomorphism h ... ∧ (∀x∉U. h x = x)"
```

Then Theorem 3.7 becomes:

1. pick the free triangle from Theorem 3.3;
2. choose the local fold neighborhood inside `U`;
3. apply the support-controlled fold lemma;
4. compose with the induction hypothesis;
5. prove the support of the composition is still inside `U`.

The last step should be a general lemma:

```isabelle
support_comp_subset:
  assumes "support f ⊆ U" and "support g ⊆ U"
  shows "support (f ∘ g) ⊆ U"
```

and similarly for inverse/composed homeomorphisms if needed.

---

## 5. Section 4.2: finish the arc-separation lemma, not the theorem body

Theorem 4.2 has already created the relevant candidate components `UQ` and `US`; the pending fact is `hD42_disjoint`. ([GitHub][3])

This is a classic Moise picture: an arc from `P` to `R` in a disk separates the boundary points/arcs lying on opposite sides in cyclic order `P Q R S`.

The worker should prove a reusable lemma:

```isabelle
polygon_disk_arc_opposite_boundary_points_separated_prefix:
  assumes "I is a polygonal disk"
      and "A is an arc from P to R"
      and "A ⊆ closure I"
      and "A ∩ frontier I = {P,R}"
      and "P,Q,R,S occur in cyclic order on frontier I"
  shows "Q and S lie in different components of closure I - A"
```

or, if the theorem uses small neighborhoods around `Q` and `S`, formulate it directly for those component sets.

The proof should be by contradiction:

1. assume `Q` and `S` lie in the same component of `I - A`;
2. extract a polygonal arc or broken line from `Q` to `S` avoiding `A`;
3. combine this with the boundary cyclic-order data;
4. apply the earlier crossing theorem / Jordan arc theorem already formalized in Sections 1–2.

Do not prove `hD42_disjoint` by component algebra alone. The disjointness is not algebraic; it is the separation theorem. The theorem body should only instantiate the reusable lemma.

A practical form:

```isabelle
have sep_QS:
  "connected_component_set (I - A) Q ≠ connected_component_set (I - A) S"
  using polygon_disk_arc_opposite_boundary_points_separated_prefix ...
```

Then derive `UQ ∩ US = {}` from standard connected-component facts.

---

## 6. Section 4.4: bricks should be replaced by one regular-neighborhood theorem

Theorem 4.4 is still the largest conceptual danger in the prefix file. It has five open book-step holes: brick decomposition, derived-neighborhood manifoldness, broken-line frontier, and two component facts. ([GitHub][3])

This is the point where a literal formalization of Moise’s “bricks” can become expensive. Bricks package too many facts:

* existence of an adapted finite decomposition,
* avoidance of two disjoint arcs/closed sets,
* manifoldness of the union of selected cells,
* frontier being a broken line,
* component behavior of the complement.

The better approach is to prove one regular-neighborhood theorem for polygonal arcs in a polygonal disk:

```isabelle
polygonal_arc_regular_neighborhood_in_disk_prefix:
  assumes "D is a polygonal disk"
      and "A is a polygonal arc in D"
      and "A avoids the specified boundary data"
  shows "∃N. polygonal_disk N ∧
             A ⊆ interior N ∧
             N ⊆ D ∧
             frontier N is a broken line ∧
             D - N has the required component behavior"
```

Then use this theorem to discharge all five `hD44_*` claims.

A book-faithful version can still mention bricks, but internally it should prove a regular-neighborhood lemma. For example:

```isabelle
geotop_brick_decomposition_exists_from_regular_neighborhood_prefix
geotop_regular_neighborhood_frontier_broken_line_prefix
geotop_regular_neighborhood_component_transfer_prefix
```

This avoids five separate in-theorem mini-projects.

The core construction can be done using compactness and mesh control:

1. The arcs/closed sets that must remain separated are compact.
2. Their distance is positive.
3. Choose a grid or triangulation mesh smaller than one third of that distance.
4. Let `N` be the union of cells meeting the target arc.
5. Prove no cell of `N` meets the forbidden arc/set.
6. Prove the frontier of `N` is a finite polygonal 1-complex.
7. Prove the complement components by applying the Section 4.2 separation lemma or a standard regular-neighborhood separation lemma.

The worker should not leave the five `hD44_*` facts as independent `sorry`s. They are all consequences of the same construction.

---

## 7. Figure 4.10 and graph-realization obligations

The active file still contains two finite graph realization holes:

```isabelle
geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

The first is for a finite connected nonisolated linear graph whose carrier is a polygon; the intended target is a subdivision of the frontier of a standard 2-simplex. ([GitHub][4])

The second is for a finite connected linear graph whose carrier is a broken line with a degree-one endpoint; the intended target is a standard boundary-arc fan. ([GitHub][4])

These should be treated as **finite graph enumeration problems**, not as planar topology problems.

### 7.1 Cycle case

Prove an abstract listing lemma:

```isabelle
finite_connected_degree_two_linear_graph_cycle_listing:
  assumes "finite linear graph L"
      and "connected carrier L"
      and "nonisolated"
      and "carrier L is a polygon"
  shows "∃vs. cyclic listing of the vertices of L ..."
```

Then prove a geometric realization lemma:

```isabelle
cycle_listing_realizes_standard_boundary_subdivision:
  assumes "cyclic listing vs ..."
  shows "∃F. F subdivides frontier of standard 2-simplex ∧
             geotop_isomorphism L F"
```

The target theorem then composes these two lemmas.

### 7.2 Boundary-arc chain case

Similarly, prove:

```isabelle
finite_connected_linear_graph_chain_listing_from_endpoint:
  assumes "carrier L is a broken line"
      and "w is a degree-one endpoint"
  shows "∃vs. chain listing from w to the other endpoint ..."
```

Then realize the chain as a subdivided boundary arc of a standard triangle:

```isabelle
chain_listing_realizes_standard_boundary_arc_fan:
  assumes "chain listing vs ..."
  shows "∃F c. standard boundary arc fan target ..."
```

The comments near the active hole already say the missing work is to recover the ordered edge chain, realize it as a subdivided boundary arc, and choose the matching endpoint. ([GitHub][4])

This split will make the proofs much shorter. The worker should avoid reasoning simultaneously about:

* graph connectivity,
* vertex degree,
* polygon/broken-line carrier geometry,
* cyclic order,
* standard target construction,
* complex isomorphism.

Each belongs in a separate lemma.

---

## 8. Local edge-star chart lemmas: strong warning about assumptions

The active local geometry holes are the most delicate remaining part. They look localized, but the current statements may be stronger than what is actually true unless their hypotheses imply more than is visible from the raw snippet.

### 8.1 One-sided semicircle separation

The open lemma is intended to choose a radius `r` and an arc `A` in the unique incident 2-simplex so that `U - A` is not connected. ([GitHub][4])

The intended proof should be Euclidean and explicit:

1. Affinely normalize the edge to the x-axis and the unique incident triangle to a closed half-plane sector.
2. Choose `r < s` small enough that:

   ```isabelle
   sphere p r ∩ local_carrier = sphere p r ∩ σ
   ```
3. Let:

   ```isabelle
   A = sphere p r ∩ σ
   ```

   which is a semicircular crosscut of the local half-disk.
4. Choose two witness points on opposite sides of `A`.
5. Show any path between them would make the continuous function `x ↦ dist x p` pass from `< r` to `> r`; hence it hits `sphere p r ∩ σ = A`.
6. Therefore the two witnesses lie in different components of `U - A`.

The proof should use the norm/intermediate-value argument, not a general Jordan theorem. This is one of the rare places where an analytic coordinate proof is simpler than abstract topology.

However, the worker should carefully re-check the exact statement. If `U` is an arbitrary subset of the polyhedron that merely contains a small local ball, then `U - A` might reconnect around the outside unless additional hypotheses prevent that. The lemma is safe if `U` is the relevant local disk/chart domain, or if the conclusion is only about a local domain such as `U ∩ ball p s`. If the current statement lacks that upper-locality or connectedness information, strengthen the assumptions or weaken the conclusion to the exact local contradiction needed.

### 8.2 Three incident triangles and small-circle complement connectedness

The open three-incident lemma tries to show that removing a small circle does **not** disconnect the relevant domain in the three-incident-edge case. The surrounding code has already built much of the finite cover/radius setup and invokes the explicit connectedness lemma. ([GitHub][4])

Again, first verify the statement. A global conclusion like:

```isabelle
top1_connected_on (U - sphere p eps)
```

usually requires some connectedness/locality hypothesis on `U`. A completely arbitrary `U` containing the small local carrier could have unrelated disconnected parts. If the visible assumptions do not imply `top1_connected_on U` or a local chart-domain condition, the lemma may be over-strong.

There is also a possible shortcut worth checking before investing heavily in this proof. Recent project reports mention same-complex two-triangle opposite-side/local-model infrastructure, and the active file now has strong local fan/link facts. ([GitHub][5])

In an embedded planar complex, three distinct 2-simplexes sharing the same edge are often impossible already by elementary affine geometry: two triangles sharing an edge must lie on opposite sides or violate the complex-intersection condition; a third triangle has no remaining side available. If the project has already proved a lemma of that form, then the entire “three incident edge faces” case can potentially be closed by contradiction before reaching the small-circle connectedness proof.

The worker should check whether a lemma like this already exists:

```isabelle
same_complex_two_2simplex_shared_edge_opposite_sides
```

If yes, prove:

```isabelle
no_three_2simplexes_share_edge_in_planar_complex
```

Then use that to eliminate the three-incident case. This may be dramatically simpler than formalizing Moise’s topological nonseparation picture.

If book-faithfulness requires preserving Moise’s route, then keep the three-incident small-circle lemma, but make it local and constructive:

```isabelle
three_page_local_star_minus_small_circle_connected:
  assumes "local star near p is exactly the three incident sectors"
      and "U_local = ball p s ∩ polyhedron K"
      and "sphere p eps ⊆ U_local"
      and "0 < eps" "eps < s"
  shows "top1_connected_on (U_local - sphere p eps)"
```

Then transfer this to the theorem’s actual `U` only after proving the needed connectedness and inclusion hypotheses.

### 8.3 Chart/Jordan-side containment

The remaining chart-side step asks for inner/outer components of the chart image of a 1-sphere, with the bounded side contained in the chart image of `U` and the outer side meeting the chart image of `U`. ([GitHub][4])

Do not prove this for arbitrary embedded 1-spheres in arbitrary open sets. Prove the exact convex-container lemma needed after mapping the local 2-cell to a standard triangle.

A good lemma is:

```isabelle
jordan_curve_inside_open_convex_set_bounded_side_subset:
  assumes "convex C"
      and "open C"
      and "J ⊆ C"
      and "geotop_is_1sphere J"
      and "bounded_component B of UNIV - J"
  shows "B ⊆ C"
```

For the standard triangle, `C` is the interior of the 2-simplex. Since `C` is convex, any point outside `C` can be connected to infinity by a ray or polygonal path avoiding `J`, so it belongs to the outer component. Therefore the bounded component must be inside `C`.

Then prove that the outer component meets `C` by choosing a point of `C` outside the bounded side, for instance near the triangle boundary but still in the interior.

This should close `hchart_image_sep` without developing a broad Jordan-side theory.

---

## 9. Recommended completion order

The worker should not finish holes in file order. The dependency-friendly order is:

### Step 1: update the dashboard

Run:

```bash
rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34
```

The June 5 status file is now likely stale because it still mentions 17 target `sorry`s and older next targets, while the raw prefix file shows several of those targets already proved. ([GitHub][1])

Update the status file immediately after confirming the live count. This prevents duplicate effort.

### Step 2: close the Section 3 selected-ear lemma

Target:

```isabelle
geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix
```

Use the already-proved all-boundary obstruction and selected-boundary-edge counting. Avoid a full dual-graph proof unless the selected-edge/cardinality approach fails.

### Step 3: close Theorem 3.4 and Theorem 3.7 together

Do not prove the fold once for Theorem 3.4 and again for Theorem 3.7. Prove a support-parametrized fold lemma, then instantiate it twice.

Theorem 3.4 uses the lemma without support constraints. Theorem 3.7 uses the same lemma with support inside `U`.

### Step 4: finish the two active graph realization holes

These are finite and combinatorial. They are likely easier than the remaining local topology if the worker introduces list/chain/cycle enumeration lemmas.

Targets:

```isabelle
geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

Prove graph listing first, standard target realization second.

### Step 5: re-evaluate the three-incident-edge route

Before proving the small-circle complement connectedness lemma, check whether the three-incident case is already impossible by planar complex geometry. If the project’s same-side/opposite-side triangle lemmas are strong enough, close the three-incident branch by contradiction.

If not, repair the statement so it is genuinely local and has the needed connectedness assumptions, then prove it by explicit path construction.

### Step 6: prove the one-sided semicircle separator

Use the distance-to-center intermediate-value proof in the normalized local half-plane/triangle. Keep it local. Avoid invoking a heavy Jordan theorem.

### Step 7: prove the chart/Jordan-side containment lemma

Use the convexity of the standard 2-simplex interior after applying the chart. The bounded side of a Jordan curve inside a convex open set remains inside that set.

### Step 8: finish Theorem 4.2

Prove the reusable opposite-boundary arc separation lemma, then discharge `hD42_disjoint`.

### Step 9: finish Theorem 4.4 last, unless another theorem requires it earlier

The brick theorem is probably the single largest remaining formalization task. Turn the five `hD44_*` holes into one regular-neighborhood theorem and one component-transfer theorem. Then the theorem body should close.

---

## 10. Main recommendations in compact form

The branch is now close enough that the worker should optimize for **proof architecture**, not brute-force local closure.

The most important actions are:

1. **Treat the current status report as stale until `rg` is rerun.**
   Several old Section 3 blockers now appear closed in the raw file.

2. **Finish Section 3 by proving the selected-boundary-ear lemma, then a fold-elimination lemma.**
   Theorem 3.3, 3.4, and 3.7 should become short wrappers.

3. **Turn Theorem 4.4 into a regular-neighborhood theorem.**
   Do not separately grind brick existence, frontier shape, manifoldness, and component behavior inside the theorem.

4. **Split graph realization into enumeration plus standard realization.**
   First get a cyclic/chain vertex list; then build the standard boundary subdivision.

5. **Be suspicious of the local `U - sphere` and `U - semicircle` statements.**
   Re-check whether `U` is constrained enough. If not, localize the statements or add the missing connectedness/chart-domain assumptions.

6. **Consider bypassing the three-incident small-circle proof by planar complex geometry.**
   If three 2-simplexes sharing one edge are already impossible in the embedded planar complex setting, this can save a large amount of topological proof work.

7. **Use explicit Euclidean normal forms for local chart lemmas.**
   Normalize by affine maps; use radius/norm intermediate-value arguments and constructed polygonal paths.

---

## 11. Final assessment

The worker has made the right kind of progress. The previous broad Section 3 base-case mess has been reduced substantially. The all-boundary and two-triangle machinery now looks proved; active local/star infrastructure has also improved. The remaining work is more concentrated and more mathematical.

The project still is not “just cleanup.” The remaining holes are exactly the hard Moise pictures:

* finite triangulated disk ears,
* fold induction with support,
* arc separation in a polygonal disk,
* regular neighborhoods/bricks,
* finite graph cycle/chain realization,
* local one-sided and three-sided edge-star chart contradictions.

The cleanest path to complete Sections 3 and 4 is to stop proving from the book theorem outward and instead prove the missing pictures as reusable lemmas. Once those lemmas exist, the top-level theorems should become straightforward applications, and the final sorry-free pass should be realistic.

[1]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/GEOTOP_SECTIONS_3_4_STATUS_2026_06_05.md "raw.githubusercontent.com"
[2]: https://github.com/JUrban/isa_geotop1/tree/codex-dev34-cache/tst "isa_geotop1/tst at codex-dev34-cache · JUrban/isa_geotop1 · GitHub"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/dev34/GeoTop_3_4.thy "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/GEOTOP_SECTIONS_3_4_REPORT.md "raw.githubusercontent.com"
