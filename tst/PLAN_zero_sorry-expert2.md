# Fresh report after the latest push: GeoTop / Moise Sections 3–4 on `codex-dev34-cache`

I restarted the inspection from the current pushed branch state. I did **not** run Isabelle locally, so I cannot independently certify the session build. I inspected the current branch layout, cache-busted raw theory files, and the worker’s reported hole list. The worker’s status is consistent with what I see: the project is much more advanced than before, but the remaining work is still substantial and mathematical, not merely tactical cleanup.

The old June 5 status file still reports **17 target `sorry`s**, so it should now be treated as stale relative to the pushed files and the worker’s updated report. The current branch has been split into more focused layers under `tst`, including `dev34_prefix_base`, `dev34_prefix_graph/cache`, `dev34_prefix_graph`, `dev34_prefix_mid`, `dev34_prefix`, and active `dev34`, which is a good sign that the worker has been isolating the hard packages instead of letting one giant prefix theory absorb everything. ([GitHub][1])

My current assessment:

> The worker’s “10 verified target holes” status is credible.
> The raw number is small, but the remaining holes are exactly the hard Moise picture-arguments: finite graph cycle/cut packages, Section 3 subdisk/fold induction, Theorem 4.2 theta separation, Theorem 4.4 bricks/regular neighborhoods, Figure 4.10 graph realization, endpoint fan realization, and one-sided local semicircle separation.

I agree with the worker’s conclusion: this is **not** “almost done” in the sense of missing a few `blast` or `simp` calls. It is “well-localized but still hard.”

---

## 1. Current structure and why the split matters

The pushed branch now has a much more refined target stack than in the earlier reports. The `tst` directory contains separate layers for graph cache, graph prefix, mid-prefix, final prefix, and active `dev34`, alongside support/open-star/link/local layers. This is important because the remaining `sorry`s are now concentrated into named packages instead of being scattered through the original monolithic `GeoTop_3_4_Prefix.thy`. ([GitHub][2])

There is also a dedicated `check_dev34_fast.sh` script with modes such as `holes`, `focus`, `focus-full`, `focus-warm`, `focus-prime`, `focus-status`, and specific split targets such as `prefix-graph-cache`, `prefix-graph`, `prefix-mid`, and `dev34`. That matches the worker’s process note about hot focused checks becoming much faster. The tooling split is now good enough that the worker should use focused iteration aggressively instead of rebuilding broad stacks after every small change. ([GitHub][3])

The most important architectural improvement is that the latest `tst/dev34_prefix/GeoTop_3_4_Prefix.thy` has been reduced almost entirely to the Theorem 4.4 brick/regular-neighborhood package. That file now imports the mid dirty layer and contains a single large book-step package around `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`. ([GitHub][4])

So the current state is much better organized than before. The project is not suffering from uncontrolled proof sprawl. It is suffering from ten hard residual packages.

---

## 2. Current hole map

Here is the current hole map, regrouped by mathematical theme rather than file order.

### A. Finite graph local/cycle package

There is one graph-cache hole:

```isabelle
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
```

This lives in `tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy`. The statement assumes a finite linear graph, a vertex `{w} ∈ L`, a simple-closed-curve carrier, and more than two incident edges at `w`, and aims to show that removing `w` disconnects the carrier. It is then used to prove that a polygonal finite linear graph has no branch vertex. ([GitHub][5])

There are two closely related holes in `tst/dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy`:

```isabelle
horbit_no_nonadjacent_reversed_book
hpoly_inter_subset_book
```

These occur inside the finite connected degree-two linear graph two-vertex boundary split proof. The comments identify the missing facts as a cycle-order/orbit fact ruling out non-adjacent reverse occurrences and a carrier-intersection fact saying the two cut path carriers meet only at the cut vertices `P` and `Q`. ([GitHub][6])

This is probably the best near-term target, exactly as the worker said.

### B. Section 3 disk/free-triangle/fold package

There are two Section 3 holes in `tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`.

The first is a subdisk induction-transfer book step. The surrounding comment says the proof needs to show that the side complexes `K1` and `K2` are smaller polygonal-disk triangulations, apply the strong induction hypothesis to obtain free triangles on the side disks, and transfer the selected boundary-edge witnesses back to the original disk. ([GitHub][7])

The second is:

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
```

This is now the central Section 3 fold package. It is support-parametric: it asks for a homeomorphism/normalization with identity outside `U`. Theorem 3.4 later uses it with `U = UNIV`, which is the right architecture. ([GitHub][7])

This means the worker has successfully compressed Theorem 3.4 and Theorem 3.7 into one hard fold-normalization lemma. That is exactly the right shape, but the lemma itself remains a genuine PL-topology package.

### C. Theorem 4.2 arc separation / theta contradiction

The third mid-prefix hole is the Theorem 4.2 separation step. The comment says the missing proof should normalize the disk and, if `Q` and `S` lie in the same component of the disk minus the arc, extract a broken line and apply the Theorem 2.8 theta-graph contradiction. ([GitHub][7])

This is not just a component-set calculation. It is the formal version of Moise’s “otherwise we get a theta curve” picture.

### D. Theorem 4.4 brick / regular-neighborhood package

The final prefix file now has the Theorem 4.4 brick package as a single combined hole:

```isabelle
hD44_book_steps
```

The comment explicitly bundles fine brick decomposition, regular-neighborhood construction, frontier broken-line proof, component-frontier facts, and cyclic-order transfer. ([GitHub][4])

This is likely the largest remaining formalization package. The worker should not attack it as “one `sorry` left in prefix.” It is a whole theorem’s worth of hidden topology.

### E. Active `dev34`: Figure 4.10 boundary cycle realization

The active `tst/dev34/GeoTop_3_4.thy` file has a hole in:

```isabelle
geotop_finite_connected_degree_two_linear_graph_boundary_subdivision_model_dev34
```

The comment says the intended proof is to enumerate the oriented successor orbit, build a subdivision of the frontier of a standard 2-simplex with the same cyclic length, and define the isomorphism by the cyclic vertex list. ([GitHub][8])

This is closely related to the graph-cycle split in the prefix graph layer. These should be handled as one graph-realization sprint, not as independent projects.

### F. Active `dev34`: endpoint chain / fan realization

The active file also has:

```isabelle
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

The local context already has endpoint and neighbor data. The comment says the remaining proof should enumerate the finite connected broken-line graph from the endpoint through the first neighbor, realize it as a subdivided boundary arc of a standard 2-simplex, choose an adjacent boundary vertex `c`, and verify the cone/fan inclusions. ([GitHub][8])

This is the path analogue of the boundary-cycle realization.

### G. Active `dev34`: one-sided semicircle separator

The final active hole is:

```isabelle
geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
```

The visible assumptions include a unique local one-sided simplex model near an edge point `p`, an equality

```isabelle
ball p s ∩ geotop_polyhedron K = ball p s ∩ σ
```

and inclusions placing the local polyhedron ball inside `U` and `U` inside the whole polyhedron. The goal is to construct a radius `r` and an arc `A` on the small sphere in `σ` such that `U - A` is disconnected. ([GitHub][8])

This is now a local Euclidean separation lemma. It should be proved by explicit geometry, not by another broad Jordan theorem.

---

## 3. Agreement with the worker’s status

The worker’s note is candid and mostly exactly right:

> “Status: not finished, and not in the ‘just clean up tactics’ phase.”

I agree. The current inventory is small, but the remaining holes are package holes. Several are theorem-sized formalizations hidden behind one `sorry`.

I also agree with the worker’s suggested best next target: the graph-cycle split in `dev34_prefix_graph`. It has only two holes inside a long proof where much of the local infrastructure is already established, and it is closely connected to the active Figure 4.10 boundary-cycle realization. The graph work is the best place to get visible progress from the improved focus-cache workflow. The `check_dev34_fast.sh` modes support exactly this style of focused iteration. ([GitHub][3])

The one refinement I would add is this:

> Treat the graph-cache branch-vertex lemma, the two graph-cycle split holes, and the active Figure 4.10 boundary-cycle realization as **one finite-graph sprint**.

They are not separate themes. Closing them together should simplify later active `dev34` work and remove a large class of graph-ordering uncertainty.

---

## 4. Best next target: graph sprint

### 4.1 Branch vertex local cutpoint package

The branch-vertex lemma says that if a finite linear graph has a simple-closed-curve carrier and a vertex with more than two incident edges, then deleting that vertex disconnects the carrier. It is used to show that a polygonal finite linear graph cannot have a branch vertex. ([GitHub][5])

Be careful here: the statement relies crucially on the **simple-closed-curve carrier** hypothesis. In an arbitrary finite graph, a vertex of degree greater than two does **not** necessarily imply that deleting the vertex disconnects the graph; theta-like graphs can reconnect away from the vertex. So the proof should not silently generalize to “degree > 2 implies cutpoint” for all finite graphs.

Recommended proof route:

1. Use the simple-closed-curve/local-1-manifold property of the carrier near `w`.
2. Show a sufficiently small local neighborhood of `w` in the finite linear graph consists of one open germ for each incident edge.
3. More than two incident edges gives at least three local punctured germs near `w`.
4. A simple closed curve minus a point has only the two local sides allowed by a 1-manifold circle model.
5. Contradict the “more than two incident edges” local structure.

A more combinatorial alternative is to prove that if `polyhedron L - {w}` were connected, then at least three incident germs plus connecting arcs away from `w` would create a theta subgraph in a simple closed curve, contradicting the existing simple-closed-curve facts. That is likely harder than the local-degree argument unless the theta machinery is already very easy to instantiate.

### 4.2 Cycle orbit no non-adjacent reverse

The `horbit_no_nonadjacent_reversed_book` hole should be handled as a pure finite-cycle enumeration lemma, not a planar geometry lemma. The current proof is already using an oriented successor orbit. The missing statement appears to rule out the same unoriented edge appearing later with reversed orientation except at the intended adjacent/cyclic positions. ([GitHub][6])

Recommended lemma shape:

```isabelle
oriented_successor_orbit_no_nonadjacent_reverse:
  assumes "degree_two finite connected linear graph data"
      and "orbit is minimal periodic"
      and "i < n" "j < n"
      and "edge_at i = reverse_edge_at j"
  shows "i = j + 1 mod n ∨ j = i + 1 mod n"
```

The key idea is minimality/injectivity of the oriented edge-state orbit before its first return. If a non-adjacent reversed edge appears, then the successor map has revisited an oriented state or its forced predecessor too early, contradicting the minimal orbit period.

Do not reason about geometric carriers here. This is a graph-state/permutation proof.

### 4.3 Two cut path carriers meet only at `P,Q`

The `hpoly_inter_subset_book` hole should then become straightforward. The proof should take an arbitrary point

```isabelle
x ∈ polyhedron K1 ∩ polyhedron K2
```

and reduce by simplex membership:

1. Pick simplexes `σ1 ∈ K1` and `σ2 ∈ K2` with `x ∈ σ1 ∩ σ2`.
2. Since this is a finite linear complex, the intersection of two 1-dimensional simplexes is either empty, a vertex, or the same edge.
3. If the intersection contains an edge, then the same edge occurs in both cut paths. The no-nonadjacent-reverse lemma rules this out except for the cut boundary edges.
4. If the intersection is a vertex, use cyclic-orbit vertex uniqueness: a vertex appears in both subpaths only if it is one of the cut vertices `P` or `Q`.

The existing proof already has a helper around “cycle cut if boundary edges absent and poly intersection subset,” so the aim should be to prove precisely the missing `polyhedron K1 ∩ polyhedron K2 ⊆ {P,Q}` fact and then let the existing downstream infrastructure fire. ([GitHub][6])

### 4.4 Active Figure 4.10 boundary cycle realization

After the graph split closes, move immediately to:

```isabelle
geotop_finite_connected_degree_two_linear_graph_boundary_subdivision_model_dev34
```

The active file’s own comment gives the right proof outline: enumerate the oriented successor orbit, construct a subdivision of the frontier of a standard 2-simplex with matching cyclic length, and define the isomorphism by the cyclic vertex list. ([GitHub][8])

The crucial implementation advice is to build two lemmas:

```isabelle
finite_degree_two_graph_has_cyclic_vertex_listing
cyclic_listing_realizes_standard_triangle_boundary_subdivision
```

The first lemma should know nothing about the standard 2-simplex. The second should know nothing about the original graph except the cyclic list. This split will prevent the proof from mixing graph connectivity, orbit minimality, affine geometry, and complex-isomorphism bookkeeping in one place.

---

## 5. Endpoint chain / fan realization

Once the cycle realization is done, the endpoint-chain/fan package is the natural next graph target:

```isabelle
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

The current context already has the endpoint `w`, its first neighbor `q`, connectedness, and endpoint data. The missing book step is to enumerate the finite connected broken-line graph from the endpoint through the first neighbor, realize it as a subdivided boundary arc of a standard 2-simplex, choose an adjacent boundary vertex `c`, and verify the cone/fan inclusions. ([GitHub][8])

This is the path analogue of the cycle case. Use a chain listing lemma:

```isabelle
finite_connected_linear_graph_endpoint_chain_listing:
  assumes "finite connected linear graph L"
      and "degree w = 1"
      and "q is the unique neighbor of w"
  shows "∃vs. distinct chain listing from w through q to the other endpoint"
```

Then use a target-realization lemma:

```isabelle
chain_listing_realizes_standard_boundary_arc_fan:
  assumes "chain listing vs"
  shows "∃L' c. boundary arc subdivision plus cone vertex c realizes the fan"
```

One likely source of pain is the statement about all finite nonempty vertex subsets `W` and convex hulls. Reduce it early:

```isabelle
finite_vertex_subset_convex_hull_in_linear_graph_cases:
  assumes "finite W" "W ≠ {}" "convex hull W ⊆ polyhedron L"
  shows "card W = 1 ∨ (card W = 2 ∧ W is the vertex set of an edge simplex)"
```

Once that case split exists, the fan inclusion obligations should become singleton/edge cases, not arbitrary finite-set geometry.

---

## 6. Section 3: subdisk induction transfer

The remaining Section 3 subdisk-transfer hole in `GeoTop_3_4_Prefix_Mid.thy` is no longer the entire theorem. It is a focused book step inside the non-free-boundary-triangle split/free-count argument. The comment says the missing work is to prove that the two side complexes are smaller polygonal-disk triangulations, apply the strong induction hypothesis to each side, and transfer the resulting selected boundary-edge witnesses back to the original disk. ([GitHub][7])

Do not try to close this as one monolithic `have`. Split it into four helper lemmas:

```isabelle
subdisk_side_complex_is_polygon_disk_triangulation
subdisk_side_complex_two_simplex_count_strictly_smaller
side_free_triangle_selected_boundary_edge_transfer
side_free_triangle_free_in_parent_or_yields_parent_free_triangle
```

The likely proof shape:

1. The non-free boundary triangle creates a cut arc/edge that decomposes the disk carrier into two polygonal subdisks.
2. Each side inherits a subcomplex from `K`.
3. Each inherited side has strictly fewer 2-simplexes than `K`.
4. Strong induction gives a free triangle on one side or both sides.
5. If the selected free triangle is not the separator/boundary triangle, its free-boundary data transfer directly to the parent disk.
6. If the selected triangle is adjacent to the cut, use the other side or a boundary-count lemma to avoid choosing the artificial cut triangle.
7. The already-proved all-boundary and two-boundary-triangle infrastructure should eliminate the small exceptional cases.

The worker has already made the right move by isolating the book step. The finish now depends on making inheritance and transfer lemmas precise.

---

## 7. Section 3: fold normalization with support

The fold package

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
```

is now the Section 3 fold bottleneck. It asks for a supported normalization/homeomorphism and is later used to prove Theorem 3.4 with `U = UNIV`, while the support refinement is what Theorem 3.7 needs. ([GitHub][7])

This is excellent architecture. The worker should preserve it. The wrong move would be to prove an unsupported Theorem 3.4 first and then separately redo the support-controlled fold for Theorem 3.7. The current support-parametric lemma should be proved once.

Recommended split:

```isabelle
free_triangle_fold_case_one_boundary_edge_supported
free_triangle_fold_case_two_boundary_edges_supported
free_triangle_fold_case_three_boundary_edges_impossible_or_trivial
fold_reduces_two_simplex_count
fold_preserves_polygon_disk_boundary_data
fold_support_subset_U
homeomorphism_support_composition_subset
```

The induction proof should then become:

1. Pick a free triangle from the Section 3 free-triangle theorem.
2. Choose a local fold neighborhood inside `U`.
3. Apply the relevant boundary-contact fold case.
4. Apply the induction hypothesis to the smaller disk/complex.
5. Compose homeomorphisms.
6. Use support-composition lemmas to preserve identity outside `U`.

A key engineering recommendation: keep the fold map local. It should be built on the triangle plus its immediate neighboring carrier, then extended by identity. Proving a global PL homeomorphism from scratch at each induction step will be too expensive.

---

## 8. Theorem 4.2: theta contradiction

The Theorem 4.2 hole is now clearly identified as an arc separation/theta contradiction. The visible proof has already established distinctness and endpoint hygiene facts around the boundary points and arc; the remaining comment says that if `Q` and `S` lie in the same component of `I - A`, one should extract a broken line and apply the Theorem 2.8 theta-graph contradiction. ([GitHub][7])

Recommended reusable lemma:

```isabelle
polygon_disk_opposite_boundary_arc_separation_prefix:
  assumes "I is a polygonal disk"
      and "A is an arc from P to R"
      and "A ∩ frontier I = {P,R}"
      and "P,Q,R,S occur in cyclic order on frontier I"
  shows "Q and S lie in different components of I - A"
```

A practical proof strategy:

1. Assume `Q` and `S` are in the same component of `I - A`.
2. Extract a path between them inside `I - A`.
3. Replace the path with a polygonal arc or broken line, using polygonal approximation inside the open set if needed.
4. Combine that `Q`–`S` arc with the original `P`–`R` arc and the appropriate boundary arcs.
5. Invoke the existing theta graph contradiction, presumably Moise/Theorem 2.8 as the comment says.
6. Transfer the contradiction back to the component statement.

The endpoint issue is the main danger. Boundary points may lie on the frontier rather than in an open interior set, so the worker may need a small perturbation lemma:

```isabelle
same_component_boundary_point_to_nearby_interior_point
```

or a formulation using boundary arcs with endpoints removed. This should be solved once, not repeatedly inside Theorem 4.2.

---

## 9. Theorem 4.4: bricks / regular neighborhoods

The latest final prefix file has compressed Theorem 4.4 into one package:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

with the single open book step `hD44_book_steps`. The comment says this one step includes fine brick decomposition, regular-neighborhood construction, frontier broken-line facts, component-frontier facts, and cyclic transfer. ([GitHub][4])

This is probably the **largest remaining hole**, even though it is only one `sorry`.

My recommendation is still: do **not** formalize Moise’s bricks literally unless the necessary brick infrastructure is already nearly complete. Instead, prove a regular-neighborhood theorem for a polygonal arc in a polygonal disk.

Target lemma:

```isabelle
polygonal_arc_regular_neighborhood_in_polygon_disk_prefix:
  assumes "D is a polygonal disk"
      and "A1 is a polygonal arc in D"
      and "A1 is disjoint from A2 except prescribed endpoints"
      and "A2 / forbidden sets are compact and separated"
  shows "∃N. polygonal_disk N ∧
             A1 ⊆ interior N ∧
             N ⊆ D ∧
             N ∩ A2 has only prescribed endpoint behavior ∧
             frontier N is a broken line ∧
             D - N has the required component transfer"
```

Then discharge `hD44_book_steps` by instantiating this regular-neighborhood theorem.

A literal brick approach would be:

1. Normalize the polygonal disk.
2. Use compactness of the two disjoint arcs/closed sets to get positive distance.
3. Choose a grid mesh smaller than the separation distance.
4. Let `N` be the union of grid bricks meeting one arc.
5. Prove `N` avoids the forbidden arc/set.
6. Prove the frontier is a finite broken line.
7. Prove the complement component behavior.

That is mathematically clear but formalization-heavy. A triangulated regular neighborhood using existing complex/subdivision machinery is likely cheaper than building a full rectangular grid theory.

This should **not** be the next target. Leave D44 until the graph and local active holes are reduced, unless some downstream dependency forces it.

---

## 10. One-sided semicircle separator

The remaining local chart lemma is:

```isabelle
geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
```

The assumptions give a local equality between the polyhedron and a single 2-simplex inside `ball p s`, and place the local polyhedron ball inside `U`, while also assuming `U` is contained in the whole polyhedron. ([GitHub][8])

This should be proved analytically.

Recommended construction:

1. Choose `r` with `0 < r < s` small enough that the circle around `p` cuts the incident simplex in the standard semicircle/crosscut.
2. Define exactly:

   ```isabelle
   A = sphere p r ∩ σ
   ```

   or the corresponding connected semicircular component if the raw intersection contains extra degeneracies.
3. Prove `arc A`.
4. Pick one witness point in the local inner cap:

   ```isabelle
   x ∈ U ∩ ball p r
   ```

   and one witness point in the local outer part:

   ```isabelle
   y ∈ U ∩ (ball p s - closed_ball p r)
   ```
5. Suppose a connected subset/path in `U - A` joins `x` to `y`.
6. Apply continuity of the distance function `z ↦ dist z p`. Since the distance goes from `< r` to `> r`, any path from `x` to `y` hits `sphere p r`.
7. Because the hit point lies inside `ball p s ∩ geotop_polyhedron K`, the local equality gives that it lies in `σ`.
8. Since `A` is the relevant sphere intersection with `σ`, the path hits `A`, contradiction.

The key technical point is to construct `A` as the full separating sphere/simplex intersection used by the distance argument. If the statement only keeps `A ⊆ sphere p r ∩ σ`, the proof must still show every possible crossing point belongs to `A`; equality is much easier.

Also, re-check the global strength of the conclusion. The statement concludes `¬ connected_on (U - A)`. The assumptions may be sufficient because any path from a local inner witness to a local outer witness must cross the small sphere before leaving the local ball. But the proof should explicitly use the **first radius-crossing** argument: take the first time the path reaches distance `r`; before that time it remains inside `ball p s`, so the local equality applies.

That “first crossing” version avoids the worry that `U` might reconnect far away.

---

## 11. Recommended finish order

I would revise the worker’s next-target plan only slightly.

### Phase 1: graph sprint

Close these together:

1. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
2. `horbit_no_nonadjacent_reversed_book`
3. `hpoly_inter_subset_book`
4. `geotop_finite_connected_degree_two_linear_graph_boundary_subdivision_model_dev34`

The graph-cycle split is the best immediate target, but the branch-vertex cache lemma is adjacent and may be needed to stabilize no-branch/degree-two assumptions. The Figure 4.10 realization should follow immediately because it can reuse the same cyclic enumeration.

### Phase 2: endpoint chain / fan realization

Close:

```isabelle
geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
```

This is the path analogue of the cycle case and should benefit from the same enumeration machinery.

### Phase 3: one-sided semicircle separator

Close:

```isabelle
geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
```

This is local and explicit. It is not trivial, but it is smaller and more analytic than D42, D44, or the fold package.

### Phase 4: Section 3 subdisk transfer

Close the subdisk induction transfer after the graph active layer is calmer. Split into side-disk inheritance, strict cardinality, induction application, and witness transfer.

### Phase 5: Section 3 fold normalization

Close the support-parametric fold package. This is central to finishing Theorems 3.4 and 3.7 cleanly.

### Phase 6: Theorem 4.2 theta separation

Close the reusable opposite-boundary arc separation lemma and then instantiate it inside Theorem 4.2.

### Phase 7: Theorem 4.4 brick / regular neighborhood

Leave the brick package last unless dependencies force it. It is the biggest proof package and should be approached with a regular-neighborhood theorem, not a literal line-by-line brick formalization.

---

## 12. Process recommendations

Use the new focused workflow as the default. The script explicitly supports `holes`, focus modes, focus warm/prime/status, and separate graph/mid/dev34 targets. The worker should keep using hot focused checks for the graph sprint and only run broader checks after a package closes. ([GitHub][3])

For each remaining hole, the worker should create a tiny local dashboard at the top of the focus file:

```isabelle
(* Remaining package obligations:
   1. ...
   2. ...
   3. ...
*)
```

Then turn each English bullet into a named lemma. The main danger now is not losing track of syntax; it is letting one `have ... sorry` continue to hide five different facts.

The status report should also stop counting only raw `sorry`s. It should classify each remaining `sorry` as one of:

```text
small local tactic
medium finite-combinatorial package
large PL-topology package
large regular-neighborhood/package theorem
```

Right now the count is 10, but by effort it is more like:

* 3 graph/cycle enumeration packages,
* 2 Section 3 PL-disk/fold packages,
* 1 theta separation package,
* 1 very large D44 regular-neighborhood package,
* 2 active graph realization packages,
* 1 local Euclidean separator.

That is why the worker’s “not just cleanup” framing is important.

---

## 13. Direct reply to the worker’s status

The worker’s status is accurate and appropriately cautious.

I would reply along these lines:

> I agree that the project is not yet in final tactic-cleanup mode. The 10-hole count is real progress, but the remaining holes are package-level. The most promising next move is indeed the `dev34_prefix_graph` cycle split, especially with the hot focus cache. I would treat the branch-vertex cutpoint lemma, the two cycle-split holes, and the active Figure 4.10 boundary-cycle realization as one graph sprint. After that, do endpoint-chain/fan and one-sided semicircle. The broader geometry packages—Section 3 fold normalization, Theorem 4.2 theta separation, and Theorem 4.4 bricks—should be handled as named reusable lemmas, not patched inside the theorem bodies.

That is the honest state: the branch is structurally much closer, but there is still significant mathematical formalization left. The project is now well-localized enough that a disciplined sequence of package closures should finish Sections 3 and 4, but nobody should expect the remaining ten `sorry`s to collapse from automation alone.

[1]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/GEOTOP_SECTIONS_3_4_STATUS_2026_06_05.md "raw.githubusercontent.com"
[2]: https://github.com/JUrban/isa_geotop1/tree/codex-dev34-cache/tst?cb=202606071202 "isa_geotop1/tst at codex-dev34-cache · JUrban/isa_geotop1 · GitHub"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/check_dev34_fast.sh?cb=202606071202 "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy?cb=202606071200 "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy?cb=202606071201 "raw.githubusercontent.com"
[6]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy?cb=202606071201 "raw.githubusercontent.com"
[7]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy?cb=202606071201 "raw.githubusercontent.com"
[8]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34/GeoTop_3_4.thy?cb=202606071201 "raw.githubusercontent.com"
