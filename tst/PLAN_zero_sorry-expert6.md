# Fresh audit at commit `96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d`

I re-audited the pushed branch at the exact commit you gave. I did **not** run Isabelle locally, so I cannot independently certify the build. I inspected the current raw theory files, the latest commit message, the fast-cache report, and the live raw `sorry` locations.

The worker’s latest report is now accurate for the pushed state:

> The live target is down to **3 remaining `sorry`s**:
> two in the Figure 3.3 supported fold machinery in `dev34_prefix_mid`, and one in the Theorem 4.4 brick / regular-neighborhood component-transfer package in `dev34_prefix`.

The previous “graph bridge next” advice is obsolete for this commit. The raw graph-cache file at `96e32ef…` has no `sorry` match, and the branch-vertex three-germs package now appears proved and used downstream. ([GitHub][1])

The current remaining `sorry`s are:

```text
tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:37615
  inside geotop_free_triangle_one_boundary_edge_supported_fold_prefix

tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:39250
  inside geotop_free_triangle_two_boundary_edges_supported_inverse_fold_prefix

tst/dev34_prefix/GeoTop_3_4_Prefix.thy:651
  inside geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

The raw web viewer compresses some source lines, but it shows the same two mid-prefix fold holes and the final prefix D44 hole. ([GitHub][2])

---

## 1. High-level status

Sections 3 and 4 are no longer broadly open. The project has reached a final, sharply localized phase.

Section 3.3 is now effectively closed in the pushed state. The theorem wrapper is short: it calls the stronger lemma proving at least two free 2-simplexes and then extracts one witness. ([GitHub][2]) The long Moise Figure 3.2 side-complex and parent-boundary witness-transfer struggle has therefore been absorbed into finished infrastructure.

Theorem 3.4 is still open only through the Figure 3.3 fold constructors. The theorem states the polygon-to-simplex-frontier homeomorphism result and its proof is wired through the fold-normalization induction. ([GitHub][2]) Theorems 3.5 and 3.6 are downstream wrappers of 3.4, and Theorem 3.7 is the supported version that also depends on the same support-parametric fold-normalization machinery. ([GitHub][2])

Section 4.2 is now closed in the live source: `Theorem_GT_4_2` calls the opposite-boundary decomposition theorem and packages the two open sides. ([GitHub][2]) Theorem 4.4 remains the only open Section 4 theorem package, with the desired conclusion that `Q` and `S` lie in the frontier of the same component of the polygonal interior minus the two arcs. ([GitHub][3])

So the dependency picture is now:

```text
Section 3:
  3.1 closed
  3.2 closed
  3.3 closed / no longer a live blocker
  3.4 blocked by Figure 3.3 Case 1 + Case 2 folds
  3.5 downstream of 3.4
  3.6 downstream of 3.4
  3.7 blocked by the same supported fold package

Section 4:
  4.1 closed
  4.2 closed
  4.3 closed
  4.4 open: brick / regular-neighborhood component transfer
```

This is genuinely close in structure, but not “just tactics.” The remaining three holes are exactly the final constructive Moise picture arguments.

---

## 2. What the latest commit changed

The latest commit, `96e32ef`, is titled **“Record Figure 3.3 triangle vertex images.”** It continues the Moise Theorem 3.4 / Figure 3.3 Case 1 carrier-isomorphism setup. The commit records the images of the four source triangles under the explicit vertex map: `v0 v4 v5` maps to `v0 v4 v1`, `v2 v4 v5` maps to `v2 v4 v1`, `v0 v5 v3` maps to `v0 v1 v3`, and `v2 v5 v3` maps to `v2 v1 v3`. The commit message says the next step is to lift these vertex-set image identities from top triangles to face-closure carriers, obtain the simplex-membership iff needed for `geotop_isomorphism`, and then invoke `geotop_isomorphism_induces_PLH`. ([GitHub][4])

That is exactly the right next move. The proof is no longer searching for the Figure 3.3 geometry. It has the explicit vertex map and the four top-triangle image facts. The remaining Case 1 task is to package those facts into a carrier isomorphism / PL homeomorphism and then prove the support and boundary-image conclusions.

The previous commit `b191ca4` had already proved the Figure 3.3 vertex map is a bijection from the source carrier vertices `{v0,v2,v3,v4,v5}` to the target carrier vertices `{v0,v1,v2,v3,v4}`, fixing `v0,v2,v3,v4` and sending `v5` to `v1`. Its message also identified the next work as proving the simplex-membership iff and applying the PLH machinery. ([GitHub][5])

So the recent commits are coherent: first prove the vertex map is a bijection; then prove top-triangle vertex images; next prove face-closure carrier isomorphism.

---

## 3. Remaining hole 1: Figure 3.3 Case 1 supported fold

The first remaining mid-prefix `sorry` is inside:

```isabelle
geotop_free_triangle_one_boundary_edge_supported_fold_prefix
```

The relevant local subclaim is named:

```isabelle
hfigure33_book_local_simplicial_extension_boundary_control
```

It asks for auxiliary vertices `v3 v4 v5` and a plane homeomorphism `f` with the expected Figure 3.3 properties: collinearity and off-line conditions, the source and target carrier intersection identities, support inside `U`, identity outside the source carrier, vertex images, simplicial behavior over the four source triangles, the old edge image `?B₀₂ = closed_segment v0 v5 ∪ closed_segment v2 v5`, and the retained boundary contact condition `C_O ∩ source_carrier ⊆ {v0,v2}`. ([GitHub][2])

This is the best next target. It is smaller than D44, and it unlocks the two main Section 3 theorems.

### 3.1 What not to do

Do not try to solve the whole fold theorem by a large ad hoc `metis` or by adding another existential wrapper. The proof is now at the right granularity: it needs a local carrier isomorphism, then PLH, then identity-outside support.

Do not change the high-level statement unless absolutely necessary. The latest commit says the supported fold statement was not changed, and that is good. ([GitHub][4])

### 3.2 Recommended proof decomposition

The next proof step should be a face-closure lifting lemma:

```isabelle
figure33_vertex_map_face_closure_membership_iff:
  assumes source/target top triangle data
      and vertex map φ fixes v0 v2 v3 v4 and sends v5 to v1
      and the four top triangle vertex-image identities
  shows
    geotop_convex_hull W ∈ source_carrier
    ⟷ geotop_convex_hull (φ ` W) ∈ target_carrier
```

The actual statement should match the existing definitions, but the idea is: stop reasoning about the four 2-simplexes only; prove the map preserves **all faces** generated by those four triangles.

The proof should split every source-carrier simplex into:

```text
top triangle itself
or a face of one of the four top triangles
```

Then map the corresponding vertex subset under the already-proved vertex map. For a face of `convex_hull {v0,v4,v5}`, for example, the image must be a face of `convex_hull {v0,v4,v1}`. Repeat for the other three top triangles, but package this as a generic finite-subset lemma rather than four long copied blocks.

After this, prove:

```isabelle
figure33_source_target_carrier_isomorphism:
  geotop_isomorphism source_carrier target_carrier φ
```

Then use the existing PLH infrastructure. The index shows the project already has `geotop_isomorphism_induces_PLH`, and the current commit explicitly names it as the next intended tool. ([GitHub][4])

### 3.3 The main risk: extension by identity

The worker’s status says the main remaining risk is extension-by-identity/support control. That is correct.

The local isomorphism gives a PLH between the source and target carriers. The fold theorem, however, wants a **plane homeomorphism**:

```isabelle
top1_homeomorphism_on UNIV geotop_euclidean_topology
  UNIV geotop_euclidean_topology f
```

with:

```isabelle
∀P∈UNIV - U. f P = P
```

The current local subclaim already asks for `f` to be identity outside the source carrier and for the source carrier polyhedron to be contained in `U`. Once those are obtained, the support step itself should be short:

```isabelle
source_carrier ⊆ U
∀P∈UNIV - source_carrier. f P = P
⟹ ∀P∈UNIV - U. f P = P
```

The file already contains support-composition and inverse-support lemmas for later use: `geotop_plane_homeomorphism_fixed_outside_comp_prefix`, `geotop_plane_homeomorphism_fixed_outside_inv_prefix`, and `geotop_plane_homeomorphism_fixed_outside_sym_prefix`. ([GitHub][2])

What is still needed in Case 1 is the patching theorem:

```isabelle
local_PLH_on_closed_carrier_extends_by_identity_to_plane_homeomorphism
```

or whatever existing theorem already plays this role. If there is no such lemma, create it once. It should say, in effect:

```isabelle
assumes local carrier C is a closed polygonal disk / finite polyhedron
    and f is a PLH C → C'
    and f agrees with identity on frontier C
    and C ⊆ U
shows ∃F. plane homeomorphism F
        ∧ F agrees with f on C
        ∧ F is identity outside C
        ∧ hence F is identity outside U
```

This is the point where the worker should be most careful. Proving all the triangle vertex images is not enough unless the patch across the carrier frontier is justified.

### 3.4 Boundary image facts

Once `f` is built, the two boundary facts should be proved separately:

```isabelle
f ` ?B₀₂ = ?B₀₁₂
f ` C_O = C_O
```

The first should follow from the edge-face images induced by the simplicial map. Since `?B₀₂` is explicitly represented as the two old segments through `v5`, and `f v5 = v1`, the image is the broken replacement arc through `v1`.

The second should use:

```isabelle
C_O ∩ source_carrier ⊆ {v0,v2}
```

plus the fact that `f` fixes `v0` and `v2` and is identity outside the source carrier. In other words, points of `C_O` outside the local carrier are fixed by support, and the only points of `C_O` inside the local carrier are fixed vertices.

This is a good small lemma:

```isabelle
figure33_retained_boundary_arc_fixed:
  assumes "C_O ∩ carrier ⊆ {v0,v2}"
      and "f v0 = v0" "f v2 = v2"
      and "∀x∉carrier. f x = x"
  shows "f ` C_O = C_O"
```

Use this instead of repeatedly unfolding the retained boundary set.

---

## 4. Remaining hole 2: Figure 3.3 Case 2 inverse/corner fold

The second mid-prefix `sorry` is inside:

```isabelle
geotop_free_triangle_two_boundary_edges_supported_inverse_fold_prefix
```

The immediate subclaim is:

```isabelle
hfigure33_corner_inverse_boundary_carrier
```

It must produce a polygon `J'` and a supported plane homeomorphism `f` such that deleting the corner triangle `θ` gives a complex whose polyhedron is the closed disk bounded by `J'`, the new closed disk lies in `U`, and `f ` J = J'`. The surrounding proof has already obtained that `K - {θ}` is a complex, finite, and has fewer 2-simplexes. ([GitHub][2])

This should come after Case 1.

### 4.1 Derive it from Case 1 if possible

The comments in the theory describe Case 2 as the inverse/corner version of Figure 3.3. The worker should try hard to derive it from the Case 1 local PL construction rather than build a second plane homeomorphism from scratch.

The idea is:

1. Normalize the two-boundary-edge corner as the **target** of a Case 1 fold.
2. Apply the Case 1 local construction in the reverse picture.
3. Take the inverse homeomorphism.
4. Use the already-proved inverse-support lemma to show the inverse is still identity outside `U`.
5. Let the new boundary be the old polygon with the two corner edges replaced by the remaining edge.

Because the file already has inverse-support infrastructure, the inverse part should not be the hard part. ([GitHub][2])

### 4.2 Do not redo count and complex deletion

The surrounding proof already has:

```isabelle
geotop_is_complex (K - {θ})
finite (K - {θ})
card two_simplexes(K - {θ}) < card two_simplexes(K)
```

via the delete-2-simplex package. The only missing part is the boundary carrier and supported homeomorphism package. Do not mix the finite count proof into the local fold construction again.

### 4.3 Likely helper theorem

A good target is:

```isabelle
figure33_corner_inverse_boundary_carrier_from_case1:
  assumes θ frontier = xy ∪ xz ∪ yz
      and θ ∩ J = xy ∪ xz
      and θ is free with two boundary edges
      and closed disk carrier ⊆ U
  shows ∃J' f.
      geotop_is_polygon J'
    ∧ geotop_polyhedron (K - {θ})
        = closure_on UNIV geotop_euclidean_topology
            (geotop_polygon_interior J')
    ∧ closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J') ⊆ U
    ∧ top1_homeomorphism_on UNIV ... UNIV ... f
    ∧ (∀P∈UNIV-U. f P = P)
    ∧ f ` J = J'
```

If Case 1 is not reusable directly due to mismatched hypotheses, introduce a smaller shared local lemma for “Figure 3.3 four-piece PL fold/inverse” and let both Case 1 and Case 2 instantiate it.

---

## 5. What happens after the two fold holes close

Once the two fold constructors close, the Section 3 wrappers should fall through the existing code.

The dispatcher `geotop_figure33_contact_cases_supported_fold_prefix` already routes empty, one-boundary, and two-boundary contact cases into the corresponding supported fold packages. The fold-reduction theorem then feeds the full fold-normalization induction. Theorem 3.7 already calls that support-parametric normalization theorem directly. ([GitHub][2])

After the two folds close, check these in order:

```isabelle
geotop_figure33_contact_cases_supported_fold_prefix
geotop_free_triangle_supported_fold_reduction_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
Theorem_GT_3_4
Theorem_GT_3_5
Theorem_GT_3_6
Theorem_GT_3_7
```

Theorems 3.5 and 3.6 should not require new mathematical work; they are downstream of 3.4. ([GitHub][2])

---

## 6. Remaining hole 3: Theorem 4.4 brick / regular-neighborhood package

The final `sorry` is in:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

The file already has a brick-decomposition definition and several useful D44 preparations. It has proved compactness/closedness and positive separation for two disjoint arcs, a fine subdivided disk carrier meeting `A1` but missing `A2`, a named carrier `N` with `A1 ⊆ N` and `N ∩ A2 = {}`, and local connected access neighborhoods near `Q` and `S` inside the complement of `A1 ∪ A2`. The remaining `hD44_component_transfer` says to use the named fine disk carrier and the local access data to produce one component whose frontier contains both `Q` and `S`. ([GitHub][3])

This is the largest remaining proof package. It should stay last.

### 6.1 Use the already-built local access data

The existing proof has local connected open sets near `Q` and `S`:

```isabelle
U_Q ⊆ polygon_interior J - (A1 ∪ A2)
U_S ⊆ polygon_interior J - (A1 ∪ A2)
Q ∈ frontier U_Q
S ∈ frontier U_S
Q' ∈ U_Q
S' ∈ U_S
```

The final target can be reduced to showing that `Q'` and `S'` lie in the **same component** of:

```isabelle
D = geotop_polygon_interior J - (A1 ∪ A2)
```

If that is proved, then define:

```isabelle
C = geotop_component_at UNIV geotop_euclidean_topology D Q'
```

and use connected-component absorption to get `U_Q ⊆ C` and `U_S ⊆ C`. Frontier transfer should then give `Q ∈ frontier C` and `S ∈ frontier C`.

This suggests a sharper remaining lemma:

```isabelle
D44_QS_witnesses_same_component_from_fine_A1_neighborhood:
  assumes named fine disk carrier N
      and A1 ⊆ N
      and N ∩ A2 = {}
      and local access witnesses Q' S'
  shows
    geotop_component_at UNIV geotop_euclidean_topology
      (geotop_polygon_interior J - (A1 ∪ A2)) Q'
    =
    geotop_component_at UNIV geotop_euclidean_topology
      (geotop_polygon_interior J - (A1 ∪ A2)) S'
```

Then `hD44_component_transfer` becomes mostly packaging.

### 6.2 Prove D44 as a regular-neighborhood theorem, not a general brick theory

The file defines `geotop_brick_decomposition`, but the current proof has moved toward a triangulated/fine-subdivision carrier package rather than a full arbitrary brick-decomposition formalization. That is a good choice. The D44 statement does not need a reusable theory of every brick decomposition in the plane; it needs one regular neighborhood of `A1` inside the closed disk that avoids `A2` and has enough frontier structure to connect the `Q` and `S` sides.

The practical internal theorem should be:

```isabelle
polygon_two_endpoint_arcs_regular_neighborhood_component_transfer:
  assumes polygon/cyclic-order data
      and A1,A2 are disjoint endpoint arcs in the closed disk
      and N is a sufficiently fine carrier with A1 ⊆ N and N ∩ A2 = {}
  shows ∃C. Q ∈ frontier C
          ∧ S ∈ frontier C
          ∧ C is a component of polygon_interior J - (A1 ∪ A2)
```

The proof can still be book-faithful:

1. Restrict the fine carrier `N` to the closed polygonal disk.
2. Analyze the relevant frontier component through `P`.
3. Extract a broken-line subarc with endpoints `V,W` on `J`.
4. Show `V,W` lie in the frontier of one component of the complement.
5. Use cyclic order and the already-closed Theorem 4.2/D42 separation package to transfer the frontier statement from `V,W` to `Q,S`.

The critical point is to avoid reopening D42. Theorem 4.2 is already available and should be the separation engine. ([GitHub][2])

### 6.3 A possible shorter route

Given the current data, there may be a shorter component proof:

* `A1 ⊆ N` and `N ∩ A2 = {}`.
* The complement of a regular neighborhood of `A1` in the disk should contain a component adjacent to the boundary arc from `Q` to `S` avoiding `P` and `R`.
* Since `Q` and `S` are both away from the endpoints and away from `A1 ∪ A2`, their small local access neighborhoods should attach to that same outside component.

If existing cyclic-order lemmas can identify the boundary arc from `Q` to `S` that avoids `P,R`, this route may be cheaper than proving a full “frontier component is a 1-sphere” statement.

But only use this shortcut if the needed boundary-arc infrastructure is already present. Otherwise, the regular-neighborhood theorem is safer.

---

## 7. Recommended finishing order

### Step 1: Finish Figure 3.3 Case 1

Target:

```isabelle
geotop_free_triangle_one_boundary_edge_supported_fold_prefix
```

Immediate subtarget:

```isabelle
hfigure33_book_local_simplicial_extension_boundary_control
```

Do the face-closure carrier isomorphism next. The latest commit explicitly says this is the next proof step: lift the top-triangle vertex image identities to face-closure carriers, obtain the simplex-membership iff, and invoke `geotop_isomorphism_induces_PLH`. ([GitHub][4])

### Step 2: Finish Figure 3.3 Case 2

Target:

```isabelle
geotop_free_triangle_two_boundary_edges_supported_inverse_fold_prefix
```

Immediate subtarget:

```isabelle
hfigure33_corner_inverse_boundary_carrier
```

Derive it from Case 1 if possible. Reuse inverse-support infrastructure, and do not redo the deletion count proof.

### Step 3: Verify all Section 3 wrappers

Run the mid-fold focus and then the broader mid-prefix check. The key wrappers should be Theorem 3.4 through Theorem 3.7. The source shows 3.7 uses the support-parametric fold-normalization package directly. ([GitHub][2])

### Step 4: Finish D44

Target:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

Reduce it to same-component membership for the local witnesses `Q'` and `S'`, using the named fine disk carrier and local access package already present.

### Step 5: Final verification

The fast-cache report says `holes` is an inventory command, not a build, and that focused split checks are for iteration rather than final certification. It recommends broader checks at package boundaries and a real final build after all target `sorry`s are gone. ([GitHub][6])

Use something like:

```bash
./check_dev34_fast.sh holes
TIMEOUT=240s ./check_dev34_fast.sh focus mid-figure33-one
TIMEOUT=240s ./check_dev34_fast.sh focus mid-fold
TIMEOUT=240s ./check_dev34_fast.sh focus prefix-d44
bash gen_index.sh
bash gen_stmt_index.sh
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-through dev34_prefix/GeoTop_3_4_Prefix.thy
```

Then run the project’s full intended Isabelle build.

---

## 8. Direct advice to the worker

The old graph advice is now obsolete. The pushed state at `96e32ef` confirms that the graph-cache file no longer has a raw `sorry`, and the remaining work is exactly the two fold constructors plus D44. ([GitHub][1])

Stay on Figure 3.3 Case 1. The latest commit was the right move: it proved the four top-triangle vertex image facts. The next proof should not invent new geometry; it should lift those facts to face-closure carriers, prove `geotop_isomorphism` for the source/target four-piece complexes, and invoke the existing PLH machinery. Then prove the extension-by-identity support and the two boundary image facts.

After Case 1 closes, derive the two-boundary corner case as the inverse fold if at all possible. The inverse-support and composition-support lemmas already exist, so the second fold should not become another full PL construction.

Leave D44 last. It is one visible `sorry`, but it is still the largest mathematical package. The good news is that D44 already has a named fine carrier `N` with `A1 ⊆ N` and `N ∩ A2 = {}`, plus local access neighborhoods near `Q` and `S`. The remaining D44 proof should focus on showing the `Q` and `S` access witnesses land in the same component of the complement.

The current path to zero target `sorry`s is now very clear:

```text
Figure 3.3 Case 1 carrier isomorphism + supported PL extension
→ Figure 3.3 Case 2 inverse/corner fold
→ Section 3 wrappers 3.4–3.7
→ D44 regular-neighborhood component transfer
→ final hole scan, index regeneration, and full build
```

[1]: https://raw.githubusercontent.com/JUrban/isa_geotop1/96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d/tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy?utm_source=chatgpt.com "raw.githubusercontent.com"
[2]: https://raw.githubusercontent.com/JUrban/isa_geotop1/96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d/tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy?utm_source=chatgpt.com "raw.githubusercontent.com"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d/tst/dev34_prefix/GeoTop_3_4_Prefix.thy?utm_source=chatgpt.com "raw.githubusercontent.com"
[4]: https://github.com/JUrban/isa_geotop1/commit/96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d?utm_source=chatgpt.com "Record Figure 3.3 triangle vertex images · JUrban/isa_geotop1@96e32ef · GitHub"
[5]: https://github.com/JUrban/isa_geotop1/commit/b191ca4?utm_source=chatgpt.com "Prove Figure 3.3 vertex map bijection · JUrban/isa_geotop1@b191ca4 · GitHub"
[6]: https://raw.githubusercontent.com/JUrban/isa_geotop1/96e32ef6f9a06d0d6729b68ee9c56a51b2902b1d/tst/DEV34_FAST_CACHE_APPROACH_REPORT_2026_06_10.md?utm_source=chatgpt.com "raw.githubusercontent.com"
