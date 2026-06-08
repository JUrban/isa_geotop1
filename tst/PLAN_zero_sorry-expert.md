# Report: GeoTop / Moise Sections 3–4 formalization on `codex-dev34-cache`

I examined the GitHub branch, the `tst` development layout, the project status reports, and the raw Isabelle theory fragments around the remaining proof holes. I did **not** run a local Isabelle build in this environment, so the conclusions below are based on the branch contents and the project’s own build/status artifacts rather than an independent kernel check.

## 1. Executive assessment

The project is **not stuck because of missing syntax or random automation failures**. It is stuck at the natural hard point of this formalization: Moise’s Sections 3 and 4 repeatedly use planar-topology pictures as arguments, while Isabelle needs those pictures decomposed into reusable lemmas about finite complexes, polygonal disks, arcs, local charts, and graph carriers.

The current branch is very close structurally. The repository branch exists as `codex-dev34-cache`, and the `tst` directory contains a layered development around `dev34_pre`, `dev34_prefix`, `dev34_core`, and active `dev34` theories. The public branch page shows the repository and branch state, while the `tst` directory confirms the development is intentionally split into prefix, facts, graph facts, link facts, open-star facts, and active work layers. ([GitHub][1])

The latest committed status file says the target stack still has **17 executable `sorry`s**: **12 in `tst/dev34_prefix`**, **0 in `tst/dev34_core`**, and **5 in active `tst/dev34`**. It also reports no remaining `sledgehammer` markers in the checked target set. The report’s completion criterion is clear: remove all `sorry`/`sledgehammer` from `tst/dev34_prefix`, `tst/dev34_core`, and `tst/dev34`, rebuild successfully, regenerate indexes, and commit. ([GitHub][2])

The good news is that this is now a **finite, well-localized completion problem**, not an exploratory port. The bad news is that the remaining holes are exactly the places where Moise silently relies on nontrivial geometric or graph-theoretic facts. The worker should stop trying to “finish the theorem at the hole” with local proof search. The fastest route is to introduce a small number of sharply stated intermediate lemmas and then make the top-level theorems almost mechanical.

My strongest recommendation is this:

> Finish Sections 3 and 4 by proving five reusable lemma families:
> **finite triangulated disk ear/free-triangle lemmas**,
> **free-triangle fold/elimination lemmas with support control**,
> **arc-crossing/separation lemmas inside a polygonal disk**,
> **finite linear graph cycle/path classification lemmas**, and
> **explicit local Euclidean chart lemmas for one-, two-, and three-triangle edge stars**.

Trying to close the remaining `sorry`s one by one without these abstractions will likely keep producing brittle proofs.

---

## 2. Current architecture and what it means

The development is deliberately layered. The status file describes the active target stack as follows: `dev34_pre` is a dirty cached prefix, `dev34_prefix` holds much of the current Sections 3–4 formalization, `dev34_core` is reported clean, and active `dev34` contains the remaining top-level/local-chart work. The status report also gives the recent successful build commands and mentions a cache commit named “Cache completed GeoTop 3-4 core prefix.” ([GitHub][2])

This architecture is sensible. It means the worker should treat the layers differently:

**`dev34_core` should be treated as frozen.**
The report says it has zero target `sorry`s. Do not disturb it unless a genuinely missing general lemma belongs there.

**`dev34_prefix` is the main Section 3 and early Section 4 bottleneck.**
Most remaining work is here. In particular, Section 3’s free-triangle/folding story and Section 4’s early arc/bricks theorems still have major proof obligations.

**Active `dev34` contains final local-chart and graph-realization obligations.**
These should be attacked after the prefix is stable, except for very localized lemmas that can be proved independently.

The older report maps the intended coverage to Moise’s Theorems 3.1–3.7 and 4.1–4.10. It explicitly lists Theorem 3.3 as the free-triangle/decomposition result, Theorems 3.4 and 3.7 as folding/support-related results, Theorems 4.1–4.4 as early separation/arc/brick material, and Theorems 4.8–4.10 as local chart/manifold boundary material. ([GitHub][3])

That mapping matters because it determines dependency order. The worker should not finish Theorem 4.10 before stabilizing the Section 3 machinery, because Section 4’s local and global manifold arguments depend on reliable disk, boundary, and finite-complex infrastructure.

---

## 3. Recent progress and recent struggles

The status reports show real progress over the last few days. They mention completed radial/local infrastructure, exposed two-triangle carrier inclusion facts, generated theorem indexes, and recent improvements around local edge models, Figure 4.10 splitting, and chart statements. ([GitHub][2])

But the recent struggle is also visible: many of the remaining holes are not “the last line of a proof.” They are large mathematical assertions hiding behind one `sorry`.

For example, the latest status names the following clusters as still significant: Theorem 3.3 disk-decomposition/free-triangle work, Theorem 3.4/3.7 fold support, Theorem 4.2/4.4 arcs and bricks, Figure 4.10 cyclic graph realization, and local semicircle/circle chart arguments for Theorems 4.8–4.10. ([GitHub][2])

That diagnosis is correct. These are not random theorem-prover annoyances. They correspond to a few mathematical themes:

1. **Moise’s “obvious from the diagram” steps need formal finite-complex lemmas.**
2. **Boundary and frontier arguments need explicit component/separation statements.**
3. **Local manifold charts need normalized Euclidean models, not ad hoc set rewriting.**
4. **Finite graph carriers need combinatorial classification before geometric realization.**
5. **The proof currently has some wrapper lemmas whose names are stronger than their underlying formal infrastructure.**

There is also a small process issue: the latest status report may be slightly stale relative to the raw theory snapshot. For instance, the status file identifies a two-triangle all-boundary step as a next target, but the raw prefix snapshot shows `geotop_two_triangle_all_boundary_edges_force_other_subset_prefix` now filled by reducing to `geotop_polygon_disk_all_triangle_boundary_closure_subset_prefix`. That does not mean the mathematical problem vanished; it likely means the hard obligation moved into the more general polygon-disk closure lemma. The worker should rerun the exact `rg` command from the status report before starting, then update the status file so nobody fights an already-moved target. ([GitHub][2])

---

## 4. Section 3: main problems and completion path

### 4.1 Theorem 3.3 is the first strategic priority

Theorem 3.3 appears to be the key Section 3 decomposition/free-triangle theorem. The raw prefix file still shows a proof hole inside the main decomposition/induction argument for Theorem 3.3, around a step that needs to identify the selected intersection behavior after cutting or choosing a subdisk. ([GitHub][4])

Another explicit Section 3 hole is `geotop_polygon_disk_two_boundary_2simplexes_prefix`, whose statement says, in effect, that if a polygonal disk triangulation has more than two 2-simplexes, then at least two 2-simplexes have boundary edges. That lemma is still marked with `sorry` in the raw prefix snapshot. ([GitHub][4])

This is exactly the kind of lemma that should not be proved only for the immediate theorem. It should be promoted into a small “finite triangulated disk has ears” package.

The mathematically clean route is:

**Lemma A: boundary simplex existence.**
Every finite triangulation of a polygonal disk with at least one 2-simplex has at least one 2-simplex incident to the boundary.

**Lemma B: two boundary triangles / two ears.**
If the triangulated disk has more than one or more than two 2-simplexes, then it has at least two boundary 2-simplexes, or at least one free triangle depending on the exact book statement.

**Lemma C: non-free boundary triangle gives a disk split.**
If a boundary triangle is not free in the required sense, then its boundary-contact pattern determines a diagonal/cut that splits the polygonal disk into two smaller polygonal disks.

**Lemma D: the induction transfer lemma.**
A free triangle found in a subdisk remains free, or can be transferred back to the original disk under explicitly stated disjointness and carrier-equality conditions.

The current code seems to be trying to prove these ideas in the middle of Theorem 3.3. That is a bad place for them. The worker should extract them into named lemmas with exact hypotheses matching the existing complex predicates.

### 4.2 Avoid over-relying on the two-triangle special case

The raw file shows several two-triangle lemmas around the all-boundary case, including `geotop_two_triangle_all_boundary_edges_force_other_subset_prefix`, `geotop_two_triangle_not_all_boundary_edges_prefix`, and a boundary-edge face-cardinality lemma. The all-boundary wrapper now appears to call a more general polygon-disk closure lemma. ([GitHub][4])

That is encouraging, but it should be verified carefully. The worker should check whether the general lemma is actually proved without hidden `sorry`s in its proof chain. If it is, mark the status file accordingly. If it is not, the underlying problem remains:

> If all three edges of a triangle lie on the polygonal boundary of the disk, then the disk cannot contain another 2-simplex outside that triangle.

This should be proved as a polygonal-disk boundary/frontier lemma, not as a two-triangle combinatorial hack. A robust statement would say that a closed triangular carrier whose entire frontier is the frontier of the disk exhausts the disk carrier. The proof should use the existing polygonal disk/frontier/closure infrastructure, not later manifold results from Section 4 unless the development order permits it.

### 4.3 Theorem 3.4 and 3.7: fold support must be made explicit

The raw prefix snapshot shows Theorem 3.4 still has an `ind_step` proof hole. The nearby base/nonempty transition appears handled, so the missing content is the actual induction step: remove or fold a free triangle and preserve the theorem’s conclusion. ([GitHub][4])

This is probably the most important Section 3 engineering decision. The worker should **not** try to finish Theorem 3.4 directly. Instead, introduce a standalone fold lemma.

A useful target lemma family would look conceptually like this:

```isabelle
free_triangle_fold_elimination:
  assumes "K triangulates a polygonal disk D"
      and "sigma is a free 2-simplex of K"
      and "boundary-contact pattern of sigma is allowed"
  shows "there exists a homeomorphism h and a smaller complex K'
         such that h maps the relevant disk/carrier to |K'|,
         K' has one fewer 2-simplex,
         the boundary polygon is transformed correctly,
         and the desired local boundary data are preserved"
```

Then Section 3.7 should use a support-controlled version:

```isabelle
free_triangle_fold_elimination_with_support:
  assumes ... and "neighborhood U contains the fold region"
  shows "exists h. homeomorphism h ∧ support h ⊆ U ∧ ..."
```

After those are proved, Theorems 3.4 and 3.7 should become induction wrappers.

The fold lemma should be split by boundary-contact case:

1. **One boundary edge.**
   Fold across the interior edge or remove the free triangle by a local PL homeomorphism.

2. **Two adjacent boundary edges.**
   This is usually easier geometrically but trickier for frontier bookkeeping.

3. **Degenerate/no-boundary-contact cases.**
   These should either be impossible under the free-triangle hypothesis or delegated to existing earlier lemmas.

The project already has evidence of recent work around radial/local infrastructure and fold-related support, so the missing move is not to invent new geometry from scratch; it is to consolidate that infrastructure into one induction-ready lemma. ([GitHub][3])

### 4.4 Recommended Section 3 order

The worker should finish Section 3 in this exact order:

1. **Regenerate the hole inventory.**
   Use the report’s `rg` command over `tst/dev34_prefix`, `tst/dev34_core`, and `tst/dev34`, then compare against the status file. The latest status says there are 17 target `sorry`s and no `sledgehammer`s, but at least one named next-step wrapper appears to have shifted in the raw theory snapshot. ([GitHub][2])

2. **Finish the polygon-disk boundary-count lemmas.**
   In particular, close `geotop_polygon_disk_two_boundary_2simplexes_prefix` or replace it with a stronger ear lemma that implies it. ([GitHub][4])

3. **Finish Theorem 3.3’s decomposition step.**
   Do this by proving subdisk-carrier equality, boundary-intersection equality, and smaller-cardinality facts separately. Do not leave them inside the induction proof. ([GitHub][4])

4. **Prove a free-triangle fold-elimination lemma.**
   This should become the engine for Theorem 3.4.

5. **Prove the support-controlled version.**
   This should become the engine for Theorem 3.7.

6. **Only then clean theorem wrappers.**
   The final proof of Theorems 3.3, 3.4, and 3.7 should be short, structured, and mostly calls to the new lemmas.

---

## 5. Section 4.2: arc separation and disjointness

Theorem 4.2 still has a hole named around `hD42_disjoint`. The raw snapshot shows the theorem statement and an unfinished disjointness/separation step. ([GitHub][4])

This is likely Moise’s familiar argument: an arc in a disk separates certain boundary points, and if the wrong components meet, one can draw a crossing arc or broken line contradicting planar order.

The worker should resist proving this by set algebra alone. The right helper lemma is an **arc-crossing contradiction** inside a polygonal disk.

A good formal shape is:

```isabelle
polygon_disk_crossing_arc_contradiction:
  assumes "A is an arc in the polygonal disk I from P to R"
      and "B is an arc or broken line in I - A from Q to S"
      and "P Q R S occur in cyclic order on the boundary"
  shows False
```

or equivalently:

```isabelle
arc_separates_opposite_boundary_points:
  assumes "A is an arc in I from P to R"
      and "P Q R S are cyclic on frontier I"
  shows "Q and S lie in different components of I - A"
```

The proof should probably reuse whichever earlier theorem corresponds to Moise’s crossing/order result, rather than rebuilding Jordan separation from scratch. The older report says Section 4.2 and 4.4 are already framed among arc and component arguments, so this missing proof is probably intended to sit on top of earlier Sections 1–2 facts. ([GitHub][3])

A practical completion strategy:

1. Define the relevant components explicitly:

   ```isabelle
   CQ = connected_component_set (I - A) Q'
   CS = connected_component_set (I - A) S'
   ```

   or whatever component notion the library uses.

2. Prove `CQ ≠ CS` by contradiction.

3. From `CQ = CS`, extract a polygonal arc or broken line in `I - A` from a point near `Q` to a point near `S`.

4. Attach short boundary-normal segments if necessary to make the endpoints exactly `Q` and `S`, while preserving disjointness from `A`.

5. Apply the crossing-order theorem.

This is the kind of proof where most difficulty comes from endpoint hygiene. The worker should introduce endpoint-perturbation lemmas rather than repeatedly unfolding component definitions.

---

## 6. Section 4.4: bricks are the danger zone

The raw prefix file shows Theorem 4.4 has several unfinished book-step holes: brick decomposition, manifoldness of a derived neighborhood, frontier as a broken line, and component facts for named points or arcs. ([GitHub][4])

This is probably the largest remaining conceptual risk. A literal formalization of Moise’s brick argument may take much longer than expected, because “bricks” package many facts at once:

* existence of a finite decomposition adapted to arcs,
* local manifold behavior of a regular neighborhood,
* frontier being a broken line,
* component separation properties,
* preservation of cyclic boundary order.

The worker should decide now whether to formalize bricks literally or replace them with a more standard regular-neighborhood lemma.

My recommendation is **not** to formalize arbitrary bricks from scratch. Instead, prove a regular-neighborhood theorem for compact polygonal arcs inside a triangulated disk.

A useful replacement theorem would be:

```isabelle
regular_neighborhood_of_polygonal_arc_in_disk:
  assumes "A is a polygonal arc in the interior of a polygonal disk D"
      and "A avoids the specified boundary arcs/points"
  shows "there exists a polygonal disk N such that
         A ⊆ interior N,
         N ⊆ D,
         frontier N is a broken line / polygonal 1-sphere,
         D - N has the required component behavior"
```

Then the book’s brick decomposition can be represented as an implementation detail, not a theorem-level dependency. If existing names require `geotop_brick_decomposition`, keep the definition as a facade but prove it using a triangulated regular neighborhood.

The theorem currently defines or references `geotop_brick_decomposition`, and the raw file shows that this is where the proof is concentrated. ([GitHub][4])

A possible fallback is to derive Theorem 4.4 from Theorem 4.2 plus compactness and polygonal approximation. That may be shorter if Theorem 4.2 is strong enough. But if Theorem 4.4 needs the exact brick frontier object later, then prove the regular-neighborhood lemma and instantiate the brick statement from it.

The key advice: **do not keep five independent `sorry`s inside Theorem 4.4.** That will lead to repeated work. Collapse them into one or two reusable neighborhood lemmas, then let Theorem 4.4 call those.

---

## 7. Figure 4.10 and graph realization

Active `dev34` still has a core hole around `geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34`, and a wrapper immediately calls it. This is the Figure 4.10 cyclic graph realization problem. ([GitHub][5])

This should be treated as a **finite graph classification problem first**, and as a geometric realization problem second.

The tempting but bad approach is to reason directly about a carrier embedded in the plane and try to construct the boundary subdivision geometrically in one proof. The better approach is:

1. Define the abstract graph of vertices and edges of the finite 1-complex.

2. Prove a combinatorial classification:

   * finite,
   * connected,
   * nonisolated,
   * linear graph,
   * every vertex has degree 2
     implies the graph is a simple cycle.

3. Produce a cyclic list of vertices and edges.

4. Separately prove that every finite simple cycle graph is PL-isomorphic to a subdivision of a triangle boundary, square boundary, or polygonal circle.

5. Use the existing geometric carrier facts only to show the hypotheses of the combinatorial lemma.

This also applies to the broken-line fan/boundary-vertex material. The raw active file shows recent proof structure around a finite linear graph broken-line/fan model, suggesting the development is already moving in this direction. ([GitHub][5])

The worker should make this split explicit:

```isabelle
finite_connected_degree2_graph_has_cycle_listing
cycle_listing_realizes_boundary_subdivision
linear_graph_polygon_carrier_has_degree2_vertices
```

Then Figure 4.10 becomes mostly composition.

The main pitfall is degree bookkeeping at endpoints. If the carrier is a circle-like graph, every vertex has degree 2. If it is a broken-line arc, exactly two vertices have degree 1 and the rest have degree 2. Those two cases should be proved separately, not interleaved.

---

## 8. Local chart obligations for Theorems 4.8–4.10

The active `dev34` file still contains local Euclidean holes. These are not global topology problems; they should be solved by explicit normal forms.

### 8.1 One-sided edge: semicircle separation

The raw active file shows a remaining `sorry` around a lemma named like `geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34`, and the nearby wrapper reduces the one-sided local chart argument to this explicit semicircle-radius separation lemma. ([GitHub][5])

That is good. The correct proof should be purely Euclidean.

Normalize the configuration by an affine homeomorphism:

* the edge becomes a diameter segment on the x-axis,
* the unique incident triangle lies in the upper half-plane,
* the point of interest is at the origin or another simple coordinate,
* the chosen radius is small enough that the local star intersects the circle/semicircle in the standard way.

Then prove separation using a continuous coordinate function, not topological guesswork. For example, the complement of a small semicircle in a half-disk has two relevant local sides. One can show two chosen points cannot be connected without crossing the semicircle by composing any hypothetical path with a radial/angle coordinate or by using a line/circle crossing lemma already present.

The important instruction to the worker is: **specialize the lemma to the exact normalized semicircle used by the proof.** A more general theorem about arbitrary semicircles in arbitrary domains will be slower.

### 8.2 Three incident triangles: small-circle complement connectedness

Another active hole is `geotop_three_incident_small_circle_complement_connected_explicit_dev34`. The status report also identifies this as one of the best next active targets. The raw file shows the explicit lemma still has `sorry`, and nearby code constructs a local finite carrier, chooses an epsilon, and invokes that explicit complement-connected lemma. ([GitHub][2])

This is the dual of the one-sided edge case. In the one-sided case, the local semicircle separates the local domain. In the three-incident case, the extra sector gives a path around the obstruction, so the punctured/complemented local domain remains connected.

Again, use a normal form. Put the edge on the x-axis and let the incident 2-simplexes occupy three sectors around it. Choose a small circle centered at the point. Then show any two points in the local carrier minus the circle can be connected by polygonal paths using the third sector as the bypass.

A strong but manageable lemma is:

```isabelle
three_sector_disk_minus_small_circle_path_connected:
  assumes "U contains three sectors around p"
      and "0 < eps" and "closed_ball p eps ⊆ local model"
  shows "path_connected (U - sphere p eps)"
```

Then derive the project’s `top1_connected_on` conclusion from path-connectedness.

Do not try to prove connectedness directly from arbitrary open-set definitions. Construct paths.

### 8.3 Local Jordan side containment

The active file also has a remaining `sorry` in `geotop_2cell_chart_1sphere_complement_not_connected_dev34`, around showing that the inner and outer sides of a charted 1-sphere have the required containment/intersection properties. ([GitHub][5])

This is another case where the generic statement may be too hard. The proof should be specialized to the actual small circle or 1-sphere chosen in the local chart.

The right helper lemma is:

```isabelle
small_circle_in_chart_has_inner_side_inside_chart_domain:
  assumes "closed_ball p r ⊆ chart_domain"
      and "J = sphere p r"
  shows "bounded_component (UNIV - J) ⊆ chart_domain"
```

and:

```isabelle
small_circle_in_chart_has_outer_side_meeting_chart_domain:
  assumes "chart_domain is a neighborhood of p"
      and "J = sphere p r"
  shows "unbounded_component (UNIV - J) ∩ chart_domain ≠ {}"
```

The first is just “the disk bounded by the small circle lies inside the selected local ball.” The second is usually witnessed by a point in the chart domain outside the small circle, chosen along a ray or inside the local star.

This will be much easier than proving a fully abstract Jordan-side statement for arbitrary embedded 1-spheres.

---

## 9. Main recommendations to the worker

### Recommendation 1: update the hole dashboard first

The status file says the current target stack has 17 executable `sorry`s and gives the exact `rg` command used to count them. It also lists the completion criteria. Start by rerunning that command and comparing against the raw files, because at least one named “next step” appears to have moved since the report text. ([GitHub][2])

The dashboard should classify each hole as one of:

* Section 3 finite disk/free-triangle,
* Section 3 fold/support,
* Section 4.2 arc separation,
* Section 4.4 regular neighborhood/bricks,
* Figure 4.10 graph realization,
* local Euclidean chart/Jordan side.

This prevents accidental proof-search drift.

### Recommendation 2: finish Section 3 before polishing active Section 4

The Section 3 holes are more foundational. The worker should close the polygonal disk/free-triangle/fold machinery before spending much time on Figure 4.10 or Theorem 4.10 wrappers.

Theorem 3.3 gives the free simplex needed for the fold induction. Theorem 3.4 is the fold induction. Theorem 3.7 is the support-controlled version. If these remain unstable, later Section 4 arguments will continue to accumulate local workarounds.

### Recommendation 3: replace monolithic book-step holes with lemma packages

The project should avoid proofs of the form:

```isabelle
have "large geometric fact" sorry
```

inside a theorem. Each such step should become a named lemma with a stable statement and a proof that can be reused.

The highest-value lemma packages are:

1. `Triangulated_Disk_Ears`
2. `Free_Triangle_Fold`
3. `Polygon_Arc_Crossing`
4. `Regular_Neighborhood_Arc`
5. `Finite_Linear_Graph_Classification`
6. `Local_Edge_Chart_Normal_Forms`

The names do not matter, but the separation does.

### Recommendation 4: use explicit Euclidean models for local chart facts

The local Section 4.8–4.10 holes should not be solved by generic topological connectedness arguments. Normalize the geometry by affine maps, choose radii with strict inequalities, and construct polygonal paths or separating coordinate functions.

This is especially important for the one-sided semicircle separation lemma and the three-incident small-circle connectedness lemma. The raw active file already reduces higher-level wrappers to these explicit lemmas, so finishing them should unlock multiple later facts. ([GitHub][5])

### Recommendation 5: treat Theorem 4.4 as a regular-neighborhood theorem, not a brick-by-brick grind

The five holes in Theorem 4.4 strongly suggest the proof currently mirrors the book too literally. The worker should introduce one robust regular-neighborhood lemma for polygonal arcs in a disk, then derive the brick facts from it.

This may feel like more work initially, but it is safer. A literal brick decomposition will require separate proofs of existence, boundary shape, manifoldness, and component behavior anyway. A regular-neighborhood theorem packages those facts in the form later Section 4 arguments actually need.

### Recommendation 6: prove graph-realization abstractly first

For Figure 4.10, first prove that the finite graph is a cycle or path abstractly, then realize that abstract graph as a boundary subdivision. Do not mix graph classification, cyclic ordering, and planar carrier geometry in a single proof.

The active hole around the connected nonisolated finite linear graph boundary-cycle model is exactly where this split should happen. ([GitHub][5])

---

## 10. Suggested concrete work plan

### Phase 0: synchronization

Run the target `rg` check and rebuild the status file. Confirm whether the count is still 17 and whether the two-triangle all-boundary item is genuinely closed or merely delegated to another unproved lemma. The latest status explicitly says the completion target is no `sorry`/`sledgehammer` in `tst/dev34_prefix`, `tst/dev34_core`, and `tst/dev34`. ([GitHub][2])

### Phase 1: Section 3 finite disk lemmas

Close:

* `geotop_polygon_disk_two_boundary_2simplexes_prefix`,
* the underlying all-boundary polygon-disk closure lemma if it still depends on an unfinished proof,
* the Theorem 3.3 decomposition hole.

Preferred mathematical proof route:

1. Work with the finite set of 2-simplexes.
2. Define boundary incident edges/faces explicitly.
3. Prove existence of at least two boundary triangles using an ear or dual-graph argument.
4. Prove that the non-free boundary case splits the disk into smaller polygonal disks.
5. Apply induction and transfer the free-triangle conclusion back.

### Phase 2: Section 3 fold induction

Close Theorem 3.4’s `ind_step` by proving a standalone free-triangle fold lemma. Then close Theorem 3.7 by proving the support-controlled version. The raw file shows Theorem 3.4’s base/nonempty structure is already in place, so the induction step is the core missing piece. ([GitHub][4])

### Phase 3: Section 4.2 and 4.4

First finish Theorem 4.2 with a crossing/separation lemma. Then attack Theorem 4.4 through a regular-neighborhood theorem rather than five independent brick subproofs. The raw file shows the unfinished Theorem 4.4 obligations are exactly the brick, manifold, frontier, and component claims that such a lemma should package. ([GitHub][4])

### Phase 4: active graph/local-chart holes

Close the Figure 4.10 graph-cycle model using finite graph classification. Then close the local chart holes:

* one-sided edge semicircle separation,
* three-incident edge small-circle complement connectedness,
* local Jordan side containment for the 2-cell chart.

The active raw file shows all three as still localized and therefore suitable for direct Euclidean normal-form proofs. ([GitHub][5])

### Phase 5: final verification

After all target holes are removed:

1. Run the target build command from the status report.
2. Run the `rg` check over `tst/dev34_prefix`, `tst/dev34_core`, and `tst/dev34`.
3. Regenerate `STMT_INDEX.txt` and theorem indexes.
4. Update the status/report files.
5. Commit with a message that explicitly says Sections 3 and 4 are `sorry`-free in the target stack.

---

## 11. Final diagnosis

The branch is in a good state for a determined finishing push. The infrastructure is no longer the main obstacle. The problem is that a few book-level geometric assertions are still too large for the current proof granularity.

The worker should not spend more time asking Sledgehammer to solve global topology pictures. The winning strategy is to formalize the missing pictures as reusable lemmas:

* triangulated disks have boundary ears/free triangles,
* free triangles can be folded away with controlled support,
* opposite boundary arcs cannot be connected without crossing,
* polygonal arcs have regular neighborhoods with polygonal frontier,
* finite linear graphs are cycles or paths,
* local edge stars reduce to explicit Euclidean sector models.

Once those are in place, the remaining theorem statements should close quickly and cleanly.

[1]: https://github.com/JUrban/isa_geotop1/tree/codex-dev34-cache "GitHub - JUrban/isa_geotop1 at codex-dev34-cache · GitHub"
[2]: https://github.com/JUrban/isa_geotop1/raw/refs/heads/codex-dev34-cache/tst/GEOTOP_SECTIONS_3_4_STATUS_2026_06_05.md "raw.githubusercontent.com"
[3]: https://github.com/JUrban/isa_geotop1/raw/refs/heads/codex-dev34-cache/tst/GEOTOP_SECTIONS_3_4_REPORT.md "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/refs/heads/codex-dev34-cache/tst/dev34/GeoTop_3_4.thy "raw.githubusercontent.com"
