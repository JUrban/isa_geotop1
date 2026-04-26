# REPORT — Theorem_GT_1 in Isabelle/HOL: a sorry-free proof

> **Theorem 1 (Moise, *Geometric Topology in Dimensions 2 and 3*, p. 7).**
> Every two subdivisions of the same complex have a common subdivision.

This document records the multi-session formalization effort that turned this
one-line theorem into the sorry-free Isabelle/HOL proof now living in
`b0/GeoTopBase0.thy`. The headline statement is

```isabelle
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows   "∃L. geotop_is_subdivision L L1 ∧ geotop_is_subdivision L L2"
```

and after Phase 8 it is proven without a single `sorry` in the basis
(`b0/GeoTopBase0.thy` + `b/GeoTopBase.thy`).

The story is essentially a worked example of a classical PL-topology argument
done from scratch on top of HOL-Analysis. It also includes a real research
moment: the proof attempt we *started* with turned out to be founded on a
**false** auxiliary lemma.

---

## 1. What Moise actually says

Moise's text (`geotop.tex` here) is, in this part of the book, a survey
chapter. Theorem 1 is *stated* on p. 7 without proof. The general
common-subdivision claim never gets a direct proof in the chapter; instead,
Moise defers the work to the problem set, where it is broken up by dimension:

| Problem | Statement |
|--------|-----------|
| 0.18 | Let `K` be a finite complex in `R²`, and `{L_i}` a finite collection of lines. Then `K` has a subdivision `K_1` in which each `L_i ∩ |K|` forms a subcomplex. |
| **0.19** | **Every two subdivisions `K_1, K_2` of a 2-simplex `σ² ⊂ R²` have a common subdivision.** |
| **0.20** | **Let `K` be a 2-dimensional complex. Then every two subdivisions of `K` have a common subdivision.** |
| 0.26 | (R³ analogue of 0.18 with planes.) |
| **0.27** | **Every two subdivisions of a 3-simplex have a common subdivision.** |
| **0.28** | **Let `K` be a 3-dimensional complex. Then every two subdivisions of `K` have a common subdivision.** |

The relevant tools Moise gives the reader for these problems are the
inductive definition of the (first) barycentric subdivision `bK` (p. 35-ish
in our text, line 1197 in `geotop.tex`) plus the three facts numbered there:

> 5. For each `K`, `bK` is a complex.
> 6. `bK` is a subdivision of `K`.
> 7. `‖b σⁿ‖ ≤ ½ ‖σⁿ‖`, for each `σⁿ`.

So the *spirit* of the textbook approach to common subdivision in arbitrary
dimension is "iterate `b` until things fit"; the *letter* of the textbook
proof is left to the reader. Our own writeup of this folkloric argument lives
in `early.tex §4` and was the original target of the formalization.

## 2. The original (failed) approach: iterated barycentric subdivision

The plan we tried to formalize was the standard one. Given a complex `K` and
a subdivision `K'` of `K`, we wanted to show that *some* iterated barycentric
subdivision `Sd^N K` refines `K'`, i.e. every simplex of `Sd^N K` is
contained in some simplex of `K'`. Once we had that, a common subdivision
of two subdivisions `L1, L2` of `K` falls out: take `N = max(m, n)` where
`Sd^m K` refines `L1` and `Sd^n K` refines `L2`, and use transitivity of
subdivision.

This is the path the formalization originally followed. The auxiliary step
became, in Isabelle, the lemma

```isabelle
geotop_iterated_Sd_refines_subdivision:
  finite K ⟹ geotop_is_subdivision K' K
  ⟹ ∃m. geotop_is_subdivision (geotop_iterated_Sd m K) K'
```

The proof we tried to give was the standard Lebesgue-number argument on the
finite open-star cover of `|K|` by vertex stars of `K'`, combined with
`geotop_iterated_Sd_mesh` (mesh shrinks by factor `n / (n+1)` per iteration).

It failed. The structural sub-lemmas were fine, but the analytic step `Step 4`
— "for every simplex `τ` of a sufficiently fine `Sd^N K`, the open stars of
`τ`'s vertices in `K'` have non-empty intersection" — refused to go through. We
sat on a `sorry` at that step and gradually realized the lemma surrounding the
sorry was just *false*.

### 2.1 The 1-dimensional counterexample

The cleanest disproof is one-dimensional. Take

* `K = {[0,1], {0}, {1}}` — a single 1-simplex with its two vertex faces.
* `K' = {[0, 1/3], [1/3, 1], {0}, {1/3}, {1}}` — the subdivision of `[0,1]` at
  the point `1/3`.

Iterating barycentric subdivision on `K` only ever produces vertices at
*dyadic* rationals: `m / 2^k` for various `m, k`. The point `1/3` is not
dyadic, so for every `N` there is exactly one sub-interval of `Sd^N K` whose
interior contains `1/3`. That sub-interval is contained in **neither**
`[0, 1/3]` nor `[1/3, 1]`. Hence `Sd^N K` never refines `K'` literally,
contradicting the lemma we were trying to prove.

### 2.2 Why the folkloric argument fails

Our writeup in `early.tex §4.5` had a subtle bug. The argument went:

> Choose `m` so each simplex `τ` of `Sd^m(K)` has diameter `< δ`. Then `τ` is
> contained in some open star `st_{K'}(v)`. Pick `x ∈ int(τ)`. Since
> `τ ⊂ st_{K'}(v)`, the point `x` lies in `int(σ)` for some `σ ∈ K'` having
> `v` as a vertex. Both `τ` and `σ` lie in some simplex of `K`. Inside that
> ambient simplex, `x ∈ int(τ) ∩ int(σ)`; since interiors of distinct
> simplices in a simplicial complex are disjoint, `τ ⊂ σ`.

The mistake is in the last sentence: "interiors of distinct simplices in a
simplicial complex are disjoint" is true *within one* complex, but `τ` and
`σ` belong to **different** complexes (`τ ∈ Sd^m K`, `σ ∈ K'`). They both
subdivide `K`, but the disjointness fact does not transfer across two
subdivisions of the same complex.

In the dyadic counterexample above (with `m = 1`, `Sd K = K|_{1/2}`), the
simplex `τ = [0, 1/2]` has interior `(0, 1/2)`, which intersects both the
interior `(0, 1/3)` of `[0,1/3] ∈ K'` and the interior `(1/3, 1)` of
`[1/3, 1] ∈ K'`, so `τ` is contained in neither. The Lebesgue argument
correctly places `τ` *in some open star* of `K'`, but cannot place it
inside any single closed simplex of `K'`.

So iterated barycentric subdivision does give a refinement of the
*non-literal* / "Munkres-type-with-closure" sort, but cannot give a
literal-containment refinement, which is what
`geotop_is_subdivision` demands. We needed a different machine.

We asked a mathematician (`ANSWER_REPORT.md`) and they pointed us at Hudson's
*Piecewise Linear Topology* (Chapter I, §2-3) and the **overlay cell
complex** construction. That became PLAN3.

---

## 3. The replacement strategy: overlay cell complex + order-complex
  triangulation

The classical PL fix factors through *cells* (convex polytopes) rather than
simplices. The high-level recipe:

1. Start with two simplicial complexes `L1, L2` with `|L1| = |L2|`.
2. Form pairwise intersections `σ ∩ τ` for `σ ∈ L1, τ ∈ L2`. These are
   non-empty convex polytopes — *cells*. Close under faces. Call the result
   `C = overlay_complex L1 L2`. It is a finite *cell* complex (Hudson's
   notion).
3. Triangulate `C` simplicially with no new vertices, getting a finite
   simplicial complex `M`. (Hudson Lemma 1.4 / Munkres §17 — barycentric
   subdivision of the cell poset.) `M` literally refines `C`.
4. Because every cell of `C` lies inside a simplex of `L1` *and* inside a
   simplex of `L2`, `M` literally refines both `L1` and `L2`.

The point that makes step 4 *literal* (and dodges the dyadic obstruction
above) is that `C` introduces new vertices wherever the boundaries of `L1`
and `L2` cross. With `K = [0,1]` and `K' = K |_{1/3}` the overlay just
contains `1/3` as a 0-cell, and the order-complex triangulation has `1/3` as
an honest vertex. No analytic limit argument is required.

---

## 4. The 8-phase formalization (PLAN3)

We split the work into eight phases, each with a `PLAN3_PHASE_n.md` plan
file. The first commit landed `2026-04-26`-ish (commit `9533507c`); Phase 8
landed at `d5336274`. **907 commits total** in the repository, of which the
plan-3 family contributes the bulk of the geotop-formalization activity.

Final basis size: `b0/GeoTopBase0.thy` is **14 886 lines**, with **262**
top-level `lemma`/`theorem`/`definition` declarations.

| Phase | Purpose | Key artefact |
|-------|---------|--------------|
| **1** | Convex linear cells (Hudson §2) | `geotop_cell` |
| **2** | Cell faces | `geotop_cell_face` (built on HOL-Analysis `face_of`) |
| **3** | Cell complexes | `geotop_cell_complex` |
| **4** | Overlay cell complex | `geotop_overlay_complex_is_cell_complex` |
| **5** | Order-complex triangulation is simplicial | `geotop_cell_complex_has_simplicial_subdivision` |
| **6** | Bridge: cell-subdivision ⟹ simplicial-subdivision of `L1, L2` | `geotop_overlay_triangulation_subdivides_left/right` |
| **7** | Common subdivision exists for `L1, L2` | `geotop_common_subdivision_finite` |
| **8** | Reprove `Theorem_GT_1`, delete the false theorem | sorry count = 0 |

Phases 1-4 are mostly bookkeeping on top of HOL-Analysis polytope theory
(`Polytope.thy`, `Convex.thy`). Phases 5-8 are where the substantial
mathematics lives.

### 4.1 Phase 5: order-complex triangulation (the hard core)

Phase 5 says: *every finite cell complex `C` has a simplicial subdivision*.
The witness is the **order complex**: the simplicial complex whose simplices
are the convex hulls of barycenters of strictly-increasing chains of cells in
`C`. This is the workhorse of barycentric subdivision when the underlying
object is a cell complex rather than just a simplicial complex. Munkres does
the simplicial special case in §15-17; Hudson does the general cell case as
Lemma 1.4.

The simplicial-complex axioms are:

* **K.0** every element is a (Moise) simplex,
* **K.1** closed under faces,
* **K.2** pairwise intersections are empty or a common face,
* **K.3** locally finite.

Phase 5 ended up with an internal sub-numbering for clarity:

| Sub-step | Lemma | Lines | Idea |
|----------|-------|-------|------|
| 5.1-5.5  | definitions (cell barycenter, cell-flag, chain-simplex, order complex) | ~60 | |
| 5.3 main | cell-flag barycenters are affinely independent | ~80 | rev_induct + `affine_hull_face_of_disjoint_rel_interior` + `affine_independent_insert` |
| 5.6a (K.0) | every chain-simplex is a Moise simplex | ~30 | uses 5.3 main + `geotop_ai_imp_general_position` |
| 5.6c (K.3) | order complex is finite | ~30 | bound length of cell-flags by `card C`, use `finite_lists_length_le` |
| 5.6b (K.1) | order complex closed under faces | ~80 | `simplex_vertices_unique` + filter sub-flag |
| **carrier**| every `x ∈ ‖C‖` has unique smallest cell `A ∋ x ∈ rel_interior A` | ~80 | `rel_frontier_of_polyhedron_alt` + `affine_hull_face_of_disjoint_rel_interior` |
| 5.7 ⊆ | `‖order_complex C‖ ⊆ ‖C‖` | ~25 | direct from 5.8 |
| 5.7 ⊇ | `‖C‖ ⊆ ‖order_complex C‖` | ~200 | strong induction on `aff_dim`, `segment_to_rel_frontier`, flag extension |
| 5.8 | each chain-simplex `⊆ last c ∈ C` | ~25 | trivial via convex hull |
| 5.9 | each `A ∈ C` is the union of contained chain-simplices | ~75 | uses carrier + 5.7 ⊇ + 5.8 |
| 5.6d.a | barycentric coords are unique on AI vertex sets | ~30 | `affine_dependent_explicit_finite` |
| 5.6d.b | for `x ∈ chain_simplex(c)`, *some* cell of `c` contains `x` in its rel_interior | ~140 | rev_induct + `convex_hull_insert` + `rel_interior_closure_convex_segment` + `in_segment(2)` |
| 5.6d.c | for `x ∈ σ_c1 ∩ σ_c2`, the carrier is in `set c1 ∩ set c2` | ~40 | combine 5.6d.b on each chain + carrier uniqueness |
| 5.6d.d | **Stripping**: if `last c ≠ carrier(x)` then `x ∈ chain_simplex(butlast c)` | ~150 | `convex_hull_insert` + `rel_interior_closure_convex_segment` |
| 5.6d.e | two `rel_frontier` points on the same ray from `b ∈ rel_interior` are equal | ~70 | open-segment ⊆ rel_interior gives a contradiction |
| 5.6d.f | **`u = u′`** (radial decomposition uniqueness) | ~80 | uses 5.6d.e + `scaleR_right_imp_eq` |
| 5.6d.g | `chain_simplex(butlast c) ⊆ rel_frontier(last c)` | ~80 | 5.8 + Step 5.3a + `face_of_subset_rel_frontier` |
| **5.6d main (K.2)** | `σ_c1 ∩ σ_c2 ⊆ chain_simplex(filter (∈ set c2) c1)` | **~330** | strong induction on `length c1 + length c2` |
| 5.6d.h | promote ⊆ to equality | ~40 | + sub-flag inclusion |
| 5.6d.i | repackage as `geotop_is_face` | ~70 | `face_of_convex_hull_affine_independent` |
| 5.6 packaging | order complex is a Moise simplicial complex | ~50 | bundle K.0/K.1/K.2/K.3 |
| 5.10 main | **`geotop_cell_complex_has_simplicial_subdivision`** | ~250 (incl. simplicial→cell complex bridge) | combine 5.6 + 5.7 + 5.8 + 5.9 |

K.2 was, by a wide margin, the hardest step. The naïve proof attempt — try to
show `V_{c1} ∪ V_{c2}` is affinely independent in general — *fails*, because
V_{c1} ∪ V_{c2}* really can be affinely dependent (e.g. four barycenter points
in the plane from incompatible flags through a common 2-cell). The right
proof goes through the carrier-cell uniqueness argument:

1. For any `x ∈ chain_simplex(c)`, the maximum cell in `c` whose barycenter
   has positive weight in the unique convex combination of `x` is exactly
   the carrier of `x` (Lemma 5.6d.b combined with carrier uniqueness from
   the cell-complex structure).
2. For `x ∈ σ_c1 ∩ σ_c2`, both carriers in the two flags coincide (Lemma
   5.6d.c).
3. The `(u, y)` in the decomposition `x = u·b(A) + (1-u)·y` with
   `y ∈ rel_frontier(A)` is uniquely determined by `x` and `A` (Lemma
   5.6d.f, the *radial decomposition uniqueness* lemma).
4. So in case 3b of K.2 (where the top of both flags equals the carrier of
   `x`), the two decompositions in `c1` and `c2` produce the *same* `y`,
   `y ∈ chain_simplex(butlast c1) ∩ chain_simplex(butlast c2)`, and we can
   recurse.

The radial-uniqueness Lemma 5.6d.f is the conceptual heart of K.2. It says:

> If `x` is in the relative interior of a convex set `S` and we write
> `x = u·b + (1-u)·y = u′·b + (1-u′)·y′` with `b ∈ rel_interior S`,
> `y, y′ ∈ rel_frontier S`, and `u, u′ ∈ [0, 1)`, then `u = u′` and
> `y = y′`.

The proof: any two `rel_frontier` points on the same open ray from `b` must
coincide, because otherwise the closer one would lie inside the open segment
to the farther one, and that open segment is contained in `rel_interior S`
(the lemma `rel_interior_closure_convex_segment` in HOL-Analysis), which
contradicts the closer point being in `rel_frontier`.

### 4.2 Phase 6: bridging back to simplicial subdivisions

The general bridge is a clean 80-line argument:

```isabelle
lemma geotop_simplicial_subdivision_from_cell_subdivision:
  fixes M C L :: "'a::euclidean_space set set"
  assumes "geotop_is_complex L"
  assumes "geotop_is_complex M"
  assumes "geotop_cell_is_subdivision M C"
  assumes "∀A ∈ C. ∃σ ∈ L. A ⊆ σ"
  assumes "∀σ ∈ L. σ = ⋃ {A ∈ C. A ⊆ σ}"
  shows   "geotop_is_subdivision M L"
```

The applied versions for the overlay scenario fall straight out: the
hypothesis `∀A ∈ C. ∃σ ∈ L1. A ⊆ σ` is `geotop_overlay_complex_refines_left`
from Phase 4, and `σ = ⋃ {A ∈ overlay_complex. A ⊆ σ}` is a small new lemma
that proves *any* `x ∈ σ ∈ L1` lies in the overlay cell `σ ∩ τ` for some
`τ ∈ L2` containing `x` (existence of `τ` follows from `|L1| = |L2|`).

### 4.3 Phase 7: the common-subdivision theorem

```isabelle
theorem geotop_common_subdivision_finite:
  fixes L1 L2 :: "'a::euclidean_space set set"
  assumes hL1: "geotop_is_complex L1"
  assumes hL2: "geotop_is_complex L2"
  assumes hL1fin: "finite L1"
  assumes hL2fin: "finite L2"
  assumes hpoly: "geotop_polyhedron L1 = geotop_polyhedron L2"
  shows   "∃M. geotop_is_subdivision M L1 ∧ geotop_is_subdivision M L2"
```

The proof is now mechanical assembly:

1. `C = overlay_complex L1 L2` is a cell complex (Phase 4).
2. `M = order_complex C` is a simplicial cell-subdivision of `C` (Phase 5,
   theorem `geotop_cell_complex_has_simplicial_subdivision`).
3. `M` is a simplicial subdivision of `L1` (Phase 6.2).
4. `M` is a simplicial subdivision of `L2` (Phase 6.3).

### 4.4 Phase 8: closing the loop

`Theorem_GT_1` is now four lines of bookkeeping plus an `apply` of
`geotop_common_subdivision_finite`. The `~430-line` previous proof body that
relied on the false iterated-`Sd` theorem was deleted, taking with it the
two surviving sorries it housed.

```isabelle
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows "∃L. geotop_is_subdivision L L1 ∧ geotop_is_subdivision L L2"
proof -
  have hL1_simp: "geotop_is_complex L1" using hL1 unfolding geotop_is_subdivision_def by blast
  have hL2_simp: "geotop_is_complex L2" using hL2 unfolding geotop_is_subdivision_def by blast
  have hL1_poly: "geotop_polyhedron L1 = geotop_polyhedron K"
    using hL1 unfolding geotop_is_subdivision_def by blast
  have hL2_poly: "geotop_polyhedron L2 = geotop_polyhedron K"
    using hL2 unfolding geotop_is_subdivision_def by blast
  have hpoly: "geotop_polyhedron L1 = geotop_polyhedron L2"
    using hL1_poly hL2_poly by simp
  have hL1fin: "finite L1" by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hL1])
  have hL2fin: "finite L2" by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hL2])
  show ?thesis
    using geotop_common_subdivision_finite[OF hL1_simp hL2_simp hL1fin hL2fin hpoly]
    by blast
qed
```

Sorry count in the basis: **0**. Build green.

---

## 5. Engineering notes

### 5.1 The `by100` discipline

Per `CLAUDE.md`, every `by` step uses the `by100` wrapper which times out the
inner method at 100 ms. The motivation is simple: in a file this long
(`14 886` lines, `262` declarations), an unguarded `auto`/`blast` can blow
through the build budget on a single bad simp call. The 100 ms cap forces
proofs to decompose.

It also forced an interesting workflow: after a single big proof addition we
would routinely see other, *pre-existing* `by100` calls start to flake under
the new memory pressure. The fix was timing-driven decomposition: dump
per-line timings with

```bash
isabelle eval_at -t -d . -l Top0 b0/GeoTopBase0.thy <last-line> > timing.txt
```

then attack any line over `~0.06s` first. Two big wins:

* Replace `using lemma_name[OF X] by (by100 simp)` with the direct
  `by (rule lemma_name[OF X])` whenever the lemma is an iff/equality.
  16 sites of `convex_hull_finite[OF X]` flipped this way alone.
* Replace `by (by100 simp)` with `by (by100 metis)` on chains of equality
  substitutions where simp's normalisation is doing a lot of unnecessary
  work.

After this pass the build dropped from "5–10 retries" to "1–2 retries" under
typical load.

### 5.2 Choice of barycenter

`geotop_cell_barycenter` is defined as `SOME b. b ∈ rel_interior C`, *not*
"centroid of vertices". This makes the affine independence proof clean (we
don't need to manage an explicit vertex set) and matches what
HOL-Analysis's lemmas expect. The cost is that we never compute concrete
coordinates — which in fairness was never the goal.

### 5.3 What we got from HOL-Analysis

The proof would not have been feasible in the time budget without
HOL-Analysis's `Polytope.thy` and friends. Critical imports:

* `affine_hull_face_of_disjoint_rel_interior` (proper face's affine hull
  misses rel_interior) — used pervasively.
* `face_of_convex_hull_affine_independent` (HOL face_of ↔ conv hull of
  vertex subset, when AI) — the bridge from K.2 in the simplicial sense to
  the cell-complex face notion.
* `rel_interior_closure_convex_segment` (open segment from rel_interior to
  closure stays in rel_interior) — the heart of the radial-uniqueness
  argument and the Stripping lemma.
* `segment_to_rel_frontier` (existence of a rel_frontier point along any
  ray) — the engine of Phase 5.7 ⊇.
* `convex_hull_insert` (explicit decomposition) — used in 5.6d.b, 5.6d.d,
  5.6d main.
* `extreme_point_of_convex_hull_affine_independent` (extreme points = vertex
  set when AI) — used for `simplex_vertices_unique`.

### 5.4 What turned out to be subtle

The single most painful phase, both intellectually and in lines, was K.2.
A small list of things that *looked* like they should work and didn't:

* "Take a common refinement of the two flags." Doesn't exist when the flags
  are incompatible (e.g. `c1 = [{a}, e_{ab}, T]`,
  `c2 = [{a}, e_{ac}, T]`).
* "Use AI of `V_{c1} ∪ V_{c2}`." False in general: the example above is four
  AI-barred points in the plane.
* "Show that `u_1 = u_2` is automatic from the bary-coord uniqueness on a
  single AI set." False — bary-coord uniqueness is *per* AI set, and the two
  flags use different ones.

The trick that finally worked is the combination of Stripping (5.6d.d) for
case 3a and *radial decomposition uniqueness* (5.6d.f) for case 3b. The
latter never actually mentions barycentric coordinates: it lives entirely
inside `rel_interior(carrier(x))`, treats the convex set as opaque, and uses
only the geometric fact that two `rel_frontier` points on the same open ray
must coincide.

---

## 6. Numerical postscript

* Final `b0/GeoTopBase0.thy`: 14 886 lines, 262 top-level declarations, build
  ~36–48 s.
* PLAN3 commits: roughly 30 substantive commits across phases 5-8, plus
  earlier groundwork in 1-4.
* Sorry count in the basis (`b0/GeoTopBase0.thy` + `b/GeoTopBase.thy`):
  **0**.
* Lines deleted in Phase 8: ~430 (the failed iterated-`Sd` proof body and
  its sorries).

The downstream proofs in `b/GeoTopBase.thy` and `GeoTop.thy` that use
`Theorem_GT_1` were unaffected: only the proof body changed, not the
statement.

---

## 7. Acknowledgements

The decisive course-correction came from a mathematician's review which
diagnosed the false iterated-`Sd` lemma and pointed at Hudson's overlay
construction (see `ANSWER_REPORT.md`). The PLAN3 file family
(`PLAN3_PHASE1.md` through `PLAN3_PHASE8.md`) records the original attack
plan, which survived almost verbatim through to the final proof.

The Isabelle proof was carried out across many sessions of pair work between
the user (J. Urban) and Claude (Anthropic), in successive context-window
iterations against `b0/GeoTopBase0.thy`. The `feedback_timing_measurement.md`
memo captures the engineering lesson about `by100` timing decomposition, for
future similar work.
