# PLAN3_PHASE5.md — Phase 5: Triangulating a cell complex

**Goal:** Prove that every finite convex cell complex has a simplicial subdivision (Hudson Lemma 1.4), with the additional property that each cell is covered face-compatibly by simplices of the triangulation.

**Status entering Phase 5:** Phases 1-4 complete. Sorry count: 1.

**Estimated:** ~200-300 lines of Isar / 3-5 days interactive work / 8-12 commits.

This is THE major work in the new strategy. Two implementation options.

---

## Hudson Lemma 1.4

From Hudson Chapter I §3 (lines 262-271):

> **Lemma 1.4.** If K is a cell complex, then K has a simplicial subdivision with no extra vertices.
>
> **Proof.** Order the vertices of K. If A ∈ K, write A = a · B, a the first vertex of A, B = all faces of A not containing a. Define subdivision of cells in order of increasing dimension by the rule:
>
> A' = a · B'
>
> where B' is the subdivision of B determined by the (simplicial) subdivision of cells of lower dimension. (If A = a, set A' = a). The construction is self-consistent because if C is a face of A containing a, then a is the first vertex of C.

So Hudson uses **induction by dimension**, choosing a distinguished "first vertex" (under a global ordering) for each cell, and coning from that vertex over the already-triangulated boundary.

---

## Two implementation options (per mathematician)

### Option A: Hudson Lemma 1.4 directly

Pros: follows the textbook exactly.
Cons: requires global vertex ordering, induction over cells by dimension, and several supporting lemmas about cone constructions.

### Option B: Order-complex / barycentric subdivision of cell poset

Construct a simplicial complex M whose:
- Vertices are barycenters of cells.
- Simplices are convex hulls of `{barycenter(A_0), barycenter(A_1), ..., barycenter(A_k)}` where `A_0 ⊊ A_1 ⊊ ... ⊊ A_k` is a chain of cells under proper-face order.

Pros: very canonical, uniform; leverages existing `geotop_chain_simplex_vertices_in_top` etc. infrastructure (Week 1 work + carrier-map machinery).
Cons: need to prove affine independence of cell barycenters in chains, plus coverage.

### Recommendation (per mathematician)

> If your current development already has strong barycentric subdivision machinery, Option B may be faster.

We have **substantial** barycentric infrastructure (28+ exports, including `geotop_chain_simplex_vertices_in_top`, `geotop_K_carriers_of_barycenters`). **Choose Option B.**

---

## Phase 5 attack outline (Option B)

### Step 5.1: Cell barycenter (~10 lines)

```isabelle
definition geotop_cell_barycenter :: "'a::euclidean_space set ⇒ 'a" where
  "geotop_cell_barycenter C = (SOME b. b ∈ rel_interior C)"
```

(Or a more specific construction using the convex hull's vertex set average.)

**Risk:** low.

### Step 5.2: Cell chain definition (~10 lines)

```isabelle
definition geotop_cell_flags :: "'a::euclidean_space set set ⇒ 'a set list set" where
  "geotop_cell_flags C =
     {c. c ≠ [] ∧ set c ⊆ C ∧ sorted_wrt (λA B. A ⊊ B) c ∧ distinct c}"
```

**Risk:** very low. Mirrors `geotop_flags`.

### Step 5.3: Cell-flag barycenter set is affinely independent (~80 lines)

```isabelle
lemma geotop_cell_flag_barycenters_affine_indep:
  fixes C :: "'a::euclidean_space set set"
  assumes hC: "geotop_cell_complex C"
  assumes hc: "c ∈ geotop_cell_flags C"
  shows "¬ affine_dependent (geotop_cell_barycenter ` set c)"
```

**Approach:** mirror `geotop_complex_flag_barycenter_affine_independent` (existing for simplices, line ~3500). The key fact: for a chain `A_0 ⊊ A_1 ⊊ ... ⊊ A_k`, barycenters are in distinct rel_interiors of nested cells, hence affinely independent.

**Risk:** medium. The simplicial version uses simplex-specific properties; need to generalize to cells.

### Step 5.4: Cell chain-simplex (~30 lines)

```isabelle
definition geotop_cell_chain_simplex :: "'a::euclidean_space set list ⇒ 'a set" where
  "geotop_cell_chain_simplex c = convex hull (geotop_cell_barycenter ` set c)"
```

Lemma: chain-simplex of a cell-flag is a simplex (uses 5.3 + finite vertex set).

**Risk:** low.

### Step 5.5: Define the order complex (~5 lines)

```isabelle
definition geotop_order_complex :: 
  "'a::euclidean_space set set ⇒ 'a set set" where
  "geotop_order_complex C = 
     {S. ∃c ∈ geotop_cell_flags C. S = geotop_cell_chain_simplex c}"
```

**Risk:** very low.

### Step 5.6: Order complex is a simplicial complex (~50 lines)

```isabelle
theorem geotop_order_complex_is_simplicial_complex:
  assumes "geotop_cell_complex C"
  shows "geotop_is_complex (geotop_order_complex C)"
```

**Approach:**
- K.0 (each element is a simplex): from chain-simplex def + 5.3 + 5.4.
- K.1 (closed under faces): face of chain-simplex corresponds to sub-chain.
- K.2 (pairwise intersection is a face): non-trivial; uses cell complex pairwise intersection.
- K.3 (locally finite): trivial since order complex is finite.

**Risk:** medium. K.2 is the tricky part.

### Step 5.7: Polyhedron equality (~40 lines)

```isabelle
theorem geotop_order_complex_polyhedron:
  assumes "geotop_cell_complex C"
  shows "geotop_polyhedron (geotop_order_complex C) = geotop_cell_polyhedron C"
```

**Approach:** ⊆ direct (each chain-simplex is in some chain-top cell). ⊇: for each x ∈ |C|, x lies in some cell A; barycenter chain ending at A's K-carrier in C gives a chain-simplex containing x. Uses inductive construction.

**Risk:** medium-high. The ⊇ direction requires a constructive argument.

### Step 5.8: Order complex refines C (~15 lines)

```isabelle
theorem geotop_order_complex_refines:
  assumes "geotop_cell_complex C"
  assumes "S ∈ geotop_order_complex C"
  shows "∃A ∈ C. S ⊆ A"
```

**Approach:** S = chain-simplex of c. Take A = last c (chain top). barycenters of c ⊆ A (analog of `geotop_chain_simplex_vertices_in_top` for cells). conv hull ⊆ A by convexity.

**Risk:** low. Mirrors existing simplex argument.

### Step 5.9: Cell-by-cell coverage (induced subdivisions) (~30 lines)

```isabelle
theorem geotop_order_complex_induced_subdivision:
  assumes "geotop_cell_complex C"
  assumes "A ∈ C"
  shows "A = ⋃ {S ∈ geotop_order_complex C. S ⊆ A}"
```

**Approach:** ⊇ direct. ⊆: for each x ∈ A, find a chain-simplex containing x with A as chain-top. Uses the same inductive argument as 5.7.

**Risk:** medium-high. This is the **face-compatible coverage** condition flagged in mathematician's §27.

### Step 5.10: Main theorem (~10 lines, just packaging)

```isabelle
theorem geotop_cell_complex_has_simplicial_subdivision:
  fixes C :: "'a::euclidean_space set set"
  assumes hC: "geotop_cell_complex C"
  shows "∃M. geotop_is_complex M ∧ finite M ∧
              geotop_cell_is_subdivision M C ∧
              (∀A∈C. A = ⋃ {S∈M. S ⊆ A})"
```

**Approach:** witness M = order_complex C. Use 5.6 (simplicial complex), 5.7 (polyhedron), 5.8 (refinement), 5.9 (cell coverage).

**Risk:** very low (just bundling).

---

## Order of attack

1. Steps 5.1-5.5 (~30 min): definitions.
2. Step 5.3 (~90 min): affine independence — substantive.
3. Step 5.6 (~60 min): order complex K.0/K.1/K.2/K.3.
4. Step 5.7 (~60 min): polyhedron equality — substantive.
5. Step 5.8 (~15 min): refinement.
6. Step 5.9 (~60 min): induced subdivisions — substantive.
7. Step 5.10 (~10 min): main theorem packaging.

Total: ~5-6 hours interactive work, ~200-300 lines.

---

## Risk mitigation

- **Forward references**: Phase 5 uses Phases 1-4 + Week 1 barycentric infrastructure. All in scope.
- **Cell barycenter definition**: SOME-style might be hard to reason about. Alternative: use specific point like `1/|V| ∑ V` if cell = conv hull V. Use Phase 1's geotop_cell_def.
- **K.2 axiom for order complex**: hardest. May require a sub-lemma that pairwise intersection of chain-simplices is a chain-simplex of a sub-chain.

---

## Validation checklist

- [ ] All 10 lemmas compile with no sorries.
- [ ] Build green at ~25-30s.
- [ ] Sorry count: still 1.
- [ ] PLAN3_PHASE6.md drafted.

---

## Handoff notes for Phase 6

After Phase 5, we have:
- Order-complex triangulation of any finite cell complex.
- Cell-by-cell face-compatible coverage.

Phase 6 will bridge this back to `geotop_is_subdivision` (Munkres-style) by combining the order-complex triangulation of the overlay complex with the union condition.
