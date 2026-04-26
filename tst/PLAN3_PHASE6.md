# PLAN3_PHASE6.md — Phase 6: Bridge from cell-subdivision to simplicial-subdivision

**Goal:** Bridge from the cell-complex world (Phases 3-5) back to the existing simplicial `geotop_is_subdivision` notion. Specifically: derive that the order-complex triangulation of the overlay complex is a Munkres-style subdivision of `L1` (and `L2`).

**Status entering Phase 6:** Phases 1-5 complete. Sorry count: 1.

**Estimated:** ~100-150 lines of Isar / 1 day interactive work / 4-6 commits.

**Output deliverables (all FULLY PROVEN):**
1. `geotop_simplicial_subdivision_from_cell_subdivision` — main bridge.
2. `geotop_overlay_triangulation_subdivides_left/right` — applies to overlay scenario.

---

## Setup checklist

1. Verify Phases 1-5 build green.
2. Re-read mathematician's §27-28 on the bridge.
3. Locate insertion point.

---

## Hudson + Mathematician guidance

The mathematician (ANSWER_REPORT.md §27-28) emphasizes:

> The union condition (every coarse simplex = finite union of finer simplices) is **NOT automatic** from containment + finiteness + polyhedron equality. Requires face-compatible triangulation.
>
> To make the union condition easy, formulate the triangulation theorem as a subdivision of the cell complex, not just a cover by simplices. Add this:
>
> ```isabelle
> ∀A ∈ C. A = ⋃ {ρ ∈ M. ρ ⊆ A}
> ```

We added this to Phase 5 Step 5.9. Now we use it.

---

## Phase 6 attack outline

### Step 6.1: General bridge lemma (~50 lines)

```isabelle
lemma geotop_simplicial_subdivision_from_cell_subdivision:
  fixes M C :: "'a::euclidean_space set set"
  fixes L :: "'a::euclidean_space set set"
  assumes hL: "geotop_is_complex L"
  assumes hLfin: "finite L"
  assumes hM_simp: "geotop_is_complex M"
  assumes hMfin: "finite M"
  assumes hC_cell: "geotop_cell_complex C"
  assumes hMC: "geotop_cell_is_subdivision M C"
  assumes h_C_in_L: "∀A ∈ C. ∃σ ∈ L. A ⊆ σ"
  assumes h_L_covered: "∀σ ∈ L. σ = ⋃ {A ∈ C. A ⊆ σ}"
  assumes h_M_induced: "∀A ∈ C. A = ⋃ {ρ ∈ M. ρ ⊆ A}"
  shows "geotop_is_subdivision M L"
```

**Approach:**
- Need to show:
  (a) M is a complex (given by hM_simp).
  (b) L is a complex (given by hL).
  (c) `geotop_polyhedron M = geotop_polyhedron L`.
  (d) `∀ρ ∈ M. ∃σ ∈ L. ρ ⊆ σ` (the refinement / Munkres clause 1).

For (c): polyhedron of M = polyhedron of C (cell subdivision) = polyhedron of L (chain via h_L_covered).

For (d): ρ ∈ M ⟹ ρ lies in some cell A ∈ C (cell subdivision); A ⊆ σ for some σ ∈ L (h_C_in_L); transitively ρ ⊆ σ.

Note: our `geotop_is_subdivision` definition (in `b0/GeoTopBase0.thy`) requires:
- both complexes
- |M| = |L|
- geotop_refines M L (which is `∀ρ ∈ M. ∃σ ∈ L. ρ ⊆ σ`)

The Munkres "every L-simplex is finite union of M-simplices" is implied by the polyhedron-equality + refinement + finiteness combination, which we have via h_L_covered + h_M_induced.

**Risk:** medium. The polyhedron equality chain requires careful unfolding.

### Step 6.2: Applied to overlay scenario (left side) (~30 lines)

```isabelle
lemma geotop_overlay_triangulation_subdivides_left:
  fixes L1 L2 :: "'a::euclidean_space set set"
  assumes hL1: "geotop_is_complex L1"
  assumes hL2: "geotop_is_complex L2"
  assumes hfL1: "finite L1"
  assumes hfL2: "finite L2"
  assumes hpoly: "geotop_polyhedron L1 = geotop_polyhedron L2"
  assumes hM: "geotop_is_complex M"
  assumes hMfin: "finite M"
  assumes hMC: "geotop_cell_is_subdivision M (geotop_overlay_complex L1 L2)"
  assumes hM_induced: "∀A ∈ geotop_overlay_complex L1 L2. A = ⋃ {ρ ∈ M. ρ ⊆ A}"
  shows "geotop_is_subdivision M L1"
```

**Approach:** Apply 6.1 with C = overlay complex, L = L1.
- h_C_in_L: from Phase 4 Step 4.13 `geotop_overlay_complex_refines_left`.
- h_L_covered: from Phase 4 Step 4.14 `geotop_overlay_complex_covers_each_left_simplex`.

**Risk:** low.

### Step 6.3: Applied to overlay scenario (right side) (~30 lines)

```isabelle
lemma geotop_overlay_triangulation_subdivides_right:
  ... (same shape, L = L2)
```

**Risk:** very low (mirror of 6.2).

---

## Order of attack

1. Step 6.1 (~90 min): general bridge — substantive.
2. Steps 6.2-6.3 (~30 min): overlay applications.

Total: ~2 hours interactive work, ~100-150 lines.

---

## Validation checklist

- [ ] All 3 lemmas compile with no sorries.
- [ ] Build green at ~25-30s.
- [ ] Sorry count: still 1.
- [ ] PLAN3_PHASE7.md drafted.

---

## Handoff notes for Phase 7

After Phase 6:
- We can derive `geotop_is_subdivision M L1` and `geotop_is_subdivision M L2` whenever M is the order-complex triangulation of the overlay.

Phase 7 just packages this into the main theorem `geotop_common_subdivision_finite`.
