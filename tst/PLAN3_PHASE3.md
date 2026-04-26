# PLAN3_PHASE3.md — Phase 3: Convex cell complexes

**Goal:** Define convex linear cell complexes (Hudson Chapter I §2), cell-complex polyhedron, and cell-complex subdivision.

**Status entering Phase 3:** Phases 1-2 complete. Sorry count: 1 (unchanged false theorem).

**Estimated:** ~80-100 lines of Isar / ~3 hours interactive work / 3-4 commits.

**Output deliverables (all FULLY PROVEN):**
1. `geotop_cell_complex` definition.
2. `geotop_cell_polyhedron` definition.
3. `geotop_cell_is_subdivision` definition.
4. `geotop_simplicial_complex_imp_cell_complex` — bridge: simplicial⇒cell.

---

## Setup checklist

1. Verify Phase 2 build green.
2. Re-read Hudson lines 148-164 (cell complex definition + subdivision definition).
3. Locate insertion point: just after Phase 2 lemmas.

---

## Hudson's definitions

From Hudson Chapter I §2 (lines 148-164):

> A **convex linear cell complex** in `E^n` is a finite set of cells in `E^n`, K, such that
> 1. If A ∈ K, every face of A is in K.
> 2. If A and B ∈ K, then A ∩ B = ∅ or A ∩ B = common face of A and B.

> A **simplicial complex** is a cell complex whose cells are all simplices.

> If K and L are cell complexes, K is called a **subdivision** of L if:
> 1. |K| = |L|.
> 2. Every cell of K is a subset of some cell of L.

(Hudson Lemma 1.2 derives the converse "every cell of L is a union of cells of K", so this is equivalent to Munkres' two-clause definition.)

---

## Phase 3 attack outline

### Step 3.1: Define `geotop_cell_complex` (~10 lines)

```isabelle
definition geotop_cell_complex :: "'a::euclidean_space set set ⇒ bool" where
  "geotop_cell_complex C ⟷
     finite C ∧
     (∀A∈C. geotop_cell A) ∧
     (∀A∈C. ∀F. geotop_cell_face F A ⟶ F ∈ C) ∧
     (∀A∈C. ∀B∈C. A ∩ B = {} ∨
        (geotop_cell_face (A ∩ B) A ∧ geotop_cell_face (A ∩ B) B))"
```

**Risk:** very low.

### Step 3.2: Define `geotop_cell_polyhedron` (~3 lines)

```isabelle
definition geotop_cell_polyhedron :: "'a::euclidean_space set set ⇒ 'a set" where
  "geotop_cell_polyhedron C = ⋃ C"
```

**Risk:** very low.

### Step 3.3: Define `geotop_cell_is_subdivision` (~5 lines)

```isabelle
definition geotop_cell_is_subdivision :: 
  "'a::euclidean_space set set ⇒ 'a set set ⇒ bool" where
  "geotop_cell_is_subdivision C' C ⟷
     geotop_cell_complex C' ∧ geotop_cell_complex C ∧
     geotop_cell_polyhedron C' = geotop_cell_polyhedron C ∧
     (∀A∈C'. ∃B∈C. A ⊆ B)"
```

**Risk:** very low. This is Hudson's def directly.

### Step 3.4: Bridge — simplicial complex is a cell complex (~30 lines)

```isabelle
lemma geotop_simplicial_complex_imp_cell_complex:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  shows "geotop_cell_complex K"
```

**Approach:**
- K is finite (assumption).
- Each σ ∈ K is a simplex, hence a cell (Phase 1 Step 1.3).
- Each face of σ ∈ K is in K (geotop_is_complex K.1 axiom).
- Each pairwise intersection σ ∩ τ ∈ K is a common face (K.2 axiom).
- The "common face" in the simplicial sense gives the cell-face condition (Phase 2 Step 2.7 — simplex_face_imp_cell_face).

**Risk:** medium. The bridge from K.2 (simplex ∩ simplex = simplex face) to cell-face requires careful argument.

### Step 3.5: Polyhedron coincidence (~5 lines)

```isabelle
lemma geotop_simplicial_polyhedron_eq_cell_polyhedron:
  fixes K :: "'a::euclidean_space set set"
  shows "geotop_polyhedron K = geotop_cell_polyhedron K"
  unfolding geotop_polyhedron_def geotop_cell_polyhedron_def by simp
```

(Trivially true since both = ⋃ K.)

**Risk:** very low.

### Step 3.6: Subdivision bridge (~20 lines)

```isabelle
lemma geotop_simplicial_subdivision_imp_cell_subdivision:
  fixes K K' :: "'a::euclidean_space set set"
  assumes hK_subdiv: "geotop_is_subdivision K' K"
  assumes hKfin: "finite K"
  shows "geotop_cell_is_subdivision K' K"
```

**Approach:**
- Both K, K' are finite simplicial complexes.
- By 3.4, both are cell complexes.
- |K| = |K'| (subdivision property).
- Every K'-simplex ⊆ some K-simplex (subdivision property).
- Hence cell_is_subdivision.

**Risk:** low.

---

## Order of attack

1. Steps 3.1-3.3 (~15 min): definitions.
2. Step 3.5 (~5 min): polyhedron eq (trivial).
3. Step 3.4 (~45 min): simplicial⇒cell complex bridge — substantive.
4. Step 3.6 (~15 min): subdivision bridge.

Total: ~80 minutes / ~80-100 lines.

---

## Validation checklist

- [ ] All 6 definitions/lemmas compile with no sorries.
- [ ] Build green at ~22-25s.
- [ ] Sorry count: still 1.
- [ ] PLAN3_PHASE3.md marked complete; PLAN3_PHASE4.md drafted.

---

## Handoff notes for Phase 4

After Phase 3, we have:
- Cell complexes formalized.
- Bridge from simplicial complexes to cell complexes.

Phase 4 will define overlay cells (`σ ∩ τ` for `σ ∈ L1`, `τ ∈ L2`), close under faces, and prove this is a cell complex. The face-closure approach (per mathematician's recommendation) is the safer route. Phase 4 is the most substantive geometric construction in the new strategy.
