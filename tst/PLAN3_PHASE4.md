# PLAN3_PHASE4.md — Phase 4: Overlay cell complex

**Goal:** Define raw overlay cells (`σ ∩ τ` for `σ ∈ L1`, `τ ∈ L2`), close under faces, and prove this is a finite cell complex covering the common polyhedron and refining both `L1` and `L2`.

**Status entering Phase 4:** Phases 1-3 complete. Sorry count: 1.

**Estimated:** ~150-200 lines of Isar / 1-2 days interactive work / 5-7 commits.

**Output deliverables (all FULLY PROVEN):**
1. `geotop_overlay_cells` raw definition.
2. `geotop_face_closure` operation.
3. `geotop_overlay_complex` (face-closed overlay).
4. `geotop_overlay_complex_finite` — finiteness.
5. `geotop_overlay_complex_is_cell_complex` — is a cell complex.
6. `geotop_overlay_complex_union` — covers common polyhedron.
7. `geotop_overlay_complex_refines_left/right` — refines L1, L2.

---

## Setup checklist

1. Verify Phase 3 build green.
2. Re-read mathematician's recommendation about face-closure (ANSWER_REPORT.md §15).
3. Locate insertion point: just after Phase 3 lemmas.

---

## Key strategy from mathematician

Per ANSWER_REPORT.md §15:

> ### Strong recommendation
> Use **face closure**. It is safer for formalization.
>
> Then the overlay definition becomes:
> ```isabelle
> definition geotop_overlay_complex where
>   "geotop_overlay_complex L1 L2 =
>      geotop_face_closure (geotop_overlay_cells L1 L2)"
> ```
> Now the closure-under-faces property is by construction.

This avoids the difficulty of proving "every face of σ ∩ τ is itself an overlay cell" (which Hudson's original definition would require).

---

## Phase 4 attack outline

### Step 4.1: Raw overlay cells (~5 lines)

```isabelle
definition geotop_overlay_cells :: 
  "'a::euclidean_space set set ⇒ 'a set set ⇒ 'a set set" where
  "geotop_overlay_cells L1 L2 =
     {C. ∃σ∈L1. ∃τ∈L2. C = σ ∩ τ ∧ C ≠ {}}"
```

**Risk:** very low.

### Step 4.2: Face closure operation (~5 lines)

```isabelle
definition geotop_face_closure :: 
  "'a::euclidean_space set set ⇒ 'a set set" where
  "geotop_face_closure C = {F. ∃A∈C. geotop_cell_face F A}"
```

**Risk:** very low.

### Step 4.3: Overlay complex (~3 lines)

```isabelle
definition geotop_overlay_complex :: 
  "'a::euclidean_space set set ⇒ 'a set set ⇒ 'a set set" where
  "geotop_overlay_complex L1 L2 = geotop_face_closure (geotop_overlay_cells L1 L2)"
```

**Risk:** very low.

### Step 4.4: Raw cells are cells (~30 lines)

```isabelle
lemma geotop_overlay_cells_are_cells:
  fixes L1 L2 :: "'a::euclidean_space set set"
  assumes "geotop_is_complex L1" "geotop_is_complex L2"
  assumes "finite L1" "finite L2"
  assumes "C ∈ geotop_overlay_cells L1 L2"
  shows "geotop_cell C"
```

**Approach:**
- Obtain σ ∈ L1, τ ∈ L2, C = σ ∩ τ ≠ {}.
- σ is a simplex (complex K.0), hence a cell (Phase 1 Step 1.3).
- τ similarly.
- Cell ∩ cell = cell (Phase 1 Step 1.4) when non-empty.

**Risk:** low.

### Step 4.5: Raw cells finite (~10 lines)

```isabelle
lemma geotop_overlay_cells_finite:
  assumes "finite L1" "finite L2"
  shows "finite (geotop_overlay_cells L1 L2)"
```

**Approach:** raw cells are images of `(σ, τ) ↦ σ ∩ τ` over `L1 × L2`, which is finite.

**Risk:** very low.

### Step 4.6: Raw cells cover common polyhedron (~30 lines)

```isabelle
lemma geotop_overlay_cells_union:
  fixes L1 L2 :: "'a::euclidean_space set set"
  assumes "geotop_polyhedron L1 = geotop_polyhedron L2"
  shows "⋃ (geotop_overlay_cells L1 L2) = geotop_polyhedron L1"
```

**Approach:** ⊆ trivial. ⊇: if x ∈ |L1| then x ∈ σ for some σ ∈ L1; |L1| = |L2| gives x ∈ τ for some τ ∈ L2; hence x ∈ σ ∩ τ which is non-empty, so σ ∩ τ ∈ overlay_cells.

**Risk:** low.

### Step 4.7: Raw cells refine left and right (~5 lines each)

```isabelle
lemma geotop_overlay_cells_refines_left:
  assumes "C ∈ geotop_overlay_cells L1 L2"
  shows "∃σ∈L1. C ⊆ σ"

lemma geotop_overlay_cells_refines_right:
  assumes "C ∈ geotop_overlay_cells L1 L2"
  shows "∃τ∈L2. C ⊆ τ"
```

**Risk:** very low. Direct from definition.

### Step 4.8: Overlay complex finite (~20 lines)

```isabelle
lemma geotop_overlay_complex_finite:
  assumes "geotop_is_complex L1" "geotop_is_complex L2"
  assumes "finite L1" "finite L2"
  shows "finite (geotop_overlay_complex L1 L2)"
```

**Approach:**
- Raw cells are finite (Step 4.5).
- Each raw cell is a cell, hence has finitely many faces (Phase 2 Step 2.6).
- Face closure of a finite set of cells with finitely many faces each is finite.

**Risk:** medium. Need careful counting.

### Step 4.9: Each face-closure element is a cell (~15 lines)

```isabelle
lemma geotop_overlay_complex_elt_is_cell:
  assumes "geotop_is_complex L1" "geotop_is_complex L2"
  assumes "finite L1" "finite L2"
  assumes "F ∈ geotop_overlay_complex L1 L2"
  shows "geotop_cell F"
```

**Approach:** F is a face of some raw cell C. Raw cell is a cell (Step 4.4). Face of a cell is a cell (Phase 2 Step 2.4).

**Risk:** low.

### Step 4.10: Overlay complex closed under faces (~10 lines)

```isabelle
lemma geotop_overlay_complex_closed_under_faces:
  assumes "F ∈ geotop_overlay_complex L1 L2"
  assumes "geotop_cell_face G F"
  shows "G ∈ geotop_overlay_complex L1 L2"
```

**Approach:** F is a face of some raw cell C. G is a face of F. By transitivity (Phase 2 Step 2.5), G is a face of C. Hence G ∈ face_closure(raw_cells).

**Risk:** low.

### Step 4.11: Pairwise intersection is common face (~30 lines, the substantive part)

```isabelle
lemma geotop_overlay_complex_pairwise_face:
  assumes "geotop_is_complex L1" "geotop_is_complex L2"
  assumes "F1 ∈ geotop_overlay_complex L1 L2"
  assumes "F2 ∈ geotop_overlay_complex L1 L2"
  assumes "F1 ∩ F2 ≠ {}"
  shows "geotop_cell_face (F1 ∩ F2) F1 ∧ geotop_cell_face (F1 ∩ F2) F2"
```

**Approach (per mathematician's note in §16):**
- F1 is a face of raw cell `σ1 ∩ τ1`, F2 is a face of raw cell `σ2 ∩ τ2`.
- F1 ∩ F2 is a face of `(σ1 ∩ τ1) ∩ (σ2 ∩ τ2) = (σ1 ∩ σ2) ∩ (τ1 ∩ τ2)`.
- Since L1, L2 are simplicial complexes, `σ1 ∩ σ2` is empty or common face, similarly `τ1 ∩ τ2`.
- Hence the intersection is well-structured and F1 ∩ F2 is a common face.

**Risk:** medium-high. This is the geometric core of the overlay construction.

### Step 4.12: Overlay complex is a cell complex (~15 lines)

```isabelle
theorem geotop_overlay_complex_is_cell_complex:
  assumes "geotop_is_complex L1" "geotop_is_complex L2"
  assumes "finite L1" "finite L2"
  shows "geotop_cell_complex (geotop_overlay_complex L1 L2)"
```

**Approach:** combine 4.8 (finite) + 4.9 (elements are cells) + 4.10 (closed under faces) + 4.11 (pairwise face intersection).

**Risk:** low if 4.11 succeeds.

### Step 4.13: Polyhedron and refinement properties (~30 lines)

```isabelle
lemma geotop_overlay_complex_union:
  assumes "geotop_polyhedron L1 = geotop_polyhedron L2"
  shows "geotop_cell_polyhedron (geotop_overlay_complex L1 L2) = geotop_polyhedron L1"

lemma geotop_overlay_complex_refines_left:
  assumes "F ∈ geotop_overlay_complex L1 L2"
  shows "∃σ∈L1. F ⊆ σ"

lemma geotop_overlay_complex_refines_right:
  assumes "F ∈ geotop_overlay_complex L1 L2"
  shows "∃τ∈L2. F ⊆ τ"
```

**Approach:**
- Polyhedron: face closure of raw cells covers what raw cells cover; raw cells cover common polyhedron (Step 4.6).
- Refinement: F is a face of raw cell C; C ⊆ σ ∈ L1 (Step 4.7); F ⊆ C ⊆ σ.

**Risk:** low.

### Step 4.14: Each L1-simplex is a union of overlay cells (~30 lines)

```isabelle
lemma geotop_overlay_complex_covers_each_left_simplex:
  assumes "σ ∈ L1"
  assumes "geotop_polyhedron L1 = geotop_polyhedron L2"
  shows "σ = ⋃ {A ∈ geotop_overlay_complex L1 L2. A ⊆ σ}"
```

(And analogous for L2.)

**Approach (per mathematician's §27):**
- σ = ⋃ overlay_cells contained in σ (since L1, L2 partition σ via simplicial intersections).
- Each overlay cell is also in face-closed overlay.

**Risk:** medium. Subtle but essential for the union condition in Phase 6.

---

## Order of attack

1. Steps 4.1-4.3 (~10 min): definitions.
2. Steps 4.4-4.7 (~30 min): raw cell properties.
3. Steps 4.8-4.10 (~30 min): face-closed complex properties.
4. Step 4.11 (~60 min): pairwise face intersection — substantive.
5. Step 4.12 (~10 min): combine into cell complex theorem.
6. Steps 4.13-4.14 (~45 min): polyhedron, refinement, union per simplex.

Total: ~3 hours interactive work, ~150-200 lines.

---

## Validation checklist

- [ ] All 14 lemmas compile with no sorries.
- [ ] Build green at ~22-25s.
- [ ] Sorry count: still 1.
- [ ] PLAN3_PHASE5.md drafted.

---

## Handoff notes for Phase 5

After Phase 4, we have:
- Working overlay cell complex covering the common polyhedron.
- Refinement properties to L1 and L2.

Phase 5 is **the major work**: triangulating the overlay cell complex to get a simplicial subdivision. This will use either Hudson Lemma 1.4 (induction by dimension) or the order-complex / barycentric subdivision approach (Option B from mathematician — leverages our existing barycentric infra).
