# PLAN3_PHASE2.md — Phase 2: Cell faces

**Goal:** Define faces of convex cells (via HOL-Analysis `face_of` predicate), prove basic face lemmas, establish that cells have finitely many faces.

**Status entering Phase 2:** Phase 1 complete. Sorry count: 1 (the false theorem, unchanged).

**Estimated:** ~100-150 lines of Isar / 1 day interactive work / 3-5 commits.

**Output deliverables (all FULLY PROVEN):**
1. `geotop_cell_face` definition (via HOL-Analysis `face_of`).
2. `geotop_cell_face_refl` — every cell is a face of itself.
3. `geotop_cell_face_imp_cell` — face of a cell is a cell.
4. `geotop_cell_face_imp_subset` — face is contained in parent.
5. `geotop_cell_face_trans` — face of face is a face.
6. `geotop_cell_finite_faces` — every cell has finitely many faces.
7. `geotop_simplex_face_imp_cell_face` — simplex faces are cell faces.

---

## Setup checklist (first 15 minutes)

1. Open Isabelle/jEdit. Verify cached build green at ~22-25s.
2. Re-read PLAN3_PHASE1.md and PLAN3.md for context.
3. Check HOL-Analysis `face_of` definition and lemmas:

```bash
grep -rn "face_of\b\|^lemma.*face_of" /project/src/HOL/Analysis/Polytope.thy 2>/dev/null | head -30
```

This should reveal: `face_of`, `face_of_imp_subset`, `face_of_refl`, `face_of_trans`, `face_of_convex_hull_*`, `polytope_face_of_subset_of_polytope`, etc.

4. Locate insertion point: just after Phase 1 lemmas (search for `geotop_cell_intersection` at line ~10998 or wherever Phase 1 lands).

---

## Hudson's face definition

From Hudson Chapter I appendix (lines 653-668):

> B is a face of cell A iff:
> (1) P ∩ A = B, where P is the hyperplane spanned by B.
> (2) No point of P lies between any two points of A − B.

This is the **exposed-face / supporting-hyperplane** characterization. Equivalent to HOL-Analysis's `face_of` for closed convex sets in finite-dimensional Euclidean space.

**Pragmatic strategy:** use HOL-Analysis `face_of` directly. Don't re-derive Hudson's halfspace characterization unless required.

```isabelle
definition geotop_cell_face :: "'a::euclidean_space set ⇒ 'a set ⇒ bool" where
  "geotop_cell_face F C ⟷ geotop_cell C ∧ F ≠ {} ∧ F face_of C"
```

**Note**: `F ≠ {}` is a stylistic choice. Hudson allows the empty face implicitly via the empty cell. In our formalization we exclude the empty cell (Phase 1 def requires `C ≠ {}`), so faces are also non-empty.

---

## Phase 2 attack outline

### Step 2.1: Define `geotop_cell_face` (~3 lines)

```isabelle
definition geotop_cell_face :: "'a::euclidean_space set ⇒ 'a set ⇒ bool" where
  "geotop_cell_face F C ⟷ geotop_cell C ∧ F ≠ {} ∧ F face_of C"
```

**Risk:** very low.

### Step 2.2: Reflexivity (~5 lines)

```isabelle
lemma geotop_cell_face_refl:
  assumes "geotop_cell C"
  shows "geotop_cell_face C C"
  unfolding geotop_cell_face_def
  using assms geotop_cell_nonempty[OF assms] face_of_refl ... 
```

**Risk:** very low. Need `face_of_refl` (HOL-Analysis: any convex set is a face of itself).

Actually `face_of_refl` requires C convex. Use `geotop_cell_convex` from Phase 1.

### Step 2.3: Subset property (~5 lines)

```isabelle
lemma geotop_cell_face_imp_subset:
  assumes "geotop_cell_face F C"
  shows "F ⊆ C"
  using assms unfolding geotop_cell_face_def using face_of_imp_subset by blast
```

**Risk:** very low.

### Step 2.4: Face is a cell (~30 lines)

```isabelle
lemma geotop_cell_face_imp_cell:
  fixes F C :: "'a::euclidean_space set"
  assumes "geotop_cell_face F C"
  shows "geotop_cell F"
```

**Approach:**
- F is a face of C, so F is a closed convex subset of C (HOL-Analysis: face_of_imp_compact when C compact).
- F is a polytope (face of polytope is polytope — HOL-Analysis: `polytope_face_of_polytope` or similar).
- Polytope = convex hull of finite set (HOL-Analysis: `polytope_def`).
- Therefore F = convex hull of finite set, hence a geotop_cell.

**HOL-Analysis support to look for:**
- `polytope_face_of_polytope`
- `polytope_def` (equivalent to "convex hull of finite set" for compact convex sets)

**Risk:** medium. Depends on HOL-Analysis providing these lemmas.

### Step 2.5: Transitivity (~10 lines)

```isabelle
lemma geotop_cell_face_trans:
  assumes "geotop_cell_face F G"
  assumes "geotop_cell_face G C"
  shows "geotop_cell_face F C"
```

**Approach:** uses HOL-Analysis `face_of_trans`: face of face is face. Plus F is a cell from 2.4.

**Risk:** very low.

### Step 2.6: Finite faces (~30 lines)

```isabelle
lemma geotop_cell_finite_faces:
  fixes C :: "'a::euclidean_space set"
  assumes "geotop_cell C"
  shows "finite {F. geotop_cell_face F C}"
```

**Approach:**
- C is a polytope (= convex hull of finite V).
- Polytope has finitely many faces (HOL-Analysis: `finite_polyhedron_faces` or `finite_face_of`).

**HOL-Analysis support:** look for `finite_polytope_faces`, `polyhedron_finite_faces`, etc.

**Risk:** medium-low. Depends on HOL-Analysis lemma availability.

### Step 2.7: Simplex faces are cell faces (~10 lines)

```isabelle
lemma geotop_simplex_face_imp_cell_face:
  fixes σ τ :: "'a::euclidean_space set"
  assumes hσ: "geotop_is_simplex σ"
  assumes hτ_face: "geotop_is_face τ σ"
  shows "geotop_cell_face τ σ"
```

**Approach:**
- σ and τ are both simplices (geotop_is_face hypothesis ⟹ τ is simplex).
- σ is a cell (Phase 1 Step 1.3).
- τ ⊆ σ and τ is a "geometric" face of σ in the simplicial sense.
- Need: τ face_of σ in HOL-Analysis sense.

**Risk:** low. The bridge from `geotop_is_face` to `face_of` should be derivable from existing geotop_is_face definitions.

---

## Order of attack

1. Steps 2.1-2.3 (~15 min): definition, reflexivity, subset.
2. Step 2.4 (~30 min): face is a cell — substantive.
3. Step 2.5 (~10 min): transitivity.
4. Step 2.6 (~30 min): finite faces — substantive.
5. Step 2.7 (~15 min): simplex face bridge.

Total: ~1.5 hours interactive work, ~80-150 lines.

---

## Risk mitigation

- **HOL-Analysis face_of vs polytope distinction**: face_of is general (for convex sets), polytope has specific definition. Make sure we apply the right lemmas.

- **Forward references**: ensure Phase 1 lemmas are above. Check `geotop_cell` and properties land before this Phase.

- **Empty face convention**: Hudson allows empty face implicitly. We exclude. If downstream needs empty face, can add later.

---

## Validation checklist

After Phase 2 completes:

- [ ] All 7 lemmas (2.1-2.7) compile with no sorries.
- [ ] Build green at ~22-25s.
- [ ] Sorry count in basis: still 1 (the false theorem; Phase 2 doesn't touch it yet).
- [ ] PLAN3_PHASE2.md marked complete; PLAN3_PHASE3.md drafted.

---

## Handoff notes for Phase 3

After Phase 2:
- Cell faces are a working notion via HOL-Analysis `face_of`.
- Cell complexes can be defined with the standard "closed under faces, pairwise common-face intersection" axioms.

Phase 3 will define cell complexes, cell-complex polyhedron, and cell-complex subdivision (Hudson Definitions, lines 148-164). Mostly mechanical.
