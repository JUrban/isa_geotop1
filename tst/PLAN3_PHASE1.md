# PLAN3_PHASE1.md — Phase 1: Convex cells

**Goal:** Define convex linear cells (per Hudson Chapter I §2) and prove the basic facts: every simplex is a cell, intersection of cells is a cell.

**Status entering Phase 1:** Phase 0 complete (commit `d7789231`). False theorem quarantined as `_FALSE`. Sorry count: 1. Build green at 23s.

**Estimated:** ~150-200 lines of Isar / 1-2 days interactive work / 4-6 commits.

**Output deliverables (all FULLY PROVEN):**
1. Definition: `geotop_cell` (a non-empty finite-vertex convex hull).
2. Lemma: `geotop_simplex_imp_cell` — every Euclidean simplex is a cell.
3. Lemma: `geotop_cell_intersection` — non-empty intersection of cells is a cell.
4. Lemma: `geotop_cell_compact`, `_closed`, `_convex` — basic properties.

---

## Setup checklist (first 15 minutes)

1. Open Isabelle/jEdit on `/project/tst/b0/GeoTopBase0.thy`. Verify cached build green at ~22s.
2. Re-read PLAN3.md (revised) and ANSWER_REPORT.md for context.
3. Locate insertion point: just **after** the false theorem block (search for `geotop_iterated_Sd_refines_subdivision_FALSE`, line ~10998-11020). Place new Phase 1 lemmas BEFORE Theorem_GT_1 (so they can be used in its eventual replacement).
4. Search for existing HOL-Analysis polytope infrastructure:

```bash
grep -rn "polytope\|^lemma.*polytope\|^definition.*polytope" /project/src/HOL/Analysis/ 2>/dev/null | head -20
```

This will tell us if HOL-Analysis already provides `polytope` (a closed bounded polyhedron / convex hull of finite set). If yes, we should reuse it. If not, define our own.

---

## Hudson's cell definition

From Hudson Chapter I §2 (line 108-112):

> (1) A cell is convex. Moreover, it is the convex hull of its vertices.
> (2) The intersection and product of cells are cells.
> (3) The convex hull of a finite set is a cell.
> (4) Let A ⊆ E^p be a cell. Let f: E^p → E^q be (affine) linear. Then f(A) is a cell.

Hudson assumes (1)-(4) and a halfspace characterization of faces. For our purposes (Option B from the mathematician), we use the **convex-hull characterization** as the primary definition, since this matches our existing simplex definition (`geotop_is_simplex σ ⟷ ∃V. ... ∧ σ = geotop_convex_hull V`).

```isabelle
definition geotop_cell :: "'a::euclidean_space set ⇒ bool" where
  "geotop_cell C ⟷ C ≠ {} ∧ (∃V. finite V ∧ C = convex hull V)"
```

(This is "non-empty polytope" in HOL-Analysis terminology.)

---

## Phase 1 attack outline

### Step 1.1: Define `geotop_cell` (~5 lines)

```isabelle
definition geotop_cell :: "'a::euclidean_space set ⇒ bool" where
  "geotop_cell C ⟷ C ≠ {} ∧ (∃V. finite V ∧ C = convex hull V)"
```

**Risk:** very low.

### Step 1.2: Basic properties — `geotop_cell_nonempty`, `_convex`, `_compact`, `_closed` (~30 lines)

```isabelle
lemma geotop_cell_nonempty:
  assumes "geotop_cell C"
  shows "C ≠ {}"
  using assms unfolding geotop_cell_def by blast

lemma geotop_cell_convex:
  assumes "geotop_cell C"
  shows "convex C"
  (* From convex_convex_hull *)

lemma geotop_cell_compact:
  fixes C :: "'a::euclidean_space set"
  assumes "geotop_cell C"
  shows "compact C"
  (* From compact_convex_hull on a finite set V *)

lemma geotop_cell_closed:
  fixes C :: "'a::euclidean_space set"
  assumes "geotop_cell C"
  shows "closed C"
  (* From compact ⟹ closed *)
```

**Risk:** low. Direct unfolding + HOL-Analysis lemmas (`convex_convex_hull`, `compact_convex_hull`, `finite_imp_compact`, `compact_imp_closed`).

### Step 1.3: `geotop_simplex_imp_cell` (~15 lines)

```isabelle
lemma geotop_simplex_imp_cell:
  fixes σ :: "'a::euclidean_space set"
  assumes "geotop_is_simplex σ"
  shows "geotop_cell σ"
proof -
  obtain V where hVfin: "finite V" and hV_ne: "V ≠ {}"
                and hV_HOL: "σ = convex hull V"
    using geotop_simplex_obtain_HOL[OF assms] by blast
  have "σ ≠ {}" using hV_ne hV_HOL hull_subset by blast
  show ?thesis
    unfolding geotop_cell_def
    using hVfin hV_HOL ‹σ ≠ {}› by blast
qed
```

**Risk:** very low. Uses existing `geotop_simplex_obtain_HOL` (W1.0 era export, line ~4140).

### Step 1.4: `geotop_cell_intersection` (~80-100 lines, the substantive part)

```isabelle
lemma geotop_cell_intersection:
  fixes A B :: "'a::euclidean_space set"
  assumes hA: "geotop_cell A"
  assumes hB: "geotop_cell B"
  assumes h_int_ne: "A ∩ B ≠ {}"
  shows "geotop_cell (A ∩ B)"
```

**Approach:** the intersection of two convex hulls of finite sets is again a polytope (this is a theorem in convex geometry, Minkowski-Weyl). Specifically:
- Both A and B are bounded convex polyhedra (intersections of finitely many halfspaces).
- A ∩ B is also a bounded convex polyhedron.
- A ∩ B has finitely many vertices, and equals the convex hull of those vertices.

**HOL-Analysis support:** this should exist as `polytope_Int` or similar. If not, we'll need to prove it.

**Strategy:**
1. First check HOL-Analysis for `polytope_Int`. If exists, reuse directly.
2. If not, prove via halfspace representation:
   - A = ⋂ halfspaces, B = ⋂ halfspaces (both finite)
   - A ∩ B = ⋂ all those halfspaces (still finite)
   - A ∩ B is a polyhedron (closed convex)
   - A ∩ B is bounded (subset of A)
   - Bounded polyhedron = polytope = convex hull of vertices

**Risk:** medium. Could be ~30 lines if HOL-Analysis has `polytope_Int`, ~100+ lines otherwise.

### Step 1.5: `geotop_cell_subset_simplex_polyhedron` (~30 lines, useful corollary)

```isabelle
lemma geotop_cell_subset_simplex_polyhedron:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hC: "geotop_cell C"
  assumes hC_sub: "C ⊆ geotop_polyhedron K"
  shows "C ⊆ geotop_polyhedron K"
  by (rule hC_sub)
```

(Trivial — just to demonstrate cells live in polyhedra.)

Skip if not needed.

---

## Order of attack

1. **Step 1.1 + 1.2** (definition + basic properties): 30 minutes. Mechanical.
2. **Step 1.3** (simplex⇒cell): 15 minutes. Uses existing infrastructure.
3. **Step 1.4** (intersection of cells): 60-90 minutes. Most substantive part. May need to dig into HOL-Analysis.

Total: ~2 hours interactive work, ~150-200 lines of Isar.

---

## Risk mitigation

- **HOL-Analysis polytope infrastructure**: search `/project/src/HOL/Analysis` first. Look for `polytope`, `polytope_Int`, `polytope_convex_hull`, etc. If these exist, Phase 1 collapses to ~50 lines.

- **Forward references**: `geotop_simplex_obtain_HOL` is at line ~4140. Insert Phase 1 lemmas AFTER that. New lemmas should land near line ~10998 (after the false theorem) but BEFORE the Theorem_GT_1 (line ~11430).

- **Type class**: use `'a::euclidean_space` throughout (matches simplex definitions, has compactness/closedness).

- **CLAUDE.md sorry-only rule**: write each lemma with `sorry` first, get the structure to compile, then replace sorries with real proofs. Use `by (by100 X)` or apply chains, never bare automation.

- **Build cycle**: aim for ~22-25s green build after each step. If build slows significantly, bisect and revert.

---

## Validation checklist

After Phase 1 completes:

- [ ] All 4-5 lemmas (1.1-1.5) compile with no sorries.
- [ ] Build green at ~22-25s.
- [ ] Sorry count in basis: still 1 (the false theorem; Phase 1 doesn't touch it yet).
- [ ] Each lemma committed separately with descriptive message.
- [ ] PLAN3_PHASE1.md marked complete; PLAN3_PHASE2.md drafted.

---

## Handoff notes for Phase 2

After Phase 1:
- Have `geotop_cell` predicate defined and basic properties.
- Know simplex⇒cell.
- Know cell-intersection is a cell.

Phase 2 will define cell faces (using halfspace or exposed-face style) and prove transitive face relations. Phase 3 will define cell complexes. Phase 4 will define overlay cells and the face-closed overlay complex.

By the end of Phase 4, the new `geotop_overlay_complex` will exist as a working construction. Phase 5 (triangulation) is the major work; Phase 6-8 are bridges and cleanup.
