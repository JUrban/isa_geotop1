# PLAN3_PHASE7.md — Phase 7: Final common-subdivision theorem

**Goal:** Prove the main theorem `geotop_common_subdivision_finite` by combining Phases 4-6.

**Status entering Phase 7:** Phases 1-6 complete. Sorry count: 1.

**Estimated:** ~50 lines of Isar / 30-60 minutes interactive work / 1-2 commits.

**Output deliverable:**
1. `geotop_common_subdivision_finite` — the new common subdivision theorem replacing the old (false) Sd-refinement approach.

---

## Setup checklist

1. Verify Phases 1-6 build green.
2. Re-read mathematician's §29.

---

## Phase 7 attack outline

### Step 7.1: Main theorem (~40 lines)

```isabelle
theorem geotop_common_subdivision_finite:
  fixes L1 L2 :: "'a::euclidean_space set set"
  assumes hL1: "geotop_is_complex L1"
  assumes hL2: "geotop_is_complex L2"
  assumes hfL1: "finite L1"
  assumes hfL2: "finite L2"
  assumes hpoly: "geotop_polyhedron L1 = geotop_polyhedron L2"
  shows "∃M. geotop_is_subdivision M L1 ∧ geotop_is_subdivision M L2"
proof -
  let ?C = "geotop_overlay_complex L1 L2"

  have hCcell: "geotop_cell_complex ?C"
    using hL1 hL2 hfL1 hfL2
    by (rule geotop_overlay_complex_is_cell_complex)  (* Phase 4 Step 4.12 *)

  obtain M where
    hM_simp: "geotop_is_complex M" and
    hMfin: "finite M" and
    hMC: "geotop_cell_is_subdivision M ?C" and
    hM_induced: "∀A ∈ ?C. A = ⋃ {ρ ∈ M. ρ ⊆ A}"
    using geotop_cell_complex_has_simplicial_subdivision[OF hCcell]
    by blast  (* Phase 5 Step 5.10 *)

  have hML1: "geotop_is_subdivision M L1"
    using hL1 hL2 hfL1 hfL2 hpoly hM_simp hMfin hMC hM_induced
    by (rule geotop_overlay_triangulation_subdivides_left)  (* Phase 6 Step 6.2 *)

  have hML2: "geotop_is_subdivision M L2"
    using hL1 hL2 hfL1 hfL2 hpoly hM_simp hMfin hMC hM_induced
    by (rule geotop_overlay_triangulation_subdivides_right)  (* Phase 6 Step 6.3 *)

  show ?thesis using hML1 hML2 by blast
qed
```

**Risk:** very low — just combining Phases 4, 5, 6.

---

## Validation checklist

- [ ] Theorem compiles with no sorries.
- [ ] Build green at ~25-30s.
- [ ] Sorry count: still 1 (the old false theorem; about to be eliminated in Phase 8).
- [ ] PLAN3_PHASE8.md drafted.

---

## Handoff notes for Phase 8

After Phase 7, we have `geotop_common_subdivision_finite`. Phase 8 reproves `Theorem_GT_1` using this — should be straightforward since `Theorem_GT_1` is essentially the same statement with subdivision-of-K context.
