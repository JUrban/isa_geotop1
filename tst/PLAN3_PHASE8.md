# PLAN3_PHASE8.md — Phase 8: Reprove Theorem_GT_1

**Goal:** Reprove `Theorem_GT_1` (the existing theorem requiring common subdivision of two subdivisions of a common K) using the new `geotop_common_subdivision_finite` from Phase 7. Eliminate the false `_FALSE` theorem and the remaining sorry.

**Status entering Phase 8:** Phases 1-7 complete. Sorry count: 1 (the false theorem).

**Estimated:** ~50 lines of Isar / 30-60 minutes interactive work / 2-3 commits.

**Output deliverables:**
1. New body for `Theorem_GT_1` using `geotop_common_subdivision_finite`.
2. Deletion of `geotop_iterated_Sd_refines_subdivision_FALSE` (or marking as DELETED).
3. Sorry count in basis: **0**.

---

## Setup checklist

1. Verify Phases 1-7 build green.
2. Re-read mathematician's §30.
3. Locate `Theorem_GT_1` (line ~11430 in `b0/GeoTopBase0.thy`).

---

## Phase 8 attack outline

### Step 8.1: Reprove Theorem_GT_1 (~30 lines)

Old proof body (uses the false theorem):

```isabelle
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows "∃L. geotop_is_subdivision L L1 ∧ geotop_is_subdivision L L2"
proof -
  have hK: "geotop_is_complex K" using hL1 unfolding geotop_is_subdivision_def by blast
  obtain m where hm: "geotop_is_subdivision (geotop_iterated_Sd m K) L1"
    using geotop_iterated_Sd_refines_subdivision_FALSE[OF hKfin hL1] by blast  (* uses FALSE *)
  obtain n where hn: "geotop_is_subdivision (geotop_iterated_Sd n K) L2"
    using geotop_iterated_Sd_refines_subdivision_FALSE[OF hKfin hL2] by blast  (* uses FALSE *)
  define N where "N = max m n"
  ... (transitivity argument)
qed
```

New proof body:

```isabelle
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows "∃L. geotop_is_subdivision L L1 ∧ geotop_is_subdivision L L2"
proof -
  have hL1_simp: "geotop_is_complex L1"
    using hL1 unfolding geotop_is_subdivision_def by blast
  have hL2_simp: "geotop_is_complex L2"
    using hL2 unfolding geotop_is_subdivision_def by blast
  have hL1_poly: "geotop_polyhedron L1 = geotop_polyhedron K"
    using hL1 unfolding geotop_is_subdivision_def by blast
  have hL2_poly: "geotop_polyhedron L2 = geotop_polyhedron K"
    using hL2 unfolding geotop_is_subdivision_def by blast
  have hpoly: "geotop_polyhedron L1 = geotop_polyhedron L2"
    using hL1_poly hL2_poly by simp
  have hL1fin: "finite L1"
    by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hL1])
  have hL2fin: "finite L2"
    by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hL2])
  show ?thesis
    using hL1_simp hL2_simp hL1fin hL2fin hpoly
    by (rule geotop_common_subdivision_finite)  (* Phase 7 *)
qed
```

**Risk:** very low. Direct application.

### Step 8.2: Quarantine / delete the false theorem (~5 lines)

The false theorem `geotop_iterated_Sd_refines_subdivision_FALSE` is now unused. Either:
- Delete it entirely.
- Replace its body with `oops` so it's marked as not a theorem.
- Leave with the `sorry` and a comment "DELETED — see geotop_common_subdivision_finite".

**Recommendation:** replace with `oops` or delete entirely. If we keep it sorry'd, the build still succeeds but sorry count remains > 0.

### Step 8.3: Verify sorry-free build (~5 min)

```bash
grep -nE "^[[:space:]]+sorry( |$|\\\\)" b0/GeoTopBase0.thy b/GeoTopBase.thy
```

Expected: 0 results in the basis (b0/GeoTopBase0.thy + b/GeoTopBase.thy).

```bash
/project/bin/isabelle process_theories -d . -l Top0 -O -o quick_and_dirty -f b0/GeoTopBase0.thy
```

Expected: green build.

---

## Order of attack

1. Step 8.1 (~30 min): rewrite Theorem_GT_1 body.
2. Step 8.2 (~10 min): quarantine false theorem.
3. Step 8.3 (~5 min): verify sorry-free.
4. Update `MEMORY.md` and `REPORT.md` to reflect milestone.
5. Commit final state.

---

## Validation checklist

- [ ] Theorem_GT_1 reproved using new theorem.
- [ ] False `_FALSE` theorem deleted or replaced with `oops`.
- [ ] **Sorry count in basis: 0**.
- [ ] Build green at ~25-30s.
- [ ] Downstream §1-§3 proofs in `b/GeoTopBase.thy` still compile (they use Theorem_GT_1, but the statement is unchanged so they should be fine).
- [ ] PLAN3_PHASE8.md marked complete.
- [ ] MEMORY.md updated with milestone.

---

## Handoff notes — what's next

After Phase 8 succeeds, the GeoTop formalization basis is **fully sorry-free**. The downstream §§2-36 sorries (~76 in `GeoTop.thy`) are no longer transitive-recursive sorries — they're genuine local sorries on individual theorems.

The GeoTop project then becomes a "fill-in-the-individual-sorries" exercise rather than blocked by foundational issues.

This is the same milestone PLAN1.md aimed at originally (Phase 3 Phase 1: §1 sorry-free). PLAN3 supersedes the original PLAN1's "iterated Sd" approach with the corrected overlay-cell-complex approach.

---

## Total effort estimate

Phases 1-8: ~900-1200 lines of Isar across ~4-6 weeks of focused interactive sessions.

Per phase:
- Phase 1: ~150-200 lines, 1-2 days.
- Phase 2: ~100-150 lines, 1 day.
- Phase 3: ~80-100 lines, 0.5 day.
- Phase 4: ~150-200 lines, 1-2 days.
- Phase 5: ~200-300 lines, 3-5 days. **Major work.**
- Phase 6: ~100-150 lines, 1 day.
- Phase 7: ~50 lines, 0.5 day.
- Phase 8: ~50 lines, 0.5 day.
