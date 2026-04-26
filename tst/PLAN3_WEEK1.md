# PLAN3 — Week 1: Sd-vertex recursive structure formalization

**Goal:** For τ ∈ Sd^m K (m ≥ 0), establish the recursive structure of V_τ so that subsequent weeks can reason about V_τ via induction on m.

**Estimated:** ~300 lines of Isar / ~1-2 days interactive work / 6-10 commits

**Output deliverables:** 4 named lemmas (W1.1 - W1.4) all FULLY PROVEN.

---

## Setup checklist (first 15 minutes)

1. Open Isabelle/jEdit on `/project/tst/b0/GeoTopBase0.thy`. Verify cached build green.
2. Read commits `b859ecf6` ... `f9601f00` for context (the carrier-map infrastructure).
3. Locate insertion point for new Week 1 lemmas: just **after** `geotop_K_carriers_of_barycenters` (line ~10780, search for `lemma geotop_K_carriers_of_barycenters`) and **before** `geotop_iterated_Sd_simplex_in_K_simplex` (line ~9938 — earlier in file). Probably best place: between lines ~9700 and ~9800, after the K_carrier function definition.
4. Read `geotop_iterated_Sd` and `geotop_is_barycentric_Sd` definitions to understand the recursion structure:

```bash
grep -n "definition geotop_iterated_Sd\|definition geotop_is_barycentric_Sd\|^lemma geotop_bK_elt_simplex_vertices" b0/GeoTopBase0.thy
```

---

## Week 1 attack outline

### W1.1: Sd^0 K = K

```isabelle
lemma geotop_iterated_Sd_zero:
  "geotop_iterated_Sd 0 K = K"
```

**Approach:**
- Look at the definition of `geotop_iterated_Sd` (likely defined recursively `Sd^0 K = K`, `Sd^(n+1) K = Sd (Sd^n K)`).
- One-liner unfold + by simp.

**Risk:** very low (~5 lines).

### W1.2: Sd-simplex vertex extraction (m = 1 case)

```isabelle
lemma geotop_Sd_simplex_vertex_decomp:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hτ: "τ ∈ geotop_iterated_Sd 1 K"
  obtains V c where "finite V" "V ≠ {}"
                and "V = geotop_barycenter ` (set c)"
                and "c ∈ geotop_flags K"
                and "geotop_simplex_vertices τ V"
                and "τ = convex hull V"
```

**Approach:**
- `geotop_iterated_Sd 1 K = Sd K` (one barycentric subdivision).
- An Sd K simplex τ is by definition `geotop_convex_hull (geotop_barycenter ` set c)` for some K-flag c.
- Use `geotop_bK_elt_simplex_vertices` (already proven, line ~4246) to extract V = barycenter ` set c.
- Use `geotop_convex_hull_eq_HOL` to convert geotop_convex_hull to convex hull.

**Risk:** medium (~50 lines). Need to understand exact form of `geotop_iterated_Sd 1 K` and `geotop_is_barycentric_Sd`.

### W1.3: Sd-simplex K-carrier alignment (m = 1 case)

```isabelle
lemma geotop_Sd_simplex_V_in_K_simplex:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hτ: "τ ∈ geotop_iterated_Sd 1 K"
  shows "∃σ_K ∈ K. (∀w ∈ {v. geotop_simplex_vertices τ V ∧ v ∈ V}. w ∈ σ_K)
                  ∧ (τ ⊆ σ_K)"
```

**Approach:**
- Apply W1.2 to extract V = barycenter ` set c, c ∈ geotop_flags K.
- Apply `geotop_chain_simplex_vertices_in_top` (already proven) to get V ⊆ last c.
- last c ∈ K (chain top is in the K-flag set).
- τ ⊆ σ_K via geotop_iterated_Sd_simplex_in_K_simplex (already proven).

**Risk:** low (~30 lines, mostly chaining existing lemmas).

### W1.4: Iterated case (general m)

```isabelle
lemma geotop_iterated_Sd_vertex_in_K_simplex:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hτ: "τ ∈ geotop_iterated_Sd m K"
  shows "∃σ_K ∈ K. τ ⊆ σ_K"
```

This is **essentially** `geotop_iterated_Sd_simplex_in_K_simplex` (already proven, line 9938). Just confirm and reuse.

**Approach:**
- Already proven! Just provide a re-export or thin wrapper if needed.

**Risk:** very low (~5 lines).

### W1.5: K-flag chain extraction (recursive m ≥ 1)

```isabelle
lemma geotop_iterated_Sd_simplex_K_flag_chain:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hm_pos: "0 < m"
  assumes hτ: "τ ∈ geotop_iterated_Sd m K"
  shows "∃σ_K ∈ K. (∀w. (∃V. geotop_simplex_vertices τ V ∧ w ∈ V) ⟶ w ∈ σ_K)
                  ∧ τ ⊆ σ_K"
```

**Approach:**
- Combination of W1.4 (τ ⊆ σ_K) and `geotop_simplex_vertices_subset` (V_τ ⊆ τ).
- Together: V_τ ⊆ τ ⊆ σ_K.

**Risk:** very low (~10 lines).

---

## Order of attack

1. **W1.1** (5 lines, 5 minutes). Quick warm-up.
2. **W1.4** (5 lines, 5 minutes). Just confirm existing lemma, no new proof.
3. **W1.5** (10 lines, 15 minutes). Combine W1.4 with vertex_subset.
4. **W1.2** (50 lines, 60 minutes). Most substantive part. Need to dig into `geotop_iterated_Sd 1 K` definition.
5. **W1.3** (30 lines, 30 minutes). Chains existing lemmas.

Total: ~100 lines, ~2 hours interactive work.

---

## Risk mitigation

- **`geotop_iterated_Sd` definition**: may use `funpow` or recursive cases. Check first 30 minutes; if hard to unfold, may need helper lemma `geotop_iterated_Sd_Suc`.
- **Forward references**: place all new lemmas AFTER `geotop_K_carriers_of_barycenters` (~line 10780). Check that all dependencies (Munkres 14.4, K_carrier function, chain_simplex_vertices_in_top) are defined ABOVE.
- **by100 flakes**: if interactive Isabelle/jEdit can't validate within ~5s, decompose into smaller steps. Use `apply (rule ...)` chains for explicit reasoning.
- **CLAUDE.md sorry-only rule**: write all new lemmas with `sorry` first, get the structure to compile, THEN replace sorries with real proofs in batches of 3-5.

---

## Validation checklist

After Week 1 completes:

- [ ] All 5 lemmas (W1.1 — W1.5) compile with no sorries.
- [ ] Build green at ~22s (no significant slowdown vs baseline).
- [ ] Sorry count in basis still 1 (only h_inter_ne; no new sorries introduced).
- [ ] Each lemma committed separately with descriptive message.
- [ ] PLAN3_WEEK1.md marked complete; PLAN3_WEEK2.md drafted with Week 2 attack outline.

---

## Handoff notes for Week 2

After Week 1:
- W1.1 (Sd^0 K = K) is mechanical.
- W1.2 (vertex decomposition for m=1) is the substantive new content; Week 2 will build on this.
- W1.3-W1.5 chain existing lemmas.
- Together: Week 1 gives the structural fact "for τ ∈ Sd^m K, V_τ ⊆ σ_K for some K-simplex". Week 2 needs to refine this to "V_τ ⊆ σ' for some K'-simplex σ' ⊆ σ_K when mesh < ε".

The KEY observation Week 2 will use: V_τ are barycenters, and barycenters of K-flag chain elements have K-CARRIERS that form a chain (already proven via `geotop_K_carrier_barycenter`). This chain structure is what Week 2 exploits via rel-distance bounds.
