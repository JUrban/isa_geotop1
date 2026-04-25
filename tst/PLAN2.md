# PLAN2.md — Closing the iterated_Sd_refines_subdivision sorry

## Problem statement

A single sorry remains in `b0/GeoTopBase0.thy` line 9681, inside
`h_star_to_simplex_del`. This sorry transitively blocks:

- `iterated_Sd_refines_subdivision` (Moise Lemma 4.17)
- `Theorem_GT_1` (Moise's first theorem: common subdivision)
- Most downstream §§2-36 content

The previous attempt used `geotop_convex_in_complex_in_simplex`, which
was provably FALSE as stated. That bug has been corrected (commit
`4fd5d4b3`): the lemma now has a TRUE strong hypothesis and is fully
proven; the false claim has been moved to a transparent sorry in
`h_star_to_simplex_del`.

## Goal

Replace the entire `h_δ_ex` / `h_star_to_simplex_del` chain with a
correct Munkres-style argument using the K-carrier infrastructure
(`geotop_complex_polyhedron_point_carrier`,
`geotop_iterated_Sd_simplex_in_K_simplex`,
`geotop_subdivision_simplex_in_parent`) added in the prior session.

After completion, sorry count in `b0/GeoTopBase0.thy` drops to **0**.

## Five-session plan

### Session N+1: subdivision covers simplex (~150 lines)

**Target lemma** `geotop_subdivision_covers_simplex`:
```
fixes K K' :: "'a::euclidean_space set set"
assumes hsub: "geotop_is_subdivision K' K"
assumes h\<sigma>: "\<sigma> \<in> K"
shows "\<sigma> = \<Union> {\<sigma>' \<in> K'. \<sigma>' \<subseteq> \<sigma>}"
```

This is the missing structural property of subdivisions: every K-simplex
is the union of K'-simplices that are entirely contained in it.

**Approach (a)** — derive from existing `geotop_is_subdivision`:

Inclusion `⊇` is trivial.

For `⊆`: take `x ∈ σ`. Show ∃ σ' ∈ K' with `σ' ⊆ σ ∧ x ∈ σ'`.

Sub-argument:
1. By `geotop_complex_polyhedron_point_carrier` applied to K':
   there's a unique K'-carrier `σ'_x ∈ K'` with `x ∈ rel_interior σ'_x`.
2. By `geotop_subdivision_simplex_in_parent`: `σ'_x ⊆ θ` for some `θ ∈ K`.
3. By `geotop_complex_polyhedron_point_carrier` applied to K:
   there's a unique K-carrier `τ_x ∈ K` with `x ∈ rel_interior τ_x`.
4. By `geotop_complex_rel_interior_imp_subset` applied to K:
   `x ∈ rel_interior τ_x ∧ x ∈ σ ⟹ τ_x ⊆ σ`.
5. By `geotop_complex_rel_interior_imp_subset` applied to K:
   `x ∈ rel_interior τ_x ∧ x ∈ θ ⟹ τ_x ⊆ θ`.
6. Need a bridge: `σ'_x ⊆ τ_x` (the K-carrier of x).
   - σ'_x has x ∈ rel_interior. τ_x has x ∈ rel_interior in K.
   - σ'_x ⊆ θ. τ_x ⊆ θ.
   - σ'_x is the K'-carrier; smallest K' simplex with x in rel_interior.
   - Need: σ'_x ⊆ τ_x.
   - Strategy: rel_interior σ'_x ⊆ τ_x (since x's neighborhood in
     aff hull σ'_x is in rel_interior σ'_x, and locally in τ_x).

**Approach (b)** — strengthen `geotop_is_subdivision` definition:

Add to the definition:
```
\<and> (\<forall>\<sigma>\<in>K. \<sigma> = \<Union> {\<sigma>' \<in> K'. \<sigma>' \<subseteq> \<sigma>})
```

Then re-audit:
- `geotop_is_subdivision_refl`: trivially holds for K' = K.
- `geotop_Sd_is_subdivision`: needs proof of covering for the SD construction.
- `geotop_iterated_Sd_is_subdivision`: should follow by induction.
- `geotop_is_subdivision_trans`: needs lemma chaining.
- `geotop_subdivision_of_finite_is_finite`: unaffected.

Recommendation: try (a) first. If the σ'_x ⊆ τ_x bridge proof gets
genuinely stuck after careful effort, fall back to (b).

### Session N+2: per-K-simplex Lebesgue lemma (~150 lines)

**Target lemma** `geotop_subdivision_lebesgue_per_simplex`:
```
fixes K K' :: "'a::euclidean_space set set"
assumes hsub: "geotop_is_subdivision K' K"
assumes hKfin: "finite K'"
assumes h\<sigma>: "\<sigma> \<in> K"
shows "\<exists>\<delta>>0. \<forall>T. T \<subseteq> \<sigma> \<longrightarrow> T \<noteq> {} \<longrightarrow>
                geotop_diameter (\<lambda>x y. norm (x-y)) T < \<delta>
                \<longrightarrow> (\<exists>\<sigma>'\<in>K'. \<sigma>' \<subseteq> \<sigma> \<and> T \<subseteq> \<sigma>')"
```

**Approach**:
1. σ compact (already proven via `compact_convex_hull` + finite V).
2. {σ' ∈ K' : σ' ⊆ σ} is finite (subset of finite K').
3. By Lemma 1, this finite family covers σ.
4. Key insight: in σ's RELATIVE topology (subspace topology),
   the sub-complex {σ' ∈ K' : σ' ⊆ σ} forms a simplicial complex on σ.
5. Build an open cover of σ in subspace topology: open stars of K'-vertices
   inside σ. Apply HOL's `Lebesgue_number_lemma` to this open cover.
6. δ_σ is the Lebesgue number; T with diam < δ_σ fits in some open star;
   need to bridge from "fits in open star" to "fits in single K' simplex".

Subtlety: Step 6 needs an ANALOGUE of the convex_in_complex argument
INSIDE σ, where σ is a single simplex. Since σ is a simplex (convex), the
local topology is well-behaved.

May need a sub-lemma: "convex T ⊆ σ_simplex with T ⊆ open_star inside σ
⟹ T ⊆ single K'-simplex in σ". This is provable because σ is itself a
simplex, so the open stars in σ behave like cones from K'-vertices.

### Session N+3: uniform Lebesgue δ over K (~50 lines)

**Target lemma** `geotop_subdivision_lebesgue_uniform`:
```
fixes K K' :: "'a::euclidean_space set set"
assumes hsub: "geotop_is_subdivision K' K"
assumes hKfin: "finite K"
assumes hK'fin: "finite K'"
shows "\<exists>\<delta>>0. \<forall>\<sigma>\<in>K. \<forall>T. T \<subseteq> \<sigma> \<longrightarrow> T \<noteq> {} \<longrightarrow>
                geotop_diameter (\<lambda>x y. norm (x-y)) T < \<delta>
                \<longrightarrow> (\<exists>\<sigma>'\<in>K'. \<sigma>' \<subseteq> \<sigma> \<and> T \<subseteq> \<sigma>')"
```

**Approach**: For each σ ∈ K, get δ_σ from Lemma 2. Take δ = Min over
finite K of δ_σ. Each δ_σ > 0, finite Min preserves positivity, gives
δ > 0.

### Session N+4: restructure iterated_Sd_refines_subdivision (~100 lines)

**Approach**:

Replace the body of `iterated_Sd_refines_subdivision` with:

```
proof -
  obtain δ where hδpos: "0 < δ" and hδprop: ...
    using geotop_subdivision_lebesgue_uniform[OF hsub hKfin hK'fin] by blast
  obtain m where hm_mesh: "geotop_mesh ... (Sd^m K) < δ"
    using geotop_mesh_iterated_Sd_tends_to_zero[...] by blast
  
  have hSdm_in_K': "∀τ ∈ Sd^m K. ∃σ' ∈ K'. τ ⊆ σ'"
  proof
    fix τ assume hτ: "τ ∈ Sd^m K"
    obtain σ_K where hσ_K: "σ_K ∈ K" and hτσ_K: "τ ⊆ σ_K"
      by (rule geotop_iterated_Sd_simplex_in_K_simplex[OF ...])
    have hτ_diam: "diam τ < δ"
      using hm_mesh hτ by ...
    have hτ_ne: "τ ≠ {}" using ...  (* τ is a simplex, nonempty *)
    obtain σ' where hσ': "σ' ∈ K'" and hσ'_sub: "σ' ⊆ σ_K" and hτσ': "τ ⊆ σ'"
      using hδprop hσ_K hτσ_K hτ_ne hτ_diam by blast
    show "∃σ' ∈ K'. τ ⊆ σ'" using hσ' hτσ' by blast
  qed
  
  (* Conclude: Sd^m K refines K'; combined with |Sd^m K| = |K| = |K'|,
     get geotop_is_subdivision (Sd^m K) K'. *)
  ...
qed
```

Delete `h_δ_ex` and `h_star_to_simplex_del` (and the WARNING block)
once iterated_Sd_refines_subdivision is restructured. Verify the build
remains green and no other usage breaks.

### Session N+5: verification & cleanup (~50 lines)

1. Run full build, confirm all sessions still build green.
2. Verify `Theorem_GT_1` now properly builds (check no transitive sorry).
3. Confirm sorry count in `b0/GeoTopBase0.thy` is 0.
4. Update `PLAN1.md` to mark this milestone complete.
5. Update `MEMORY.md` to remove the "buggy lemma" entry and add the
   completion entry.
6. Commit final state with message `Theorem_GT_1 fully closed`.

## Risk register

| Risk | Mitigation |
|---|---|
| Lemma 1 approach (a) gets stuck on σ'_x ⊆ τ_x bridge | Fall back to approach (b): strengthen subdivision def. |
| Strengthened subdivision def breaks `geotop_Sd_is_subdivision` | Re-prove with new clause (~50 lines added work). |
| Per-K-simplex Lebesgue Step 6 bridge harder than expected | Try alternative: use Lebesgue with diff cover (e.g., balls) |
| Build flakes during long-running session | Keep `-o threads=1` for stable timing; commit incrementally. |
| Memory bloat from accumulated 30 000+ lines | Use cached layered build; only `b0/` needs rebuild. |

## Concrete file targets

- New lemmas added to `b0/GeoTopBase0.thy` (foundational layer).
- Restructure `iterated_Sd_refines_subdivision` in same file.
- No changes expected to `b/GeoTopBase.thy` or `GeoTop.thy` (those
  layers consume `Theorem_GT_1` transitively).

## Estimated total

~500 lines of new proof, 5 sessions of ~2 hours each, build cycles
of ~2 minutes per iteration with `-o threads=1`. Sorry count goal: **0
in `b0/GeoTopBase0.thy`** (currently 1).

## Why this fixes the no-recursive-sorries goal

After completion:
- `iterated_Sd_refines_subdivision` is fully closed.
- `Theorem_GT_1` is fully closed (all dependencies discharged).
- Downstream §§2-36 theorems that depend on `Theorem_GT_1` no longer
  have a recursive-sorry blocker.
- The §§2-36 sorries that remain (currently 76) are genuine local
  content, not transitive blockers from the foundational layer.

The single sorry currently blocking would have made any downstream
proof using `Theorem_GT_1` recursive-sorry. After this plan's
completion, that path is clear.
