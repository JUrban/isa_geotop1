# PLAN3.md — Closing the final basis sorry (h_inter_ne)

## Status

**As of 2026-04-26 (commit `f9601f00`):**

The basis (`b0/GeoTopBase0.thy` + `b/GeoTopBase.thy`) has **exactly 1 sorry**, on a TRUE statement. Build green at 21-22s. All other infrastructure is in place.

The single remaining sorry is `h_inter_ne` inside `geotop_iterated_Sd_refines_subdivision`:

```isabelle
have h_inter_ne: "(\<Inter>w\<in>V\<^sub>\<tau>. geotop_open_star K' w) \<noteq> {}"
  sorry
```

Where:
- `τ ∈ Sd^m₀ K` (an iterated barycentric subdivision simplex)
- `m₀` chosen via mesh shrinkage so `mesh(Sd^m₀ K) < ε`
- `ε` is a Lebesgue number for the K'-vertex-star open cover of |K|
- `V_τ` is the simplex vertex set of τ
- `V_τ ⊆ open_star(v, K')` for some K'-vertex v (already established)

The claim is TRUE (Munkres §15-16 classical refinement). Its proof requires ~200-400 lines of Isar synthesizing Sd-vertex recursive structure with carrier-map machinery.

## Infrastructure already in place

The session of 2026-04-26 (commits `b859ecf6` through `f9601f00`) built up extensive supporting infrastructure:

**K-carrier machinery (~14 exports):**
- `geotop_K_carrier` definition (THE σ ∈ K with x ∈ rel_interior σ)
- `geotop_K_carrier_eq`, `_in`, `_rel_interior`
- `geotop_K_carrier_subdiv_subset`: K'-carrier ⊆ K-carrier
- `geotop_K_carrier_contains_point`, `_in_polyhedron`
- `geotop_K_carrier_self_in_rel_interior`
- `geotop_K_carrier_subset_containing_simplex` (smallest enclosing)
- `geotop_K_carrier_shared_rel_interior` (locally constant)
- `geotop_K_carrier_barycenter`: K_carrier(b σ) = σ
- `geotop_K_carrier_vertex`: K_carrier v = {v} for v ∈ V(σ)
- `geotop_K_carrier_chain_combo` (the chain-positive-combo K-carrier law)
- `geotop_carrier_unique`
- `geotop_complex_polyhedron_point_carrier_unique`
- `geotop_K'_carrier_in_K_carrier` (functional bridge)

**Munkres Lemma 14.4 biconditional:**
- `geotop_open_star_inter_to_simplex` (⟸ direction)
- `geotop_simplex_to_open_star_inter` (⟹ direction)
- `geotop_open_star_inter_simplex_iff` (named theorem)
- `geotop_open_star_inter_carrier` (carrier-form characterization)
- `geotop_open_star_eq_carrier_contains_vertex`

**Closed star + complex/simplex/polyhedron exports:**
- `geotop_closed_star` definition with `_subset_polyhedron`, `_contains_vertex`, `_closed`
- `geotop_simplex_is_convex`, `_compact`, `_closed`, `_nonempty`
- `geotop_simplex_obtain_HOL` (combined obtains-form)
- `geotop_simplex_vertices_subset`
- `geotop_simplex_closure_rel_interior` (rel_interior dense in σ)
- `geotop_simplex_rel_interior_nonempty`
- `geotop_complex_polyhedron_compact/closed/bounded`
- `geotop_finite_subset_simplex_hull_subset`
- `geotop_subK'_family_finite`
- `geotop_chain_simplex_vertices_in_top` (V_τ ⊆ chain top)
- `geotop_chain_barycenters_in_top`
- `geotop_K_carriers_of_barycenters` (K_carrier ∘ barycenter = id on K)

**Surgical restructure of `iterated_Sd_refines_subdivision`** (commits `7232b44a`, `4cd1cc7f`, `9ac596c4`, `f6db0a3a`, `b00db318`, `20e24b7e`):
- Deleted ~340 lines of buggy h_δ_ex / h_star_to_simplex_del chain (FALSE statements)
- Replaced with sorry-only Isar 6-step structure
- 5 of 6 sub-steps **FULLY PROVEN**:
  - Step 1: Lebesgue ε for K'-vertex stars (✓)
  - Step 2: mesh shrinkage to m₀ (✓)
  - Step 3: τ ⊆ open_star(v, K') for some K'-vertex v (✓)
  - Step 4: vertex extraction V_τ (✓)
  - Step 5: Munkres 14.4 ⟸ in K' (✓)
  - Step 6: convexity τ = conv hull V_τ ⊆ σ' (✓)
- Step 4(b) (the deep analytic claim h_inter_ne) is the SOLE remaining sorry

## What's blocked

`geotop_iterated_Sd_refines_subdivision` is the sole gate to:
- `Theorem_GT_1` (Moise's first theorem: common subdivision)
- All §§2-36 content downstream of Theorem_GT_1

After h_inter_ne discharges, the basis is sorry-free. `Theorem_GT_1` builds. Downstream content unblocks.

## Continuation-mode limitations encountered

The session tried multiple times to discharge h_inter_ne but ran into:

1. **Build cycle latency**: each iteration (write → submit → wait 21s+ → debug) takes 5-10 cycles per substantive change.
2. **Load-induced by100 flakes**: ~1/3 of builds hit 100ms timeout on unrelated lines (load varies during run).
3. **Forward-reference debugging**: each typo / position error costs a full 21s retry.
4. **No interactive editor**: cannot use Isabelle/jEdit's instant validation; every change is a full file rebuild.

For the analytic synthesis (~200-400 lines), this overhead makes continuation-mode infeasible. Estimate: 100+ continuation cycles, mostly waiting on builds.

## Proposed multi-session plan

### Week 1: Sd-vertex recursive structure formalization (~300 lines)

**Goal**: For τ ∈ Sd^m K, extract the recursive K-flag chain underlying V_τ. Each Sd-vertex w ∈ V_τ traces back to a K-simplex w_K via barycenter recursion.

**Concrete deliverables:**
- `geotop_Sd_iter_simplex_vertex_K_simplex`: for τ ∈ Sd^m K with vertex w ∈ V_τ, the recursive barycenter unwinding gives w = barycenter of some K-simplex (or recursively a Sd^{m-1} K-simplex). Specifically:
  - For m = 0: V_τ ⊆ V(K) (trivial — Sd^0 K = K).
  - For m = 1: V_τ = barycenter ` (set c) for some K-flag c (already proven via `geotop_bK_elt_simplex_vertices`).
  - For m ≥ 2: V_τ = barycenter ` (set c) where c is a Sd^{m-1} K-flag. Each barycenter recursively unwinds.
- `geotop_Sd_iter_vertex_to_K_carrier`: for w ∈ V_τ (any iterate), K_carrier_K w is a specific K-simplex (the chain top after recursive unwinding).
- `geotop_Sd_iter_V_τ_in_K_simplex`: V_τ ⊆ σ_K for some σ_K ∈ K (the recursive chain top).

**Risk**: high — requires careful inductive structure on m.

### Week 2: core analytic step — rel-distance + chain alignment (~200-300 lines)

**Goal**: prove the core claim "for τ ⊆ σ_K with diam τ < δ_τ (specific positive bound), V_τ ⊆ σ' for one K'-simplex σ' ⊆ σ_K".

**Concrete deliverables:**
- `geotop_simplex_rel_dist_bound`: for σ' ⊆ σ_K with σ' ∈ K' AND σ' a face of σ_K (sub-simplex with vertices in V(σ_K), not arbitrary subset), the rel-distance dist({x}, σ_K \ σ') > 0 for x ∈ rel_interior σ' — this circumvents the original counterexample by using the FACE structure.
- `geotop_Sd_simplex_K_face_alignment`: for τ ∈ Sd^m K with V_τ in σ_K, the recursive Sd-flag chain ensures V_τ are in a SPECIFIC K'-FACE-OF-σ_K-SIMPLEX (not arbitrary K'-simplex). Uses Sd-vertex barycenter structure + face axiom of K'.
- Combine: V_τ all in one K'-face-of-σ_K-simplex σ', via mesh < δ.

**Risk**: high — requires the precise Munkres §16 argument. The KEY observation is that Sd-simplices DO end up in K'-FACES of σ_K (not just any K'-simplex), making the rel-distance bound work.

### Week 3: discharge h_inter_ne (~50 lines)

**Goal**: with Weeks 1+2 in hand, prove h_inter_ne in a clean ~50-line proof.

**Concrete deliverable:**
```isabelle
have h_inter_ne: "(⋂w∈V_τ. geotop_open_star K' w) ≠ {}"
proof -
  obtain σ' where hσ': "σ' ∈ K'" and hVσ': "V_τ ⊆ σ'"
    using week2_lemma[OF ...] by ...
  show ?thesis
    using geotop_simplex_to_open_star_inter[OF hK'comp hσ' hVσ'] by ...
qed
```

**Risk**: low if Weeks 1+2 succeed.

### Week 4: verify and clean up (~50 lines)

**Goal**: verify `Theorem_GT_1` fully closes; downstream §§2-36 sorries no longer transitively-recursive.

**Concrete deliverables:**
- Run full build, verify 0 basis sorries.
- Update PLAN2.md, MEMORY.md to reflect milestone.
- Update REPORT_*.md with final status.

**Risk**: low.

## Recommended workflow

For each week:
1. **Fresh focused session** with full context handoff (read this PLAN3.md + relevant commits).
2. **Interactive Isabelle/jEdit** for rapid 1-2s build feedback during iteration.
3. **Commit on every successful sub-lemma** to preserve incremental progress.
4. **Drop back to continuation-mode** only for status updates and small touch-ups.

## Critical context preservation

If switching to a different operator:
- Read `PLAN2.md` ADDENDUM for the buggy original h_δ_ex chain analysis (corrected by surgical restructure).
- Read this PLAN3.md for the structured 4-week plan.
- Inspect commit `f9601f00` for the current state.
- The 28+ carrier-map exports listed above are the substantive infrastructure; do not duplicate.
- **Never attempt to discharge h_inter_ne with the OLD h_δ_ex generic-convex approach** — that's the bug we already fixed (small-disk-on-K'-vertex counterexample).

## Estimated total effort

~600-800 lines of new Isar across 4 weeks. Each week is independently checkpoint-able. Sorry count target: **0 in basis** (currently 1).
