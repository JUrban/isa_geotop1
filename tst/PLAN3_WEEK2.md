# PLAN3 — Week 2: Core analytic step (rel-distance + chain alignment)

**Goal:** For τ ∈ Sd^m K with mesh(Sd^m K) sufficiently small, V_τ ⊆ σ' for SOME K'-simplex σ' ⊆ σ_K (the chain top from W1.5).

**Status entering Week 2:** Week 1 complete (commit `2e6a29ae`). Sorry count: 1 (h_inter_ne).

**Estimated:** ~200-300 lines of Isar / 3-5 days interactive work / 8-12 commits.

**Output deliverable:** ONE major lemma `geotop_Sd_simplex_in_K'_simplex` plus 3-5 supporting lemmas — all FULLY PROVEN.

---

## Setup checklist (first 15 minutes)

1. Open Isabelle/jEdit on `/project/tst/b0/GeoTopBase0.thy`.
2. Read commits `e216195e` ... `2e6a29ae` (Week 1 work) for context.
3. Locate insertion point: just **after** `geotop_iterated_Sd_simplex_V_in_K_simplex` (W1.5, line ~9985 — search for it).
4. Read the existing infrastructure pointers:

```bash
grep -n "^lemma geotop_K_carriers_of_barycenters\|^lemma geotop_K_carrier_barycenter\|^lemma geotop_K'_carrier_in_K_simplex\|^lemma geotop_subdivision_covers_simplex\|^lemma geotop_chain_simplex_vertices_in_top" b0/GeoTopBase0.thy
```

5. Re-read PLAN3.md and PLAN3_WEEK1.md to refresh the overall plan.

## ⚠ CRITICAL FINDING (2026-04-26 fresh-session setup)

**Setup analysis revealed W2.1 as stated is unprovable via rel-distance.**

Counterexample: σ_K = triangle [a,b,c], σ' = edge [a,b] (a FACE of σ_K, V_σ' = {a,b} ⊆ V_σ_K = {a,b,c}). Take x = midpoint of [a,b] ∈ rel_interior σ'. Points in σ_K \ σ' (triangle interior) can be arbitrarily close to x. So dist(x, σ_K \ σ') = 0. Same for σ_K \ rel_interior σ'.

**Conclusion:** σ_K \ σ' (or \ rel_interior σ') is NOT closed for σ' a face of σ_K when dim σ' < dim σ_K. The rel-distance approach fundamentally cannot work this way.

**Implication for Week 2 plan:** the Munkres §16 argument must use a DIFFERENT analytic technique. The W2.1 + W2.3 structure as drafted is unworkable.

## Revised approach (Munkres §16 "open star" argument)

The classical proof does NOT use rel-distance bounds. Instead:

1. Lebesgue ε for K'-vertex-star cover (already proven in `iterated_Sd_refines_subdivision`).
2. For τ ⊆ open_star(v, K') (one K'-vertex v), each w ∈ V_τ has v ∈ V(K'-carrier(w)).
3. **Key new claim**: for τ a Sd-simplex (V_τ are barycenters of a K-flag chain), the K'-carriers σ'_i = K'-carrier(barycenter σ_i) for i = 0..p (chain) all contain v, AND they are NESTED: σ'_0 ⊆ σ'_1 ⊆ ... ⊆ σ'_p.

The nesting claim is the actual deep fact. It comes from:
- σ'_i ⊆ σ_i ⊆ σ_p (chain).
- v ∈ σ'_i for each i (from open_star).
- σ'_i ∩ σ'_p contains v, hence non-empty. By K.2 axiom, σ'_i ∩ σ'_p is a face of both.
- For σ'_i ⊆ σ'_p, we need σ'_i = σ'_i ∩ σ'_p, i.e., σ'_p ⊇ σ'_i.

The "σ'_p ⊇ σ'_i" claim requires σ'_p to be the K'-CARRIER of barycenter σ_p, which has DIMENSION = dim σ_p (since barycenter σ_p is in rel_interior σ_p, which is "deepest" in σ_p). The dim hierarchy might give σ'_i face of σ'_p.

**This is still a non-trivial claim.** Will need careful argument.

## Revised W2 plan

- **W2.1 (REVISED)**: K'-carrier dimension = K-carrier dimension when point in rel_interior of K-simplex (~80 lines). For x ∈ rel_interior σ_K, the K'-carrier σ'_x has same dim as σ_K (or related dim relationship).
- **W2.2**: K-flag chain elements form a face-chain in K (~60 lines). Same as before — uses face axiom.
- **W2.3 (REVISED)**: K'-carriers σ'_i along the K-flag chain are nested (~80 lines). The deep analytic claim.
- **W2.4**: Discharge h_inter_ne (~50 lines). With nested K'-carriers, σ'_p contains all V_τ, giving Munkres 14.4 ⟹ result.

## Mathematical correctness check

Before proceeding with W2.1 revised, need to verify the nesting claim itself by hand on a small example. The fresh session should START by working a 2D example:

K = single triangle [a,b,c]. K' = some specific subdivision. For an Sd^1 K-simplex τ with K-flag c = [{a}, [a,b]] (a chain), V_τ = {barycenter {a}, barycenter [a,b]} = {a, midpoint ab}.

K'-carriers:
- K'-carrier(a) = some K'-simplex with a in its rel_interior. Since {a} ∈ K' (subdivision preserves K-vertices), K'-carrier(a) = {a}.
- K'-carrier(midpoint ab) = some K'-simplex with midpoint ab in its rel_interior. Depends on K' structure.

For nesting: {a} ⊆ K'-carrier(midpoint ab)? This requires the K'-simplex containing midpoint ab in rel_interior to also contain a. Since a is on the boundary of K'-carrier(midpoint ab) (assuming the K'-simplex extends to include endpoint a), this is plausible.

But for a K' that subdivides edge ab into many segments, K'-carrier(midpoint ab) might be a tiny segment NOT containing a. Then {a} ⊄ K'-carrier(midpoint ab), and the nesting claim FAILS.

**This suggests the nesting claim is actually FALSE in general.** Need to think harder.

## Revised conclusion

The classical Munkres §16 argument is more subtle than direct nesting. Possible approaches:

1. Use ITERATION m large enough that ALL Sd^m K-vertices fall into the SAME K'-simplex. This requires a quantitative argument about how Sd-iteration "concentrates" vertices.

2. Use a more elaborate carrier-chain argument that doesn't require literal nesting but exploits Sd-flag-chain refinement.

3. Use Munkres' §16.4 direct subdivision-mapping argument (different proof path).

Given the difficulty, Week 2 may need to expand to a 2-3 week effort, with W2 being preparatory and the actual h_inter_ne discharge happening in W3.

Continuing investigation is required before code is written.

---

## Week 2 attack outline

### W2.1: Per-K-simplex rel-distance lemma (~80 lines)

**Statement:**
```isabelle
lemma geotop_K'_simplex_rel_distance_bound:
  fixes K K' :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hK': "geotop_is_complex K'"
  assumes hsub: "geotop_is_subdivision K' K"
  assumes hKfin: "finite K"
  assumes hK'fin: "finite K'"
  assumes hσK: "σ_K ∈ K"
  assumes hσ': "σ' ∈ K'"
  assumes hσ'_face: "σ' ⊆ σ_K ∧ (∃W. geotop_simplex_vertices σ_K W ∧ V_σ' ⊆ W)"
                     (* σ' is a face of σ_K — specifically, V_σ' ⊆ V_σ_K *)
  shows "∀x ∈ rel_interior σ'. ∃ρ::real > 0.
            ∀y ∈ σ_K. dist x y < ρ ⟶ y ∈ σ'"
```

**Approach:**
The KEY analytic insight: when σ' is a FACE of σ_K (V_σ' ⊆ V_σ_K), then σ_K \ σ' is closed (since σ' is the convex hull of a vertex subset). The rel-distance approach works in this case.

Why this avoids the disk-on-vertex counterexample: that counterexample had σ' = K'-vertex inside σ_K's interior — σ' was NOT a face of σ_K. Here we restrict to genuine faces.

Sub-claims:
- `σ_K \ σ'` is closed: σ' = conv hull V_σ' ⊆ σ_K, σ_K \ σ' = σ_K ∩ (-σ') = σ_K ∩ closure of (interior σ_K \ σ') ... need careful argument.
- For x ∈ rel_interior σ', dist(x, σ_K \ σ') > 0 (compact-disjoint-closed argument).
- Take ρ = dist(x, σ_K \ σ').

**Risk:** medium-high. Need to establish σ_K \ σ' closed for σ' a FACE of σ_K. Standard but careful.

### W2.2: Sd-flag chain top is a K-FACE not just sub-K-simplex (~60 lines)

**Statement:**
```isabelle
lemma geotop_Sd_chain_K_carriers_face_chain:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hτ: "τ ∈ geotop_iterated_Sd 1 K"
  shows "∃c. c ∈ geotop_flags K ∧
              τ = geotop_convex_hull (geotop_barycenter ` set c) ∧
              (∀i j. i < length c ∧ j < length c ∧ i ≤ j
                       ⟶ c ! i ⊆ c ! j ∧
                          (∃W_i W_j. geotop_simplex_vertices (c ! i) W_i ∧
                                      geotop_simplex_vertices (c ! j) W_j ∧
                                      W_i ⊆ W_j))"
```

**Approach:**
The K-flag c has elements σ_0 ⊊ σ_1 ⊊ ... ⊊ σ_p in K. By complex face axiom, σ_i ⊊ σ_j (both in K, σ_i ⊊ σ_j non-empty intersection) implies σ_i is a FACE of σ_j (V(σ_i) ⊆ V(σ_j)).

This is a critical "lift" from "σ_i ⊊ σ_j" (subset) to "V(σ_i) ⊆ V(σ_j)" (vertex subset).

Use `geotop_complex_inter_face_HOL` or similar.

**Risk:** medium. The face axiom of K is strong enough to give this.

### W2.3: K'-carriers of V_τ form a sub-chain of K-carriers (~50 lines)

**Statement:**
```isabelle
lemma geotop_Sd_V_τ_K'_carrier_chain:
  fixes K K' :: "'a::euclidean_space set set"
  assumes ... (K, K' complexes, K' subdivision of K, K finite)
  assumes hτ: "τ ∈ geotop_iterated_Sd 1 K"
  shows "∃c ∈ geotop_flags K. ∃σ' ∈ K'.
           σ' ⊆ last c ∧ (V_σ' is a K'-vertex face of last c) ∧
           geotop_barycenter ` set c ⊆ σ'"
```

**Approach:**
This is the actual Sd-vertex-concentration claim restricted to m=1.

For τ ∈ Sd^1 K with V_τ = barycenter ` set c (W1.2), the K-carriers are elements of c (chain). For each σ_i ∈ c, K'-carrier(barycenter σ_i) ⊆ σ_i (bridge).

The σ_i form a face-chain in K (W2.2). Within σ_p (chain top), the K'-simplices σ'_i = K'-carrier(barycenter σ_i) are... claim: σ'_p ⊇ σ'_0, σ'_1, ..., σ'_(p-1) (i.e., the highest K'-carrier contains all the others, when V are face-aligned).

Wait — this requires careful argument. Let me think:
- barycenter σ_i ∈ rel_interior σ_i ⊆ σ_i ⊆ σ_p (chain).
- K'-carrier(barycenter σ_i) ⊆ σ_i ⊆ σ_p.
- The K'-carriers are K'-simplices ⊆ σ_p.

Why would σ'_p contain all σ'_i? It's the K'-simplex with barycenter σ_p in its rel_interior, which is "deep inside" σ_p. The other barycenters are in faces σ_i ⊊ σ_p, on the boundary of σ_p in some sense.

This requires the K'-simplices to be "compatible" with the K-face structure of σ_p. Specifically, σ'_p should be a TOP-DIM K'-simplex within σ_p, and σ'_i for i < p should be K'-FACES of σ'_p.

This is the deep analytical claim — true by Munkres §16 but requires precise formalization.

**Risk:** HIGH. May need additional sub-lemmas about K' subdivision structure aligned with K-faces.

### W2.4: Combine W2.1-W2.3 to discharge h_inter_ne (~50 lines)

**Statement:**
```isabelle
have h_inter_ne_proof: "(⋂w∈V_τ. geotop_open_star K' w) ≠ {}"
  using W2.3 + carrier-form characterization (geotop_open_star_inter_carrier)
  ...
```

**Approach:**
W2.3 gives σ' ∈ K' with V_τ ⊆ σ'. By Munkres 14.4 ⟹ in K' (`geotop_simplex_to_open_star_inter`), the open-star intersection over V_τ is non-empty.

Discharge h_inter_ne in `geotop_iterated_Sd_refines_subdivision`.

**Risk:** low.

### W2.5 (optional): Generalize to Sd^m K for m > 1 (~30 lines)

If only the m=1 case is proven by W2.1-W2.4, the iterated case may need a separate inductive argument. Or: any subdivision K' of K satisfies the refinement claim, so by Sd^1 K being a subdivision of K, Sd^1 K refines K' for all K' subdivisions of Sd^1 K. Need to think about this carefully.

If iterated_Sd_refines_subdivision can be specialized to m=1, this case may be sufficient.

---

## Order of attack

1. **W2.1** (rel-distance bound for FACE σ' ⊆ σ_K) — 60-80 minutes. Most mechanical of the analytic lemmas.
2. **W2.2** (chain → face-chain via face axiom) — 45 minutes. Uses existing complex axioms.
3. **W2.3** (K'-carriers form sub-chain) — 90-120 minutes. The HARD analytic step.
4. **W2.4** (discharge h_inter_ne) — 30 minutes. Should be straightforward given W2.3.
5. **W2.5** (generalize to Sd^m if needed) — 30 minutes.

Total: ~5-7 hours interactive work spread over 3-5 days.

---

## Risk mitigation

- **W2.3 is the bottleneck.** If the "K'-carriers form sub-chain" claim doesn't hold cleanly, we may need to break W2.3 into sub-cases (e.g., based on whether σ' is a top-dim K'-simplex in σ_p or a face).
- **Forward references**: place W2.x lemmas in dependency order. W2.1 (no dependencies) → W2.2 (uses face axiom) → W2.3 (uses W2.1 + W2.2) → W2.4 (uses W2.3).
- **Type class compatibility**: euclidean_space throughout for closed/compact arguments.
- **by100 flakes**: use `apply (rule ...)` style for explicit step-by-step reasoning when blast/auto times out.

---

## Validation checklist

After Week 2 completes:

- [ ] All 4-5 lemmas (W2.1 — W2.4 [+ W2.5]) compile with no sorries.
- [ ] h_inter_ne discharged inside `geotop_iterated_Sd_refines_subdivision`.
- [ ] **Sorry count in basis: 0** (was 1 entering Week 2).
- [ ] Build green at ~22-25s.
- [ ] Each lemma committed separately with descriptive message.
- [ ] PLAN3_WEEK2.md marked complete; PLAN3_WEEK3.md becomes essentially "verification only" since h_inter_ne is gone.

---

## Handoff notes for Week 3

After Week 2 successful completion:
- The basis is **fully sorry-free**.
- `Theorem_GT_1` (common subdivision theorem) is now provable end-to-end.
- Week 3 work consists of: verify full build green, downstream §§2-36 proofs no longer transitive-sorry.
- Week 4 becomes verification + cleanup + REPORT writing.

Net effect: Weeks 3 and 4 may compress to ~2-3 days total if Week 2 succeeds cleanly.

---

## Critical mathematical insight (for the operator)

The reason W2.1 is restricted to σ' a FACE of σ_K (V_σ' ⊆ V_σ_K) and not arbitrary K'-simplex:

**Counterexample to the general statement** (from PLAN2 ADDENDUM):
Take K = single 2-simplex, K' = subdivision adding interior vertex m + 6 sub-triangles. σ' = {m} (a 0-simplex of K' inside σ_K's interior). σ' is NOT a face of σ_K (m is not a K-vertex). σ_K \ {m} = open disk minus a point, NOT closed. dist(m, σ_K \ {m}) = 0.

**The fix**: Sd-vertices are barycenters of K-simplices, and their K-CARRIERS are face-chain elements (W2.2). The K'-carriers σ'_i ⊆ σ_i (chain element), so σ'_i are sub-K'-simplices of K-FACES of σ_K. The face structure is preserved.

**Munkres §16 essential idea**: Sd-simplices are "aligned" with K-faces via the chain structure. Subdivisions K' that don't preserve this face-alignment (like adding a new interior vertex m) are STILL OK — because Sd^m K simplices for m large have V_τ K-carriers that nest into the K-face structure, and the K'-simplices σ'_i preserve this nesting via the bridge.

The hard part of W2.3: making "K'-simplices preserve face nesting" precise.
