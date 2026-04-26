# REPORT — Literal refinement theorem for iterated barycentric subdivision

## What we are formalizing

We are formalizing parts of E. E. Moise, *Geometric Topology in Dimensions 2 and 3* (Springer GTM 47, 1977), in Isabelle/HOL. Moise's Theorem 1 (page 5 of Introduction) states:

> **Theorem 1 (Moise).** Every two subdivisions of the same complex have a common subdivision.

Moise does not prove this in the text; it is treated as background, with the proof presumably from a standard algebraic topology reference (Munkres' *Elements of Algebraic Topology* is the most common).

Our formalization follows Moise's approach: prove Theorem 1 via the auxiliary fact that some iterated barycentric subdivision of K refines any given subdivision of K. Specifically:

## Key auxiliary theorem we cannot find a clean classical proof for

### Statement

Let `K, K'` be (Euclidean) simplicial complexes in ℝⁿ. Assume `K` is finite, and `K'` is a subdivision of `K` (in Munkres' sense — see definitions below). Define the iterated barycentric subdivision `Sdᵐ K` recursively: `Sd⁰ K = K`, `Sdᵐ⁺¹ K = Sd(Sdᵐ K)`.

**Claim (the literal refinement theorem):**
There exists `m ∈ ℕ` such that `Sdᵐ K` is a subdivision of `K'` (in Munkres' sense).

Equivalently, by Munkres' Definition 15.1.1:

> ∃ m. ∀τ ∈ Sdᵐ K. ∃ σ' ∈ K'. τ ⊆ σ'   (LITERAL set-containment)

### Definitions used

(Following Munkres, *Elements of Algebraic Topology*, §15.)

- A **(Euclidean) complex** `K` is a collection of simplices in ℝⁿ such that:
  (K.0) Each `σ ∈ K` is a (closed) Euclidean simplex.
  (K.1) Every face of every `σ ∈ K` is in `K`.
  (K.2) For every `σ, τ ∈ K`, if `σ ∩ τ ≠ ∅` then `σ ∩ τ` is a face of each.
  (K.3) Every `σ ∈ K` has an open neighborhood meeting only finitely many simplices of `K`.

- The **polyhedron** `|K|` is `⋃ K`, with the subspace topology from ℝⁿ.

- A complex `K'` is a **subdivision** of `K` if:
  (S.1) Each simplex of `K'` is contained in a simplex of `K` (literal set-containment).
  (S.2) Each simplex of `K` equals the union of finitely many simplices of `K'`.

- The **first barycentric subdivision** `Sd K` is constructed by recursively starring the `p`-skeleton from the barycenters of `(p+1)`-simplices (Munkres Definition, p. 85). Equivalently (Munkres Lemma 15.3, p. 85), `Sd K` consists of all simplices of the form `[σ̂₁ σ̂₂ ... σ̂ₙ]` where `σ₁ > σ₂ > ... > σₙ` is a strictly-descending chain of simplices of `K` and `σ̂` denotes the barycenter of `σ`.

- The **mesh** `‖K‖` is the supremum of diameters of simplices in `K`.

### What is in Munkres §15-17

Munkres provides:

1. **Theorem 15.4 (Mesh shrinkage):** Given a finite complex `K`, a metric for `|K|`, and `ε > 0`, there is `N` such that each simplex of `Sdᴺ K` has diameter less than `ε`. Specifically `‖Sdᴺ K‖ ≤ (n/(n+1))ᴺ · ‖K‖` where `n = dim K`.

2. **Theorem 16.1 (Finite Simplicial Approximation Theorem):** Let `K, L` be complexes with `K` finite. Given a continuous map `h : |K| → |L|`, there is `N` such that `h` has a simplicial approximation `f : Sdᴺ K → L`.

   Here `f : Sdᴺ K → L` is a SIMPLICIAL MAP — it sends `Sdᴺ K`-vertices to `L`-vertices, and each simplex `τ ∈ Sdᴺ K` is mapped to a simplex `f(τ) ∈ L`.

3. **Lemma 17.1:** If `K'` is a subdivision of `K`, then the identity `i : |K| → |K|` has a simplicial approximation `g : K' → K`.

### Why these are insufficient for our claim

The literal refinement claim says **τ ⊆ σ'** as sets in ℝⁿ.

The simplicial approximation theorem says **`f(τ) ⊆ L`** (image is a simplex).

These are different statements:

- For `h = id : |K| → |K'|` (when `K'` is a subdivision of `K`, so `|K| = |K'|`), Theorem 16.1 gives `f : Sdᴺ K → K'` simplicial, with the **star condition**: `St(v, Sdᴺ K) ⊆ St(f(v), K')` for each vertex `v` of `Sdᴺ K`.

- For `τ ∈ Sdᴺ K` with vertices `V_τ`, the simplicial map gives `f(V_τ) ⊆ V(σ')` for some `σ' ∈ K'`. Each `x ∈ τ` lies in `⋂_{v ∈ V_τ} St(f(v), K')`. By Munkres' Lemma 14.4, this intersection is non-empty iff `f(V_τ)` spans a `K'`-simplex (which it does, since `f` is simplicial).

- But this places each `x` in **some** `K'`-simplex `τ'_x` containing `σ'` as a face. The simplex `τ'_x` may differ for different `x ∈ τ`.

In particular, **τ ⊆ τ'** for a single fixed `τ' ∈ K'` is **not** a direct consequence of the simplicial approximation theorem.

### Counterexample to a simpler formulation we tried

Define for `σ' ∈ K'` with `σ' ⊆ σ_K` (some `K`-simplex) and `x ∈ rel-interior σ'`:
> `δ(x, σ', σ_K) = dist(x, σ_K \ σ')` or `dist(x, σ_K \ rel-interior σ')`.

We hoped that for `τ ⊆ σ_K` with `x ∈ τ ∩ rel-interior σ'` and `diam τ < δ`, we'd have `τ ⊆ σ'`.

**Counterexample:** Take `σ_K` = closed triangle `[a, b, c]`, `σ'` = closed edge `[a, b]` (a face of `σ_K`). Take `x = midpoint of edge ab ∈ rel-interior σ'`. Points in `σ_K \ σ'` (the triangle interior) can be made arbitrarily close to `x` by approaching `x` from inside the triangle. So `dist(x, σ_K \ σ') = 0`. The same holds for `dist(x, σ_K \ rel-interior σ')`.

So a per-point rel-distance bound on `(x, σ', σ_K)` does **not** give a positive lower bound, even when `σ'` is a face of `σ_K`.

### Counterexample to a "K'-carrier nesting" formulation we tried

For `τ ∈ Sd K` (the first barycentric subdivision) with `Sd`-vertices `V_τ = barycenter(set c)` for some `K`-flag `c = [σ₀ ⊊ σ₁ ⊊ ... ⊊ σₚ]`, the `K`-carriers of `V_τ` are exactly the chain elements `{σ₀, ..., σₚ}`.

We hoped that for `K'` a subdivision of `K` and `K'-carrier` of each `bary(σᵢ)` defined as the unique `K'`-simplex `σ'ᵢ` with `bary(σᵢ) ∈ rel-interior σ'ᵢ`, the `σ'ᵢ` would be **nested** (`σ'₀ ⊆ σ'₁ ⊆ ... ⊆ σ'ₚ`), so taking `σ'ₚ` would give `V_τ ⊆ σ'ₚ`.

**Counterexample:** Take `K` = closed segment `[a, b]`. `K`-flag `c = [{a}, [a, b]]`. `Sd K`-vertices = `{a, midpoint(ab)}`. Take `K'` to be a subdivision of `[a, b]` into many sub-segments: `[a, p₁], [p₁, p₂], ..., [pₙ, b]` where `p_{n/2} = midpoint(ab)`. Then:
- `K'-carrier(a) = {a}` (a `K'`-vertex).
- `K'-carrier(midpoint(ab)) = {p_{n/2}} = {midpoint(ab)}` (also a `K'`-vertex).

These are **not nested**: neither `{a} ⊆ {midpoint(ab)}` nor vice versa.

So `Sd`-vertex `K'-carriers` are not nested in general.

## Concrete downstream uses requiring LITERAL refinement

The literal refinement theorem is required to prove **Moise's Theorem 1** (common subdivision exists), which is then used heavily for **piecewise-linear (PL) homeomorphism transport** arguments. Specifically:

### Use 1: Theorem 1 (common subdivision) — internal use

```isabelle
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows "∃L. geotop_is_subdivision L L1 ∧ geotop_is_subdivision L L2"
```

Proof outline (in our formalization):
- Apply literal refinement to get `m, n` with `Sdᵐ K` a subdivision of `L1`, `Sdⁿ K` a subdivision of `L2`.
- Take `N = max m n`. By monotonicity (`Sd` preserves subdivision-of relation), `Sdᴺ K` is a subdivision of `Sdᵐ K` and of `Sdⁿ K`, hence (transitivity) of `L1` and `L2`.

The literal refinement is the only nontrivial input.

### Use 2: PL-isomorphism transport

Given a PL homeomorphism `f : |L| → |K|` where `L₁` is a subdivision of `L`, we want to construct a subdivision `L₃` of `L₁` such that `f` is simplicial on each simplex of `L₃` (refining the original PL structure). Sketch from `b/GeoTopBase.thy` line 4098:

```isabelle
(* (4) Apply Theorem_GT_1 to get a common subdivision K_3 of fL_1 and K_1
       (uses finite K hypothesis). *)
obtain K₃ where hK₃_fL₁: "geotop_is_subdivision K₃ fL₁"
             and hK₃_K₁:  "geotop_is_subdivision K₃ K₁"
  using Theorem_GT_1[OF hKfin hfL₁_sub hK₁K] by ...

(* (5) Pull K_3 back through f to get L_3 < L_1 with f : L_3 ≅ K_3. *)
define L₃ where "L₃ = (λσ. inv_into (geotop_polyhedron L) f ` σ) ` K₃"
```

This step requires that for each `σ ∈ K₃` we have `σ ⊆ τ` for some `τ ∈ K₁` **literally**, so that `f⁻¹(σ) ⊆ f⁻¹(τ)` lands inside a single simplex of `L` where `f⁻¹` is well-defined and PL.

If we only had simplicial-approximation-style refinement (`σ` mapped to some `K₁`-simplex via a simplicial approximation map), then `f⁻¹(σ)` would not directly land in a single `L`-simplex, breaking the construction.

### Use 3: Repeated PL-isomorphism transport for §§2-3 of Moise

The PL transport argument (Use 2) is the workhorse for many §§2-3 theorems (Moise's text). It is invoked tens of times. Each invocation requires literal refinement (set-containment) for the inverse-image construction to be well-defined.

### Summary of downstream use

Without literal refinement:
- `Theorem_GT_1` cannot be proved.
- All §§2-3 PL-isomorphism transport arguments fail.
- The §1 (Theorem 1) Moise statement is unproven.

## Specific question for a mathematician

We need a classical proof of the following statement:

> **Theorem (LITERAL Sd refinement):** Let `K` be a finite Euclidean simplicial complex in ℝⁿ. Let `K'` be a subdivision of `K`. Then there exists `N ∈ ℕ` such that for every simplex `τ ∈ Sdᴺ K`, there is some simplex `σ' ∈ K'` with `τ ⊆ σ'` (set-containment).

Equivalently: `Sdᴺ K` is a subdivision of `K'` (in Munkres' sense, Definition 15.1).

### What we have

1. Mesh shrinkage: `Sdᴺ K` has all simplices of arbitrarily small diameter as `N → ∞`.
2. Lebesgue number for the cover of `|K| = |K'|` by `K'`-vertex open stars: there's `λ > 0` such that every set of diameter `< λ` lies in some open star `St(v, K')`.
3. Combining 1+2: for `N` large, every `τ ∈ Sdᴺ K` lies in some `St(v, K')` for some `K'`-vertex `v`.
4. Munkres' Lemma 14.4 / iff-form: For any non-empty finite `V ⊆ |K'|`, `∩_{w ∈ V} St(w, K') ≠ ∅` iff there's some `K'`-simplex containing all of `V`.

### What we need

A direct proof that `τ ⊆ σ'` for some `σ' ∈ K'`, NOT just `τ ⊆ St(v, K')`.

### Possible approaches we've considered (and their issues)

**Approach A (per-point rel-distance):** failed counterexample above.

**Approach B (`K'`-carrier nesting):** failed counterexample above.

**Approach C (Sd-vertex barycentric structure):** the `Sd`-vertices are barycenters of `K`-flag chains. Possibly the chain structure forces `K'`-carriers into a specific configuration. We have not been able to make this precise.

**Approach D (apply Munkres' Theorem 16.1 simplicial approximation, then refine):** the simplicial approximation `f : Sdᴺ K → K'` provides set-membership in stars, but not literal set-containment of simplices.

### What we'd like

Either:
- **(I)** A clean classical proof of the LITERAL refinement statement (perhaps in Spanier *Algebraic Topology*, Hatcher *Algebraic Topology*, or another reference we haven't checked).
- **(II)** Confirmation that the LITERAL refinement is genuinely classical folklore that requires careful elementary geometry of barycentric subdivisions, and a sketch of the precise argument.
- **(III)** Counterexample showing that the LITERAL refinement is FALSE in general, so that our formalization needs to be restructured to use a weaker simplicial-approximation-style notion of subdivision.

Outcome (III) would be unexpected — we believe LITERAL refinement is true, since standard textbooks treat "common subdivision" as routine — but we cannot rule it out.

## Current state of formalization

- The basis (`b0/GeoTopBase0.thy` + `b/GeoTopBase.thy`) has **1 sorry** on the LITERAL refinement claim, structured into a 6-step Isar proof:
  - Steps 1, 2, 3, 4, 5, 6 are FULLY PROVEN using existing infrastructure.
  - Step 4 (the deep analytic step) is a single `sorry` on:
    > `(⋂_{w ∈ V_τ} open_star(w, K')) ≠ ∅`
    where `V_τ` is the vertex set of an `Sdᵐ K` simplex `τ ⊆ open_star(v, K')` for some `K'`-vertex `v` (the Lebesgue conclusion).

- 28+ supporting lemmas have been formalized:
  - K-carrier function (the unique K-simplex with x in rel-interior)
  - Munkres 14.4 biconditional (open-star intersection ↔ vertex set spans K-simplex)
  - Closed star, chain-vertex containment, etc.

- Build green at ~22 seconds.

## Files

- `b0/GeoTopBase0.thy`: foundational layer with the sorry'd theorem (`geotop_iterated_Sd_refines_subdivision`, around line 11000) and all infrastructure.
- `b/GeoTopBase.thy`: §1 layer using Theorem_GT_1 in PL transport.
- `GeoTop.thy`: §§2-36 layer using §1 results.
- `PLAN3.md`, `PLAN3_WEEK1.md`, `PLAN3_WEEK2.md`: plans documenting the attack and the dead-ends.

If you have a clean proof or reference, please share, with as much rigor as possible (a sketch should at least pinpoint what additional structure on `Sd^N K` and `K'` is being used — e.g., specific properties of barycentric subdivision, geometric inequalities, or a different formulation of the refinement claim).
