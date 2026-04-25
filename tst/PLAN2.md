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

## REVISED ANALYSIS (after Session N+1 + N+3 work)

Sessions N+1 and N+3 turned out as planned. Session N+2 needs major
revision because the original formulation is too strong:

**Original N+2 statement (too strong):**
> For σ ∈ K and T ⊆ σ convex non-empty with diam T < δ_σ, ∃ σ' ∈ K' with σ' ⊆ σ and T ⊆ σ'.

**Counterexample:** Take K = single 2-simplex σ. K' = a subdivision of σ adding
a vertex m in interior + several new triangles. Take T = small disk centered
on m. Then T is convex, diam < δ for any positive δ, but T spans multiple
K'-simplices around m.

**Correct N+2 (per Munkres):** This must be reformulated to use SD-SPECIFIC
structure of Sd^m K simplices. Their vertices are barycenters of K-flags;
their geometry is specific.

Alternative: directly prove `iterated_Sd_refines_subdivision` without going
through a generic Lebesgue lemma, using:
- Each Sd^m K simplex tau has K-carrier σ_K ∈ K.
- tau's vertices V_T are inside σ_K, forming a chain of barycenters.
- For m large, V_T concentrates near a specific point x_0 ∈ σ_K.
- x_0 has K'-carrier σ'_0 ⊆ σ_K (bridge lemma).
- For m large, ALL of V_T is in σ'_0 (specific calculation using
  bary chain structure).
- Hence tau = conv hull V_T ⊆ σ'_0 (convex).

This bypasses the buggy generic Lebesgue path entirely.

## NEXT SESSION FOCUS

Skip N+2 as originally formulated. Instead:

**Session A**: Prove the "vertices concentrate in K'-simplex" lemma:
For Sd^m K simplex tau with K-carrier σ_K, ∃ m_0 such that for all
m ≥ m_0, tau's vertices V_T ⊆ σ' for some K'-simplex σ' ⊆ σ_K.

**Session B**: Use this to directly close `iterated_Sd_refines_subdivision`,
deleting the buggy h_δ_ex / h_star_to_simplex_del chain.

**Session C**: Verify Theorem_GT_1 builds with no recursive sorries.

This is approximately the same total effort as the original 5-session
plan, but with a different decomposition that avoids the generic-Lebesgue
dead end.

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

## ADDENDUM 2026-04-25 (continued analysis): Session A sub-decomposition

After repeated review, the "vertices concentrate in K'-simplex" lemma
needs explicit decomposition. Here is the sub-strategy.

### Why naive Lebesgue + open star fails

For x near a K'-vertex v inside a K-simplex σ_K, the open star of v in
K' restricted to σ_K is NOT covered by a single K'-simplex containing
v. Multiple K'-simplices share v, and a small simplex τ around v may
have vertices in different ones with no upper bound in K'. The
counterexample is the "small disk on K'-vertex" case.

### Why barycentric-chain structure of Sd^m K rescues this

A vertex of Sd^m K is a barycenter b(σ_0...σ_m) for a chain σ_0 < ... < σ_m
in K (actually m levels deep after m subdivisions). The KEY structural
property: any TWO vertices of an Sd^m K simplex τ correspond to chains
σ^A, σ^B that share a common chain TOP (the K-carrier of τ is determined
by the top of all vertex-chains).

### Sub-claim (Session A.1): chain-tops align

For τ a face of Sd^m K with vertices b_0, ..., b_k, let chain_i be the
K-flag whose barycenter is b_i. The K-carrier of τ is max_i top(chain_i),
where top is the maximum K-simplex in the flag.

### Sub-claim (Session A.2): vertex containment

If x_i ∈ σ_K is a barycenter from chain_i ⊆ σ_K (for all i), then x_i
all share the SAME K-carrier σ_K. Moreover, for m large the chains
chain_i differ only in their top portions, all bounded inside σ_K.

### Sub-claim (Session A.3): K'-carrier match

Given x_i all in σ_K with chain-tops aligned, for m large all x_i have
the SAME K'-carrier σ' ⊆ σ_K. Hence τ = conv hull {x_0, ..., x_k} ⊆ σ'
(by convexity).

### Why this is harder than it looks

Sub-claim A.3 is where the actual analytic work lies. It requires
quantitative control over how Sd-iteration shrinks chains relative to
K' vertex spacing. The standard Munkres argument uses the fact that
mesh(Sd^m K) → 0 (already proven via geotop_mesh_iterated_Sd) plus a
specific Lebesgue number for K' relative to σ_K (a per-simplex quantity).

### Direct alternative: bypass via diameter-ratio recursion

Munkres-style proofs of refinement-by-mesh use a more subtle observation:
for a simplex τ ⊆ K-simplex σ_K, if τ has its MIN vertex (in chain order)
in rel_interior of some K'-simplex σ' ⊆ σ_K, and τ has diameter less
than the rel-distance from rel_interior σ' to its rel_frontier, then
τ ⊆ σ'.

This requires per-K'-simplex rel-distance lower bounds (positive due to
finite K' and compact K'-simplices), which is provable but adds
~150 lines of analytic infrastructure.

### Recommendation

Session A is genuinely deep classical work (~500-800 lines total). It
should be attempted in a fresh focused session with no other competing
work. The current state (sorry at line 9985 with full documentation;
all bridge infrastructure in place) is a stable checkpoint suitable
for handoff or pause.

## NEW INFRASTRUCTURE 2026-04-25 (post-bridge-stabilization session)

A 21-piece carrier-map infrastructure layer has been added on top of
the bridge lemma. All commits green-built. Files: `b0/GeoTopBase0.thy`.

### Carrier-map function

- `geotop_K_carrier K x = THE σ. σ ∈ K ∧ x ∈ rel_interior σ`
- `geotop_K_carrier_eq`: σ witness ⟹ K_carrier = σ
- `geotop_K_carrier_in`: K_carrier ∈ K
- `geotop_K_carrier_rel_interior`: x ∈ rel_interior (K_carrier x)
- `geotop_K_carrier_subdiv_subset`: K'-carrier x ⊆ K-carrier x
- `geotop_K_carrier_contains_point`: x ∈ K_carrier x
- `geotop_K_carrier_in_polyhedron`: K_carrier ⊆ |K|
- `geotop_K_carrier_self_in_rel_interior`: alias for K_carrier_eq
- `geotop_K_carrier_subset_containing_simplex`: x ∈ σ ⟹ K_carrier x ⊆ σ
- `geotop_K_carrier_shared_rel_interior`: same rel_interior ⟹ same carrier
- `geotop_K_carrier_barycenter`: K_carrier (b σ) = σ for σ ∈ K
- `geotop_K_carrier_vertex`: K_carrier v = {v} for v ∈ V(σ), σ ∈ K
- `geotop_K_carrier_chain_combo`: K_carrier of chain-positive-combo = chain top

### Uniqueness facts

- `geotop_carrier_unique`: rel_interior membership determines K-simplex uniquely
- `geotop_complex_polyhedron_point_carrier_unique`: ∃! σ. σ ∈ K ∧ x ∈ rel_interior σ
- `geotop_K'_carrier_in_K_carrier`: bridge in carrier-function form

### Simplex/complex/polyhedron exports

- `geotop_simplex_is_convex`, `_compact`, `_closed`, `_nonempty`
- `geotop_simplex_vertices_subset`, `_obtain_HOL`
- `geotop_simplex_closure_rel_interior`
- `geotop_simplex_rel_interior_nonempty`
- `geotop_finite_subset_simplex_hull_subset`
- Complex-context corollaries for each (`_complex_simplex_*`)
- `geotop_complex_polyhedron_compact`, `_closed`, `_bounded`
- `geotop_subK'_family_finite`

### Stability fix

`geotop_K'_carrier_in_K_simplex` (the bridge) had a 5-fact
by100 simp chain that flaked under load. Decomposed into three
2-fact stages (commit `d9b226f7`).

### How this maps to N+2 reformulation

For an Sd^m K-simplex τ with chain σ_0 ⊊ ... ⊊ σ_p in K:
- Each Sd-vertex b_i = barycenter of some sub-flag of K
- K_carrier(b_i) = chain-top of that sub-flag (via K_carrier_chain_combo)
- For any positive convex-combination interior point x ∈ rel_interior τ,
  K_carrier(x) = max chain-top across positive contributors
- The bridge gives: K'_carrier(x) ⊆ K_carrier(x)
- Refinement claim: for m large, K'_carrier(x) is constant on V_τ

The refinement claim (constancy on V_τ as m → ∞) is the remaining
Sd-vertex-concentration argument. The infrastructure to STATE and
manipulate it is now all in place.
