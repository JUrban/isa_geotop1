# PLAN1 — Close §1 + Intro sorries so §1 can be cached

**Status at time of writing:** 539 total sorries; §1 has 3 sorries (A, B, C below) after my decomposition work; 3 relevant Intro sorries (D, E, F) that §1 depends on via Theorem_GT_1.

## §1 + Intro sorry map (6 sorries)

| # | Location | Content | Difficulty | Dependencies |
| - | -------- | ------- | ---------- | ------------ |
| A | L9160 (§1) | `geotop_broken_line_subarc` polyhedron side | Medium (~100-150 lines) | — |
| B | L9234 (§1) | `geotop_broken_lines_glue_disjoint_endpoints` polyhedron side | Medium (~80-120 lines) | — |
| C | L9295 (§1) | `geotop_broken_line_arc_reduction` cross-arc case | Medium (~150 lines) | **A + B** |
| D | L1945 (Intro) | `geotop_classical_Sd_exists` | Hard (~200-250 lines) | — |
| E | L3084 (Intro) | Lebesgue tightening in refinement lemma | Medium (~80-120 lines) | — |
| F | L3313 (Intro) | `h_f_exists` classical barycentric extension | Hard (~150-200 lines) | — |

## Attack order — Phase 1 then Phases 2-4

### Phase 1 — polyhedral sub-complex infrastructure (closes A, B, enables C)

The shared missing infrastructure: *"a sub-polyhedron built by restricting a 1-complex K to vertices in an interval of the arc-parametrisation is itself a complex"*. Build as standalone lemmas:

1. **`geotop_broken_line_1dim`** — if `B = |K|` is an arc, every simplex of `K` has dim ≤ 1. Proof via HOL's `invariance_of_domain` applied to any putative 2-simplex interior ↪ |K| ≃ [0,1].
2. **`geotop_arc_endpoint_is_vertex`** — a topological endpoint of a broken line's arc is a degree-1 vertex of every witnessing complex. Proof via invariance-of-domain around interior points of an edge.
3. **`geotop_complex_restrict_vertices`** — restricting K to a vertex subset V' that is "graph-connected within K" gives a sub-complex whose polyhedron is the graph-union of V'-incident edges.
4. **`geotop_subpath_polyhedron`** — path_image(subpath s_X s_Y γ) = polyhedron of the sub-complex built from the vertices of K the subpath traverses (possibly after edge subdivision at interior X, Y).

With 1-4, A closes (via 4), B closes (union of two sub-complexes meeting at a shared vertex, K.2 checked by 2), C closes (first-intersection extraction on the 1-complex graph, then apply A and B).

**Phase 1 total effort:** ~300-400 lines of Isar, split into 5-6 helper lemmas. Session-timeout-safe if each helper is a separate top-level lemma.

### Phase 2 — D (classical Sd construction)

Concrete construction per Moise early.tex Def 4.4:
- Define `flag K` = maximal chains of faces in K.
- Barycenter-subdivision: for each flag `σ_0 ⊂ σ_1 ⊂ ... ⊂ σ_n`, take the simplex with vertices `barycenter σ_0, ..., barycenter σ_n`.
- Verify: resulting set is a complex, has K's 0-simplices, satisfies `mesh ≤ (n/(n+1)) · mesh K` (Lemma 4.11).

Cascade: D unblocks `mesh_iterated_Sd_tends_to_zero`, `Theorem_GT_1`, `Theorem_GT_3` transitivity, `hK'_ref` in transport.

### Phase 3 — E (Lebesgue tightening)

Apply HOL's `Lebesgue_number_lemma` to the open cover of `|K'|` by vertex-stars. Extract δ such that any set of diameter < δ sits in a single star. Then tighten "star" to "simplex containing v" via `geotop_vertex_stars_cover` (already proved).

### Phase 4 — F (barycentric extension)

Given iso `φ: V(K) → V(L)`, define `g` on each simplex σ ∈ K by: for `x = Σ α_v v` (bary coords on σ), set `g(x) = Σ α_v φ(v)`. Verify bary-linear on each σ, image in a simplex of L, bijective, inverse also bary-linear.

## Recommendation

**Phase 1 first** gives us a fully sorry-free §1 — the actual caching target. Phases 2-4 close Intro sorries that §1 references through Theorem_GT_1's deeper structure but don't directly block §1's own theorems compiling. With `quick_and_dirty`, §1 is technically cacheable NOW, but Phase 1 gives a "trusted cache".

## Execution rules (from CLAUDE.md)

- Sorry-first: new proof skeletons with `sorry` only, then replace via sledgehammer in batches of 3-5.
- **Only** `by (by100 X)` for new tactics — no bare `by blast`/`by simp`/etc.
- Never collapse Isar have/obtain scaffolds to shrink sorry counts.
- Keep full build under ~30s; cached under ~10s.
- Commit frequently with clear messages.
- Don't run builds in 3× retry loops — retry at most once for known-flaky pre-existing lines.
- If build hits session timeout (> 120s), split the offending proof into separate top-level lemmas so each has its own compilation budget.

## Progress log

Record completions here as they happen:

- [x] Strengthened `geotop_is_broken_line` def with 1-dim witness (e5a4ccc6).
- [~] Phase 1.1: `geotop_complex_subdivide_edge` — VERTEX CASE CLOSED; interior case sorry (df602bd6).
- [x] Phase 1.2: `geotop_complex_subdivide_at` — FULLY PROVED (39c82d2a).
- [x] Phase 1.2b: `geotop_broken_line_finite_witness` — FULLY PROVED via compactE_image (4d826231).
- [x] Phase 1.3: `geotop_broken_line_vertex_at` — FULLY PROVED (finite + vertex).
- [x] Phase 1.B: `glue_disjoint_endpoints` polyhedron — FULLY PROVED structurally (3085cd02, 21f4d9fd).
- [~] Phase 1.C: disjoint sub-case of `arc_reduction` hard case — CLOSED via glue_disjoint (91784d0b); overlap sub-case still sorry.
- [x] Phase 1.C helper `geotop_arc_first_intersection` — FULLY PROVED (commit e8baa6d5). 41-line compactness argument: S = γ -` T ∩ [0,1] nonempty closed bounded, sstar = Inf S ∈ S, minimality via cInf_lower.
- [ ] Phase 1.A: close A (`broken_line_subarc` polyhedron) — still sorry (needs graph sub-complex extraction).
- [ ] Phase 1.C overlap: requires subarc polyhedron (1.A) since the first-intersection argument needs a specific sub-arc construction, not subarc's abstract ∃B'.
- [ ] Phase 2: close D (`classical_Sd_exists`)
- [ ] Phase 3: close E (Lebesgue tightening)
- [ ] Phase 4: close F (`h_f_exists`)

## Session 2026-04-23: first_intersection + Phase 1.1 infrastructure

### Fully proved helpers (this session):

- `geotop_arc_first_intersection` (e8baa6d5) — compactness first-intersection.
- `geotop_subdivide_edge_polyhedron_eq` (3f63ec16) — polyhedron equality.
- `geotop_subdivide_edge_simplexes` (8b8fe06e) — K.0 axiom.
- `geotop_subdivide_edge_locfin` (2404680a) — K.3 axiom (finite K').
- `geotop_subdivide_edge_vertices_in_K` (a4eafd09) — vertex face-closure.

### Skeletons added (sorry with plan):

- `geotop_subdivide_edge_face_closed` (2c4ea14f) — K.1 axiom.
- `geotop_subdivide_edge_inter_face` (ec69299e) — K.2 axiom.

### Phase 1.1 interior assembly (ec69299e):

`geotop_complex_subdivide_edge_interior` now has a fully structured
proof that uses all helpers. Only 1 sub-sorry remains (`hK'_comp`
— fold K.0+K.1+K.2+K.3 into is_complex_def). The face_closed and
inter_face helpers are the two classical-content sorries.

### Structured-proof lesson applied:

Replaced flaky `by (by100 blast)` on 3-4 element set-membership
disjunctions with explicit `UnE` + nested `disjE` applications.
Each step uses `by (by100 simp)` on a singleton-membership claim.
The new `geotop_subdivide_edge_simplexes` proof demonstrates this
robust style — passes on first retry under load.

### Infrastructure built (reusable):

Now stable in GeoTopBase:
- `geotop_arc_first_intersection` — Inf of closed preimage.
- `geotop_subdivide_edge_polyhedron_eq` — polyhedron invariance.
- `geotop_subdivide_edge_simplexes` — K.0.
- `geotop_subdivide_edge_locfin` — K.3 (UNIV).
- `geotop_subdivide_edge_locfin_inherit` — K.3 (inheritance, no finiteness).
- `geotop_subdivide_edge_vertices_in_K` — vertex face-closure.
- `geotop_complex_subdivide_edge_vertex` — vertex case of edge subdivision.
- `geotop_1dim_complex_simp_dim_le_1` — dim bound.
- `geotop_broken_line_finite_witness` — finite witness via compactE_image.
- `geotop_broken_line_vertex_at` — subdivide at any point.
- `geotop_HOL_arc_imp_geotop_is_arc` — reverse arc bridge.
- `geotop_HOL_homeomorphic_imp_top1_homeomorphism_on` — reverse homeomorphism bridge.
- `geotop_continuous_on_imp_top1_continuous_map_on` — continuity bridge.
- `geotop_simplex_diameter_nonneg` — simplex diameter bound.
- `geotop_mesh_norm_nonneg` — mesh non-negative (with finite/diameter hypotheses).

### Session 2026-04-23 continued: CLOSE face_closed (K.1) and singleton_ne_e helpers

Major closure:
- `geotop_subdivide_edge_singleton_ne_e` FULLY PROVED (commit 69ac3d82).
- `geotop_closed_segment_simplex_vertices` FULLY PROVED (8ad86dad).
- `geotop_subdivide_edge_face_closed` (K.1) FULLY PROVED (e4bdecdb).

Phase 1.1 interior hK'_comp now has K.0 ✓, K.1 ✓, K.3 ✓ — only K.2
(inter_face) remains sorry. Also hardened flaky GeoTop line 8770.

**6 real §1+Intro sorries remaining** (was 7):
  - D L1945 `classical_Sd_exists`
  - E L3084 Lebesgue tightening
  - F L3313 `h_f_exists`
  - Phase 1.1 K.2 `inter_face` — 4x4 case analysis (last Phase 1.1 piece)
  - Phase 1.A `subarc` polyhedron
  - Phase 1.C overlap

### Remaining real §1+Intro sorries (was 7, now 6):

Phase 1.1 interior is now FULLY STRUCTURALLY PROVED using 6 helpers
(5 fully proved + 2 skeleton = 7 helpers total). Assembly hK'_comp
is CLOSED. Only K.1 and K.2 content remains as narrow sorries:
  - D (L1945) `classical_Sd_exists`
  - E (L3084) Lebesgue tightening
  - F (L3313) `h_f_exists`
  - Phase 1.1 K.1 (face_closed) — single focused sorry, signature
    strengthened with 1-dim + R distinctness for the core argument
  - Phase 1.1 K.2 (inter_face) — 4x4 case analysis sorry
  - Phase 1.A (subarc polyhedron) — graph sub-complex
  - Phase 1.C overlap — uses first_intersection helper now (all
    structure present, just needs sub-arc construction).

## Final state after this extended session

**GeoTopBase.thy** (Intro + §1): 6 real sorry tactics (= 11 grep-counted due to
comment mentions). These are the 6 classical-content sorries:
  1. L1945 `classical_Sd_exists` — barycentric subdivision construction (D).
  2. L3084 Lebesgue tightening in refinement lemma (E).
  3. L3313 `h_f_exists` barycentric extension (F).
  4. L9076 `subdivide_edge_interior` Phase 1.1.
  5. L9437 `subarc` polyhedron Phase 1.A.
  6. L9759 `arc_reduction` overlap case Phase 1.C.

**GeoTop.thy** (§§2-36): 529 sorries.

**Total: 540 (539 via grep, off-by-one from comment mentions).**

**Build times:**
  - Fresh: GeoTopBase 37s + GeoTop 14s = 51s.
  - Cached: 8-10s.

## Session 2026-04-23 continued: CLOSE K.2 inter_face (full 4×4 case analysis)

**K.2 inter_face FULLY PROVED** via 4 macro-cases + 6 new helper lemmas:

Helpers added:
- `geotop_subdivide_edge_el_inter_er` — ?el ∩ ?er = {R} via library `Int_closed_segment`.
- `geotop_subdivide_edge_v0_notin_er` — v₀ ∉ cs R v₁ (derived from intersection exactness).
- `geotop_subdivide_edge_v1_notin_el` — symmetric.
- `geotop_singleton_is_face_self` — {x} is a face of {x}.
- `geotop_closed_segment_is_face_endpoint` — endpoints are 0-faces of a segment.
- `geotop_closed_segment_is_face_self` — segment is a face of itself.
- `geotop_subdivide_edge_sigma_cap_e_cases` — for σ ∈ K-{e} in 1-dim K, σ∩e ∈ {{},{v₀},{v₁}} via K.2 of K + |V_σ| ≤ 2.

Main proof structure (commits dcf2c38f 58c8e0f7 3626af6c 817e92ee e8c1f548 19bcaa70):
- Old × old: direct K.2 of K.
- Old × new: σ∩e classification + endpoint faces; three of the subcases vacuous.
- New × old: symmetric dual of old × new (duplicated, not extracted).
- New × new: 3×3 disjE enumeration; ?el∩?er={R} closes the tricky pair.

**5 real §1+Intro sorries remaining** (was 6):
  1. L1945 `classical_Sd_exists` (D).
  2. L3084 Lebesgue tightening (E).
  3. L3313 `h_f_exists` (F).
  4. L10918 subarc polyhedron (Phase 1.A).
  5. L11293 arc_reduction overlap (Phase 1.C).

All of Phase 1.1 (`complex_subdivide_edge`) is now STRUCTURALLY + CONTENT-COMPLETE.
Build times unchanged: fresh 51s, cached 8s.

## Session 2026-04-23 continued: Phase 1.A infrastructure

Added reusable helpers for the subarc polyhedron proof (still sorry,
but the pieces needed are now in place):

- `geotop_1dim_simplex_cases` — a 1-dim complex simplex is a singleton
  or a closed_segment between distinct points.
- `geotop_arc_homeomorphism_image` — `arc γ ⟹ ∃h. homeomorphism {0..1}
  (path_image γ) γ h`. Thin wrapper on `homeomorphism_arc`.
- `geotop_complex_subset_is_complex` — a face-closed subset of a
  complex is a complex. General-purpose sub-complex machinery.
- `geotop_complex_restrict_subset_is_complex` — specialisation:
  `{σ ∈ K : σ ⊆ B'}` is automatically face-closed (faces are subsets)
  and hence a complex when K is.
- `geotop_complex_restrict_preserves_1dim` — 1-dim-ness is inherited
  by arbitrary subsets.

With these, the Phase 1.A construction becomes: take K (1-dim complex
with |K| = B), subdivide at X, Y to get K_sub (still 1-dim complex);
then K' = {σ ∈ K_sub : σ ⊆ ?B'} is a 1-dim complex by the helpers.
Remaining gap: |K'| = ?B' (needs γ^{-1}(σ)-is-interval + non-crossing
argument).

**Follow-up:** added `geotop_arc_preimage_is_interval` — for γ an arc
and σ ⊆ path_image γ connected, `{t ∈ [0,1]. γ t ∈ σ}` is a closed
interval. Proof via `homeomorphism_arc` + `is_interval_connected_1`.
This is the key step for Phase 1.A: when σ is a 1-simplex (singleton
or closed segment, both connected), γ^{-1}(σ) is a sub-interval. The
union of these sub-intervals over σ ∈ K equals [0,1] (since |K| = B).
After subdivision at X (=γ(s_X)), Y (=γ(s_Y)), the sub-interval
[s_lo, s_hi] sits at a breakpoint, so every σ's sub-interval is
either entirely in [s_lo, s_hi] or entirely out.

**More follow-up:** strengthened `subdivide_edge`/`subdivide_at` to
expose `K - {e} ⊆ K'` and `∀v. {v} ∈ K ⟶ {v} ∈ K'`. Added
`geotop_complex_subdivide_at_two`: given X, Y ∈ |K|, produces K''
with BOTH {X} ∈ K'' and {Y} ∈ K''. This was essential because
subdividing at X then at Y requires knowing that {X} survives the
second subdivision (which it does — it's a 0-simplex, not an edge).

### Phase 1.A proof sketch (for next session)

With all this infrastructure, the subarc polyhedron proof becomes:
1. Get K witnessing B = |K| (broken_line_finite_witness).
2. `subdivide_at_two K X Y` → K'' with {X}, {Y} ∈ K''.
3. `K' = {σ ∈ K'' : σ ⊆ ?B'}` — a sub-complex by restrict_subset_is_complex.
4. `polyhedron K' ⊆ ?B'`: immediate (σ ⊆ ?B' ⟹ ⋃K' ⊆ ?B').
5. `?B' ⊆ polyhedron K'`: for x ∈ ?B' = γ[s_lo, s_hi], x = γ(t).
   Pick σ ∈ K'' with x ∈ σ. Let [a, b] = γ^{-1}(σ) (via preimage_simplex_is_interval).
   Claim [a, b] ⊆ [s_lo, s_hi]: if s_lo ∈ (a, b), then γ(s_lo) ∈ interior(σ)
   is a vertex of K''; by K.2 applied to {X/Y} and σ, {X/Y} is face of σ,
   hence an endpoint — contradiction. Similarly for s_hi. So [a, b] ⊆ [s_lo, s_hi],
   hence σ = γ[a, b] ⊆ γ[s_lo, s_hi] = ?B', σ ∈ K'.

Estimated proof length: 200-300 Isar lines. Plans to close next session.

### Attempted Phase 1.A proof — lesson learned

First attempt (~473 lines monolithic) hit 120s session timeout. Split
attempt (~140-line preimage_structure helper + main) hit type issue:
`continuous_injective_image_segment_1` requires `f :: 'a ⇒ real`, not
`f :: real ⇒ 'a` as we have for γ.

**Fix for next session:** add a projection-based helper
`geotop_homeomorphism_segment_endpoints`:
`continuous_on [p..q] γ → inj_on γ [p..q] → γ ` [p..q] = closed_segment a b
 → {γ p, γ q} = {a, b}`.
Proof via projection π(x) = inner (b - a) x:
- π ∘ γ : [p, q] → ℝ continuous injective (π injective on closed_segment a b).
- Apply continuous_injective_image_segment_1 to π ∘ γ.
- Get {π(γ p), π(γ q)} = {π a, π b}.
- π injective on σ gives {γ p, γ q} = {a, b}.
Then Phase 1.A proof becomes ~200 lines (single monolithic fits under 120s).

### 2026-04-24 continuation: PHASE 1.A FULLY PROVED!

Helper stack built and all proven (15 new fully-proven lemmas in Phase 1.A
infrastructure, spanning from K.2 closure through Phase 1.A):

- `geotop_inner_diff_inj_on_closed_segment` — projection π(x) = (b-a)·x
  is injective on closed_segment a b for a ≠ b.
- `geotop_inner_diff_image_closed_segment` — π image of segment equals
  real closed_segment of endpoint projections.
- `geotop_homeomorphism_segment_endpoints` — {γ p, γ q} = {a, b} when γ
  is a cts bijection {p..q} → closed_segment a b. Uses the two projection
  helpers + `continuous_injective_image_segment_1`.
- `geotop_arc_1simplex_preimage_structure` — combines preimage_interval
  + endpoints: for σ = closed_segment a b 1-simplex, γ^{-1}(σ) = {p..q}
  with {γ p, γ q} = {a, b}.
- `geotop_subarc_polyhedron` (**Phase 1.A MAIN**) — γ([s_lo, s_hi]) is
  the polyhedron of a 1-dim sub-complex. ~310-line proof via subdivide_at_two
  + restrict + case analysis on σ (singleton vs 1-simplex) + interval
  containment via vertex-in-1simplex endpoint contradiction.

Phase 1.A sorry at geotop_broken_line_subarc closed via direct application.

**4 real §1+Intro sorries remaining** (was 5):
  1. L1945 `classical_Sd_exists` (D).
  2. L3084 Lebesgue tightening (E).
  3. L3313 `h_f_exists` (F).
  4. L12434 arc_reduction overlap (Phase 1.C).

Phase 1.C is NOW UNBLOCKED (was blocked on 1.A). Plan: use first_intersection
helper + geotop_subarc_polyhedron directly.

### 2026-04-24 continued: PHASE 1.C FULLY PROVED!

Added 2 helpers + closed sorry:
- `geotop_broken_line_compact` / `_closed` — broken lines are compact/closed
  (finite union of compact convex hulls).
- Phase 1.C overlap fully proved inline (~220 lines): extract γ_1, γ_2 arcs;
  apply `geotop_arc_first_intersection` with T = B_2' to get sstar, R;
  build B_1'' = γ_1([0, sstar]) and B_2'' = γ_2([sstar_2, 1]) via
  `geotop_subarc_polyhedron`; B_1'' ∩ B_2'' = {R} by minimality of sstar;
  glue via `geotop_broken_lines_glue_disjoint_endpoints`.

**PHASE 1 IS NOW FULLY CLOSED.** 3 real sorries remaining (all Intro classical):
  1. L1945 `classical_Sd_exists` (D) — barycentric subdivision construction.
  2. L3084 Lebesgue tightening (E).
  3. L3313 `h_f_exists` (F) — barycentric extension.

§1 (broken lines, arcs, sub-arcs, arc reduction) is CACHEABLE as sorry-free
content. All Phase 1.x theorems fully proven.

## Attack notes for D, E, F (remaining Intro sorries)

### E (L3084) — Lebesgue tightening
The stated h\<delta>prop is TECHNICALLY UNPROVABLE in the empty K case
(conclusion requires ∃v ∈ vertices(K') = ∅). Even in the non-empty case,
the "S connected → S in single σ" step requires rel_interior disjointness
in a simplicial complex, which is not in HOL-Analysis directly.

Options for closing E:
- (a) Restructure surrounding proof to handle K = {} case separately;
  modify h\<delta>prop to require S non-empty + connected; prove rel_int
  disjointness via face_of_disjoint_rel_interior (from Polytope library)
  after bridging geotop_is_face to HOL's face_of (itself non-trivial for
  combinatorial ≠ affine-independence simplices).
- (b) Derive the weaker claim "∃σ ∈ K'. τ ⊆ σ" directly for simplex τ
  via a different classical argument (e.g., barycenter of τ in some σ +
  convexity + closed star containment), avoiding rel_interior.

Both options are substantive (~100+ line proofs with multiple lemmas).

### D (L1945) — classical_Sd_exists (barycentric subdivision)
Construction per Moise early.tex Def 4.4: bK = all flags of face-barycenters.
Verification requires: bK is a complex, polyhedron bK = polyhedron K,
mesh bK ≤ n/(n+1)·mesh K. ~200-250 lines.

### F (L3313) — h_f_exists (barycentric extension)
Extend vertex-iso φ to PL-homeomorphism between polyhedra. Via barycentric
coordinates: for x = Σα_v v on σ, set g(x) = Σα_v φ(v). Verify bijective
+ linear on each simplex. ~150-200 lines.

All 3 require substantive classical PL-topology formalization.

## Session 2026-04-23/24 grand total

- **K.2 inter_face** FULLY PROVED (major Phase 1.1 piece).
- **Phase 1.A subarc polyhedron** FULLY PROVED (310-line main + 7+ helpers).
- **Phase 1.C arc_reduction overlap** FULLY PROVED (220-line inline).
- **GeoTopBase: 6 → 3 real sorries** (4 grep sorries + 3 text comments).
- ~53 commits spanning K.2 closure + Phase 1.A infrastructure + Phase 1.C.
- Build stable: 7-9s cached, ~65s fresh.
- Phase 1 (§1 content) is NOW SORRY-FREE and cacheable.
- Remaining blockers for full GeoTopBase cache: D, E, F (all Intro classical).

**Key reusable helpers added this session** (all fully proven):
- `geotop_arc_homeomorphism_image`
- `geotop_1dim_simplex_cases`
- `geotop_arc_preimage_is_interval`, `_simplex_is_interval`
- `geotop_complex_subset_is_complex`
- `geotop_complex_restrict_subset_is_complex`, `_preserves_1dim`
- `geotop_complex_subdivide_at_two` (strengthened `subdivide_edge/at`)
- `geotop_1dim_vertex_in_simplex_is_face`, `_is_endpoint`
- `geotop_inner_diff_inj_on_closed_segment`, `_image_closed_segment`
- `geotop_homeomorphism_segment_endpoints`
- `geotop_arc_1simplex_preimage_structure`
- `geotop_subarc_polyhedron` (Phase 1.A main)
- `geotop_broken_line_compact`, `_closed`

All of Phase 1 content is now SORRY-FREE and ready to cache.

### Post-Phase-1: E-support infrastructure added

Two foundational bridge helpers to enable E (Lebesgue tightening) attack:
- `geotop_complex_inter_face_HOL` — (σ∩τ) is a HOL face_of σ for σ,τ∈K
  with σ∩τ ≠ {}. Extracted from the existing open_star_complement proof
  pattern (used `face_of_convex_hull_affine_independent`).
- `geotop_complex_rel_interior_disjoint_distinct` — for σ ≠ τ in K
  (complex), rel_interior σ ∩ rel_interior τ = {}. Derived via
  face_of_disjoint_rel_interior on the three cases: σ ∩ τ = ∅; σ ⊆ τ;
  neither ⊆ the other.

These enable attacking E via:
1. For convex T ⊆ open_star K v, pick x_0 ∈ T with x_0 ∈ rel_int σ_0.
2. Define path γ(t) = (1-t)x_0 + t y for y ∈ T. γ continuous, image ⊆ T.
3. S_0 = {t | γ(t) ∈ σ_0} is closed in [0,1]. s* = sup S_0. Show s* = 1.
4. Needs: continuity of "which rel_int" switching + rel_interior openness
   in affine hull — still requires more work than I can complete here.

Next session should focus on: either (a) finishing E with the new
rel_interior disjointness infrastructure via a detailed "sup of bounded
set" argument, (b) tackling D (barycentric subdivision) which is more
independent of E, or (c) F (barycentric extension).

Additional E-bridge helper added:
- `geotop_complex_point_in_unique_rel_interior` — each x in |K|
  belongs to rel_interior of exactly one σ ∈ K. Immediate from
  rel_interior_disjoint_distinct.

### Correct classical argument for E (documented for future work)

**Claim**: For T convex ⊆ open_star K v with T ≠ {}, ∃σ ∈ K. v ∈ σ ∧ T ⊆ σ.

**Proof sketch** (from Moise early.tex):
1. open_star K v = ⋃{rel_int τ : τ ∈ K, v ∈ τ}, a finite union in a
   finite complex K' = K.
2. For x, y ∈ T in rel_int σ_1, rel_int σ_2 (possibly equal), the
   segment xy must stay in open_star K v (T convex).
3. If σ_1 ≠ σ_2: at generic interior point of xy, z = (1-t)x + ty is
   NOT in affine hull σ_1 ∪ affine hull σ_2 (when σ_1 ⊄ σ_2 and vv).
   Hence z ∉ σ_1 ∪ σ_2. z must be in some σ_3 ∋ v with different
   affine hull. But iterating this around the segment gives infinitely
   many simplices for a finite complex — contradiction.
4. So all points of T are in one σ (call it σ_0 = the unique simplex
   with x ∈ rel_int σ_0 for some x ∈ T). Then T ⊆ σ_0.

Formalising step 3 in Isabelle requires: (a) `affine_independent_span_eq_aff_hull`
equivalents, (b) finite complex ⟹ finite relevant σ's bound, (c) the
"segment leaves finite union" classical lemma. ~100 additional lines.

With all three pieces, E closes in ~150 lines total using existing
rel_interior disjointness helpers.

### Session discovery: by100 method text limitation

by100 wraps `Method.text_closure`, which apparently doesn't accept compound
method text like `(simp add: foo)` or `(metis lemma1 lemma2)`. Only bare
method names work: `by (by100 simp)`, `by (by100 blast)`, `by (by100 auto)`,
`by (by100 metis)`, etc. For specific lemma injections, use `using foo` +
bare by100 method.

Workaround patterns:
- `using facts by (by100 simp)` — puts facts in simp's `using` rules.
- Pre-derive intermediate facts by explicit rule application:
  `have h: "..." by (rule specific_lemma[OF ...])` (outside by100).
- For algebra: use `by (by100 argo)` for real-arithmetic-closed conjectures.

This constraint shaped the endpoint-matching helper proof style — all
algebraic manipulations had to use explicit rule application + by100 simp.

## Session split DONE (commit 384f54d0)

Split GeoTop.thy into:
  - `b/GeoTopBase.thy` (Intro + §1, 11 sorries, builds 37s fresh).
  - `GeoTop.thy` (§§2-36, 529 sorries, builds 14s fresh on cached GeoTopBase).
  - ROOT has two sessions, each with its own 120s timeout.

Benefits realized:
  - Cached iteration on §§2+ only rebuilds those (not the 10,000-line §1 prefix).
  - Per-theory 120s budget lets Phase 1.1 interior's structured proof fit.

Phase 1.1 interior now has structured proof (K.0 derived from 1-dim + simplex_dim;
1-dim via 4-case explicit disjE; |K'|=|K| via Un_closed_segment; only K.1/K.2/K.3
verification remains as one focused sorry - commit 0886697b).

## Remaining work to close §1 sorry-free

Core infrastructure sorries that unlock everything:
1. `geotop_complex_subdivide_edge` interior case (~80 lines, concrete construction).
2. `geotop_complex_subdivide_at` (trivial given 1.1 — case-split on dim of σ containing R).
3. `geotop_broken_line_finite_witness` (~30 lines, compactness + K.3 subcover).
4. Finiteness preservation in `vertex_at` (~15 lines, inspect subdivide_at's structure).

Then A and C become tractable:
- A: subarc polyhedron requires graph-theoretic sub-complex extraction (~80 lines).
- C: arc_reduction cross-arc first-intersection (~100 lines).

## Split-proof safety template

To avoid session-timeout when proofs get long, put each step as its own top-level lemma:

```isabelle
(* NOT this — compounds by100 cost *)
lemma big:
  ...
proof -
  have h1: ... by ...  (* 40 lines *)
  have h2: ... by ...  (* 40 lines *)
  show ?thesis using h1 h2 by ...
qed

(* Use this instead *)
lemma step1:
  ...
proof - ... qed

lemma step2:
  ...
proof - ... qed

lemma big:
  using step1 step2 by ...
```

Each lemma gets its own 120s slice of the session budget.
