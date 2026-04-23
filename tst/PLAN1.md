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

## Session 2026-04-23: first_intersection closure

- `geotop_arc_first_intersection` FULLY PROVED (commit e8baa6d5) — 41-line
  compactness argument. This is the key helper for Phase 1.C overlap's
  first-intersection strategy.

The remaining 6 §1+Intro sorries still need dedicated work for
direct closure (all require ~80-200 line classical PL proofs).

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
