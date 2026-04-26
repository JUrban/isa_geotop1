# PLAN3.md — Closing the final basis sorry (REVISED 2026-04-26)

## SUPERSEDED — see ANSWER_REPORT.md and ACK_ANSWER_REPORT.md

The original PLAN3 (and PLAN3_WEEK1, PLAN3_WEEK2) followed the strategy of proving an iterated barycentric subdivision refinement theorem:

> Sd^N K refines K' for some N when K' is a subdivision of K.

**This claim is FALSE.** A 1-dimensional counterexample (subdivision of [0,1] at 1/3, dyadic-only Sd^N vertices) decisively disproves it. See `ANSWER_REPORT.md` for the mathematician's full analysis.

The correct strategy is the classical **overlay-cell-complex construction** (Hudson, *Piecewise Linear Topology*, Chapter I §2). This is documented in `ANSWER_REPORT.md` with an 8-phase Isabelle development plan.

## Status

**As of 2026-04-26 (commit `d7789231`):**

- Basis (`b0/GeoTopBase0.thy` + `b/GeoTopBase.thy`) has **1 sorry** on the FALSE theorem, now renamed to `geotop_iterated_Sd_refines_subdivision_FALSE` (marked, quarantined).
- Build green at ~22-23s.
- All 28+ supporting carrier-map infrastructure exports from prior work are preserved (still useful for Phase 5 of the new strategy).

## New strategy (per ANSWER_REPORT.md)

### Overview

```text
Given finite simplicial complexes L1, L2 with |L1| = |L2|:
1. Form the raw overlay cells {σ ∩ τ : σ ∈ L1, τ ∈ L2, σ ∩ τ ≠ ∅}.
2. Close under faces to get a finite convex cell complex C.
3. Triangulate C (Hudson Lemma 1.4 OR order-complex triangulation).
4. The triangulation M is the common subdivision: every simplex of M
   is contained in σ ∩ τ for some σ ∈ L1 and τ ∈ L2.
```

The new vertices created at boundaries of L1 ∪ L2 (e.g., at 1/3 in the counterexample) avoid the dyadic-vs-irrational issue.

### 8-phase development plan (per mathematician)

- **Phase 0**: Disable / quarantine the false theorem. ✅ DONE (commit `d7789231`).
- **Phase 1**: Convex cells (definition, simplex⇒cell, cell∩cell=cell). ~150-200 lines.
- **Phase 2**: Cell faces (definition, basic lemmas, finite-faces). ~100-150 lines.
- **Phase 3**: Convex cell complex (definition, polyhedron, subdivision). ~80-100 lines.
- **Phase 4**: Overlay cell complex (raw + face closure + properties). ~150-200 lines.
- **Phase 5**: Triangulating a cell complex (Hudson 1.4 or order-complex). ~200-300 lines.
- **Phase 6**: Bridge from cell-subdivision to simplicial-subdivision. ~100-150 lines.
- **Phase 7**: Final `geotop_common_subdivision_finite` theorem. ~50 lines.
- **Phase 8**: Reprove `Theorem_GT_1` using new theorem. ~50 lines.

**Total estimated:** ~900-1200 lines of new Isar across 4-6 weeks.

### Recommendations from mathematician

1. **Use face-closure approach** (don't require all cell faces present in original overlay). Add face closure as a definition step. Safer for formalization.

2. **Use Option B (order-complex triangulation)** for Phase 5. Leverages our existing barycentric subdivision machinery (W1.0-W1.5 from previous work). Vertices = barycenters of cells, simplices = chains of cells under proper-face order.

3. **Watch the union condition** carefully. "Every coarse simplex = finite union of finer simplices" is NOT automatic from containment + finiteness. Requires face-compatible triangulation, which is given by face-closure of overlay + cell-by-cell triangulation.

4. **Hyperplane arrangement** as fallback. If overlay intersection property gets hard, switch to representing cells as sign/equality patterns over a finite set of supporting hyperplanes.

## What's preserved from prior work (still useful)

The Week 1 lemmas (W1.0-W1.5) about Sd^m K simplex structure are NOT directly applicable to the new strategy (no longer using iterated barycentric subdivision). However:

- **Carrier-map infrastructure (~14 K_carrier exports)**: useful for Phase 5 (relating cell rel-interiors to simplex rel-interiors, bridging cell-complex to simplicial-complex notions).
- **Munkres 14.4 biconditional**: applies to the order-complex triangulation (verifying it's a simplicial complex).
- **Closed star definition**: useful for Phase 5 cell-complex topology arguments.
- **Chain-simplex barycenter machinery (`geotop_chain_barycenters_in_top`, etc.)**: directly applies to order-complex of cell poset (chains of cells correspond to chains of simplices, but at cell level instead of simplex level).
- **Bridge stabilization fix (`d9b226f7`)**: still applies, build remains stable.

The ~28+ infrastructure exports are NOT wasted.

## Next steps

1. ✅ Phase 0 done.
2. Read `hudson1-3.tex` Chapter I §2 carefully (50-100 page extraction).
3. Write `PLAN3_PHASE1.md` with concrete attack outline for Phase 1 (convex cells).
4. Begin Phase 1 implementation in fresh focused session.

## Files

- `ANSWER_REPORT.md`: mathematician's full response.
- `ACK_ANSWER_REPORT.md`: my acknowledgment.
- `hudson1-3.tex`: Hudson's PL topology Chapter I-III.
- `REPORT_LITERAL.md`: prior self-contained statement of the false claim.
- This file (`PLAN3.md`): SUPERSEDED original plan; revised to reflect new strategy.
- `PLAN3_WEEK1.md`, `PLAN3_WEEK2.md`: SUPERSEDED Week 1/2 sub-plans of the failed strategy.
