# Fresh report on `isa_geotop1`, branch `codex-dev34-cache`

I re-inspected the current public branch, the raw theory files, recent progress reports, and the newest commit messages. I did **not** run Isabelle locally, so I cannot independently certify the session. This report is based on the pushed repository state and the worker’s own checked reports/commits.

## 1. Most important update

The worker’s pasted **5-hole** status appears to be **one commit stale** relative to the latest public branch.

The latest commit titled **“Close Figure 3.2 parent-empty count”** says it discharged the selected-free parent-empty subclaim at the old line-29514 location by replacing the local `sorry` with `hparent_empty_candidate_force_nonempty`. The same commit message says the live target holes dropped **from five to four**, leaving: the graph local-side bridge, the two Figure 3.3 fold packages, and Theorem 4.4’s brick/regular-neighborhood transfer. ([GitHub][1])

So the current best summary is:

> Public branch state appears to be **4 remaining target `sorry`s**, not 5, assuming the newest commit is included.
> Theorem 3.3 is no longer blocked by the line-29514 selected-free counting obstruction; it is now blocked by the graph/local-component bridge.

The worker’s broader judgment remains right: these are still **large book-proof packages**, not routine tactic cleanup.

---

## 2. Current live structure

The branch has become much better organized. The `tst` directory is split into layers such as `dev34_prefix_base`, `dev34_prefix_graph/cache`, `dev34_prefix_graph`, `dev34_prefix_mid`, `dev34_prefix`, and active `dev34`, plus generated indexes and progress reports. ([GitHub][2])

The fast-cache report is also relevant. It describes focused proof iteration through split layers and named targets such as `graph-branch`, `mid-split-free`, `mid-fold`, and `prefix-d44`. It explicitly warns that fast focused checks are for iteration, not final certification, and recommends broader checks at package boundaries. ([GitHub][3])

The current practical picture is therefore:

| Area            | Status                                                       |
| --------------- | ------------------------------------------------------------ |
| Section 3.1–3.2 | Closed                                                       |
| Section 3.3     | Structurally closed except for graph/local bridge dependency |
| Section 3.4     | Open through Figure 3.3 fold constructors                    |
| Section 3.5     | Downstream of 3.4                                            |
| Section 3.6     | Downstream of 3.4                                            |
| Section 3.7     | Open through same supported fold machinery                   |
| Section 4.1     | Closed                                                       |
| Section 4.2     | Closed in live source                                        |
| Section 4.3     | Closed                                                       |
| Section 4.4     | Open, largest remaining package                              |
| Active `dev34`  | No visible raw `sorry` in the current file inspection        |

The raw active `dev34/GeoTop_3_4.thy` search found no remaining `sorry`, and the earlier endpoint-chain and one-sided semicircle work now appears routed through proved wrappers rather than open active-file holes. ([GitHub][4])

---

## 3. Theorem 3.3: what remains now

The raw wrapper for `Theorem_GT_3_3` is short. It states that if `J` is a polygon, `K` is a complex whose polyhedron is the closed polygonal disk, and `K` has more than one 2-simplex, then some `σ₂` is a free 2-simplex of `K` relative to `J`. The proof calls the stronger count theorem, which proves at least two free 2-simplexes. ([GitHub][5])

The worker’s pasted status said Theorem 3.3 had two residuals:

1. the graph/local branch-point exclusion package;
2. the final selected-free counting obstruction around line 29514.

The newest commit says item 2 is closed. ([GitHub][1])

That leaves the graph/local bridge.

### 3.1 Remaining Theorem 3.3 blocker: graph local-side bridge

The remaining graph-cache `sorry` is inside:

```isabelle
geotop_branch_vertex_three_germs_same_side_component_prefix
```

The statement is explicitly a Moise branch-vertex local-side package, not an arbitrary graph theorem. It assumes the local simple-closed-curve / finite linear graph / local-star context and must produce a component of

```isabelle
ball w r - (S ∪ T ∪ U)
```

whose closure touches three selected incident edge germs. ([GitHub][6])

This then feeds the branch-vertex deletion/disconnect theorem:

```isabelle
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
```

which is used to rule out branch vertices in the polygonal/simple-closed-curve setting. ([GitHub][6])

### Recommendation for this proof

Do **not** try to prove the false general statement:

```text
degree > 2 ⇒ deleting the vertex disconnects the graph
```

That is false for theta-like finite graphs. The proof must use the **simple closed curve carrier** and the **local 1-manifold/two-sided behavior** near `w`.

The right target is the exact local bridge already staged in the cache file:

```isabelle
branch_vertex_three_germs_same_side_component:
  local simple-closed-curve star data
  + three distinct incident germs S,T,U at w
  + connected/local-side witness data
  ⟹ ∃C. C is a component of ball w r - (S ∪ T ∪ U)
        and closure C touches all three germs
```

The nearby proof already has the contradiction package: a local component of the punctured ball cannot touch three selected germs in a simple-closed-curve local model. The missing work is to **produce that component**, not to reprove the radial-sector contradiction.

A productive proof route is:

1. Use the existing connected sets/witnesses from the surrounding context, rather than introducing a new global graph path theorem.
2. Restrict to the local ball and use the already established cover by the three germ sectors plus the complement region.
3. Pick a point in the relevant local complement region and take its connected component in `ball w r - (S ∪ T ∪ U)`.
4. Use first-entry/closure arguments to show the same component touches the three germs.
5. Apply the already staged “no local component touches three germs” contradiction.

The proof should be kept specific to the variables and side data in `geotop_branch_vertex_three_germs_same_side_component_prefix`. A more general lemma will likely be either false or much harder.

Once this closes, Theorem 3.3 should be genuinely finished, assuming the latest selected-free count commit remains accepted by Isabelle.

---

## 4. Section 3 after Theorem 3.3

The raw mid-prefix file shows Theorems 3.4–3.7 are now organized correctly.

`Theorem_GT_3_4` is the theorem that every polygon is carried by a plane homeomorphism to the frontier of a 2-simplex. Its proof now obtains a triangulation and delegates the hard work to the fold-normalization package. ([GitHub][5])

`Theorem_GT_3_5` and `Theorem_GT_3_6` are downstream wrappers: 3.5 uses 3.4 twice plus simplex-frontier homeomorphism machinery, while 3.6 pulls back a 2-simplex under the homeomorphism from 3.4. ([GitHub][5])

`Theorem_GT_3_7`, the supported version of 3.4, also delegates to the same support-parametric fold-normalization package. ([GitHub][5])

So the worker’s Section 3 diagnosis is right:

> After the graph bridge closes Theorem 3.3, the only real Section 3 work is the Figure 3.3 fold construction package.
> Theorems 3.5 and 3.6 should not need new mathematics.

---

## 5. The two remaining fold holes

The current raw mid-prefix file shows two remaining fold constructors:

```isabelle
geotop_free_triangle_one_boundary_edge_supported_fold_prefix
geotop_free_triangle_two_boundary_edges_supported_inverse_fold_prefix
```

The one-boundary-edge case is described as Moise Figure 3.3 Case 1: a local quadrilateral fold, supported in `U`, that removes a free 2-simplex with one boundary edge. The two-boundary-edge case is described as the corner-removal / inverse fold case. ([GitHub][5])

The dispatcher then uses these contact cases inside the supported fold-reduction theorem, and the full fold-normalization induction composes this reduction with the induction hypothesis. ([GitHub][5])

### 5.1 Recommendation: prove the one-boundary case first

The one-boundary-edge fold should be treated as the primitive PL construction.

Recommended internal lemmas:

```isabelle
one_boundary_fold_local_carrier:
  identifies the local quadrilateral / fold carrier

one_boundary_fold_PL_homeomorphism:
  constructs the local PL homeomorphism

one_boundary_fold_extends_by_identity:
  extends the local map to the plane and fixes everything outside U

one_boundary_fold_reduces_triangle_count:
  the new complex has strictly fewer 2-simplexes

one_boundary_fold_preserves_disk_data:
  the image polygon and new complex still satisfy the induction hypotheses
```

The key is to **avoid building a global arbitrary homeomorphism from scratch**. Build the PL map on the local carrier and extend by identity. The conclusion needs a plane homeomorphism fixed outside `U`; that support condition should be proved from the construction, not patched at the end.

The count decrease should be a simple finite-set proof once the new complex is defined correctly:

```isabelle
{τ∈K'. dim τ = 2} ⊂ {τ∈K. dim τ = 2}
```

with the removed free triangle as the explicit omitted element.

### 5.2 Recommendation: derive the two-boundary case from the one-boundary case if possible

The two-boundary-edge case is described as an inverse/corner fold. If the local geometry permits it, prove it by applying the one-boundary fold to the inverse local picture, then invert the resulting supported homeomorphism.

That would avoid duplicating the PL map construction.

The proof should establish:

1. the corner triangle gives the inverse of a one-boundary fold model;
2. the inverse map is still identity outside `U`;
3. the image polygon/complex has the required reduced triangle count;
4. the new disk data match the induction hypothesis.

A small support lemma will be useful:

```isabelle
homeomorphism_identity_outside_inverse:
  assumes "homeomorphism h" and "∀x∉U. h x = x"
  shows "∀x∉U. inv h x = x"
```

and similarly for composition:

```isabelle
homeomorphism_identity_outside_comp:
  assumes "∀x∉U. f x = x" and "∀x∉U. g x = x"
  shows "∀x∉U. (g ∘ f) x = x"
```

If those already exist, use them directly; otherwise they are worth adding as general helper lemmas.

---

## 6. Section 4 status

Theorem 4.2 is now closed in the live source. The raw file shows `Theorem_GT_4_2` calling the opposite-boundary theta/component split theorem and then packaging the `U_Q`, `U_S` decomposition. ([GitHub][5])

Theorem 4.1 and Theorem 4.3 are also present as closed wrappers in the prefix files. ([GitHub][5])

That leaves Theorem 4.4.

---

## 7. Theorem 4.4: the remaining large Section 4 package

The final prefix file now contains the brick decomposition definition and the main D44 package:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

The single remaining `sorry` is not small. The surrounding comments explicitly bundle the fine brick decomposition, the regular neighborhood of one arc, the frontier as a simple closed curve/broken line, component-frontier facts, and cyclic-order transfer to `Q,S`. ([GitHub][7])

This is the largest remaining proof package.

### Recommendation: prove the conclusion as a regular-neighborhood theorem

The theorem ultimately needs a component `C` of

```isabelle
geotop_polygon_interior J - (A1 ∪ A2)
```

whose frontier contains both `Q` and `S`.

Do not expand the current `sorry` into five unrelated local `sorry`s. Instead, prove one internal theorem:

```isabelle
polygon_two_endpoint_arcs_regular_neighborhood_component_transfer:
  assumes polygon/cyclic-order data
      and A1,A2 are disjoint arcs in the closed disk
      and A1 ∩ J = {P}
      and A2 ∩ J = {R}
  shows ∃C. Q ∈ frontier C
          ∧ S ∈ frontier C
          ∧ C is the relevant component of
              polygon_interior J - (A1 ∪ A2)
```

Internally, this can still follow Moise’s brick proof:

1. Choose a fine brick or triangulated regular neighborhood `N` of `A1`.
2. Ensure `N` avoids `A2` except for prescribed endpoint behavior.
3. Intersect with the closed polygonal disk to obtain `N'`.
4. Prove `frontier N'` has the required polygonal/broken-line component.
5. Extract endpoints `V,W` on `J`.
6. Show `V,W` lie in the frontier of a single component of the complement.
7. Use cyclic order and the now-closed Theorem 4.2 separation machinery to transfer from `V,W` to `Q,S`.

If existing brick infrastructure is thin, a **triangulated regular neighborhood** of `A1` inside the disk may be cheaper than a literal rectangular brick decomposition. The current definition `geotop_brick_decomposition` can remain as a facade if needed, but the proof should target the actual component-transfer conclusion.

D44 should be left last unless it blocks something else. It is one visible hole, but it is proof-theoretically the largest remaining item.

---

## 8. Recommended finishing order from here

### Phase 1: Close the graph local-side bridge

Target:

```isabelle
geotop_branch_vertex_three_germs_same_side_component_prefix
```

This should finish the last apparent dependency of Theorem 3.3. Work in the already staged local-star context. Do not generalize to arbitrary finite graphs.

### Phase 2: Re-check Theorem 3.3 end-to-end

After the graph bridge closes, run the focused mid split and the live hole scan. The latest commit says the parent-empty count residual is already closed, so Theorem 3.3 should then be genuinely done. ([GitHub][1])

### Phase 3: Close the two Figure 3.3 fold constructors

Targets:

```isabelle
geotop_free_triangle_one_boundary_edge_supported_fold_prefix
geotop_free_triangle_two_boundary_edges_supported_inverse_fold_prefix
```

Prove the one-boundary-edge local fold first. Then derive or reuse as much as possible for the two-boundary inverse/corner case.

### Phase 4: Verify Theorems 3.4–3.7

Once the fold constructors close, check that:

```isabelle
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
Theorem_GT_3_4
Theorem_GT_3_5
Theorem_GT_3_6
Theorem_GT_3_7
```

all process without new local holes.

### Phase 5: Finish D44

Target:

```isabelle
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
```

Use the regular-neighborhood/component-transfer strategy. Treat this as the final large theorem package, not as cleanup.

---

## 9. Process advice

The worker should update the status report immediately from “5 holes” to “4 holes” if the latest commit has been pulled and accepted locally. The commit itself says the line-29514 selected-free count hole is gone and lists the four remaining target holes. ([GitHub][1])

Use the focused checker workflow:

```bash
./check_dev34_fast.sh holes
TIMEOUT=240s ./check_dev34_fast.sh focus graph-branch
TIMEOUT=240s ./check_dev34_fast.sh focus mid-fold
TIMEOUT=240s ./check_dev34_fast.sh focus prefix-d44
```

The fast-cache report recommends this style of focused iteration, followed by broader `cache-through` or layer checks at package boundaries. ([GitHub][3])

After each real package closure:

```bash
./check_dev34_fast.sh holes
bash gen_index.sh
bash gen_stmt_index.sh
./check_dev34_fast.sh cache-through <changed-theory>
```

The commit history is currently useful because it names proof packages precisely: side-count residuals, parent-boundary residuals, chord witness transfer, and Figure 3.2 parent-empty count. Keep that style. ([GitHub][8])

---

## 10. Direct assessment for the worker

The worker’s pasted diagnosis was essentially right, but the public branch now appears one commit ahead of it.

Theorem 3.3 is no longer missing the line-29514 selected-free counting endpoint. The remaining Theorem 3.3 obstruction is the graph/local-component bridge in the branch-vertex exclusion machinery. Close that next.

After that, Section 3 reduces to the two Figure 3.3 fold constructors. The support-parametric fold architecture is correct; preserve it. Do not prove an unsupported 3.4 separately and later redo 3.7. Build the local PL fold once with support control, then let 3.4 and 3.7 consume it.

Section 4 is now mostly done except Theorem 4.4. D44 is still a large Moise brick/regular-neighborhood theorem. Treat it as the final big package and prove the component-transfer conclusion through a regular-neighborhood construction, using the now-closed D42 separation machinery wherever possible.

The branch is genuinely close in organization and dependency structure. It is not close in the sense of “a few tactics left.” The fastest path to zero target `sorry`s is:

```text
graph local-side bridge
→ Theorem 3.3 final check
→ one-boundary fold
→ two-boundary inverse fold
→ Section 3 wrappers
→ D44 regular-neighborhood/component transfer
```

[1]: https://github.com/JUrban/isa_geotop1/commit/bb065cba68deaee0c6773bbffd569312a430ebb6 "Close Figure 3.2 parent-empty count · JUrban/isa_geotop1@bb065cb · GitHub"
[2]: https://github.com/JUrban/isa_geotop1/tree/codex-dev34-cache/tst "isa_geotop1/tst at codex-dev34-cache · JUrban/isa_geotop1 · GitHub"
[3]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/DEV34_FAST_CACHE_APPROACH_REPORT_2026_06_10.md?cb=202606121500 "raw.githubusercontent.com"
[4]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34/GeoTop_3_4.thy?cb=202606121540 "raw.githubusercontent.com"
[5]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy?cb=202606121520 "raw.githubusercontent.com"
[6]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy?cb=202606121530 "raw.githubusercontent.com"
[7]: https://raw.githubusercontent.com/JUrban/isa_geotop1/codex-dev34-cache/tst/dev34_prefix/GeoTop_3_4_Prefix.thy?cb=202606121550 "raw.githubusercontent.com"
[8]: https://github.com/JUrban/isa_geotop1/commits/codex-dev34-cache/ "Commits · JUrban/isa_geotop1 · GitHub"
