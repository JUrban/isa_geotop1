# Sections 3-4 Formalization Overview

Date: 2026-06-17

This is a brief project report on the Moise Sections 3-4 formalization work in `tst/`.  The detailed item-by-item correspondence is in `SECTIONS_3_4_FORMALIZATION_MAP.md` and `SECTIONS_3_4_FORMALIZATION_DETAILS.tex`.

## Current Status

The Section 3-4 theorem chain is closed in the current `dev34` split:

- Section 3: `Theorem_GT_3_1` through `Theorem_GT_3_7`.
- Section 4: `Theorem_GT_4_1` through `Theorem_GT_4_10`.
- Main Section 3 definitions: `geotop_free_2_simplex`, `geotop_boundary_free_2_simplex`.
- Main Section 4 definition: `geotop_brick_decomposition`.
- Support theorem outside Sections 3-4: `Theorem_GT_4_invariance_of_domain` in `gb/GeoTopBase.thy:6722`.

A direct scan of the current Section 3-4 theory files found no active `sorry` or `oops` markers.  The only hit for `admit` was prose in a comment using the English word "admits".

## Size and Location

| Area | File or directory | Lines / size | Role |
|---|---:|---:|---|
| Base prefix | `dev34_prefix_base/GeoTop_3_4_Prefix_Base.thy` | 5,865 lines | Theorems 3.1-3.2 and low-level simplex/homeomorphism setup. |
| Mid prefix | `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` | 67,258 lines | Free-simplex machinery, Theorems 3.3-3.7, and Theorems 4.1-4.2. |
| Prefix | `dev34_prefix/GeoTop_3_4_Prefix.thy` | 32,860 lines | Theorem 4.3, brick-decomposition definition, and Theorem 4.4. |
| Facts layer | `dev34_facts/GeoTop_3_4_Facts.thy` | 7,516 lines | Theorems 4.5-4.7 and reusable Jordan/separation facts. |
| Final dev34 layer | `dev34/GeoTop_3_4.thy` | 32,239 lines | Theorems 4.8-4.10 and the manifold/link/star work. |
| Main proof files total | above five `.thy` files | 145,738 lines | Working Section 3-4 formalization split. |
| Fast cache | `.dev34_fast_cache/` | about 90 MB | Generated prefix/slice cache for faster focused checks. |
| Report snippets | `sections_3_4_snippets/` | about 160 KB | Cached exact source excerpts for the detailed LaTeX report. |
| Rendered snippets | `sections_3_4_rendered/` | about 80 KB | Rendered book excerpts for the detailed LaTeX report. |

## How It Was Done

The development was split into layers so that finished infrastructure could be reused without replaying the whole theory stack on every edit.  The main layers are `dev34_prefix_base`, `dev34_prefix_mid`, `dev34_prefix`, `dev34_facts`, and `dev34`.

The workflow relied heavily on searchable indexes:

- `THEOREMS_AND_DEFS.txt` for declaration names and line numbers.
- `STMT_INDEX.txt` for normalized theorem/definition statements.
- Full-tree `rg` searches for local proof facts and comments.

The fast iteration path used `.dev34_fast_cache` and `check_dev34_fast.sh`.  That cache stores generated prefixes and focused slices so that a long theorem package can be checked without rebuilding all earlier finished text.  It is a development accelerator, not a substitute for final Isabelle verification.

## Main Proof Strategy

Section 3 was closed by turning Moise's geometric induction into explicit reusable packages:

- Theorem 3.3 uses the stronger "at least two free 2-simplexes" induction.
- Theorem 3.4 uses the Figure 3.3 fold and inverse-fold packages.
- Theorem 3.7 reuses the same fold normalization with support control outside a chosen open set.

Section 4 was closed by mixing faithful formalizations of Moise's arguments with library-backed topological bridges:

- Theorem 4.2 packages the opposite-boundary arc separation argument.
- Theorem 4.4 packages the brick/regular-neighborhood component-transfer argument.
- Theorems 4.3, 4.5, and 4.6 use HOL-Analysis/Jordan-Brouwer bridges where that is cleaner than replaying every planar picture argument.
- Theorem 4.8 follows Moise's five-link-lemma plan inside the theorem body.
- Theorem 4.9 identifies the topological boundary with one-incident edges.
- Theorem 4.10 uses the invariance-of-domain bridge for the frontier-to-boundary inclusion.

## Problems and Solutions

| Problem | Solution |
|---|---|
| Long theory files made ordinary verification slow. | Split the development into layers and used `.dev34_fast_cache` focused prefix/slice checks. |
| Search by memory was unreliable in a 100k+ line development. | Regenerated and used `THEOREMS_AND_DEFS.txt`, `STMT_INDEX.txt`, and full-index `rg` searches frequently. |
| Moise's proofs rely on figures and phrases such as "evidently". | Replaced picture arguments by named local lemmas and reusable geometric packages. |
| Theorem 3.3 needed a stronger induction than the final theorem statement. | Proved and used the two-free-simplex count theorem, then extracted the weaker witness theorem. |
| Theorem 3.4 and 3.7 required controlled plane homeomorphisms. | Built supported Figure 3.3 fold/inverse-fold packages and a supported normalization theorem. |
| Theorem 4.4's brick proof was too broad if formalized as a general brick theory. | Focused on the exact component-transfer conclusion needed by the theorem. |
| Theorem 4.8 needed many local incidence and link facts. | Broke the proof into L1-L5 local steps plus named semicircle, three-incident-simplex, and Figure 4.10 cone/link packages. |
| The detailed LaTeX report became slow to compile when it read high line ranges from large `.thy` files. | Cached source excerpts in `sections_3_4_snippets/` and rendered book excerpts in `sections_3_4_rendered/`. |

## What Went Well

- The split architecture made it possible to close very large theorem packages incrementally.
- The index files made theorem lookup and line-number reporting practical.
- The proof packages now document the correspondence between Moise's informal geometric steps and formal Isabelle objects.
- The final report files give both a compact map and a detailed three-view explanation: raw book LaTeX, rendered book statement/proof, and Isabelle statement.

## Remaining Caveats

- The `dev34` split is a working formalization layer; integration into the final canonical `GeoTop.thy` layout may still require cleanup.
- Some book sublemmas are absorbed into stronger library-backed theorems rather than reproduced line-for-line.
- The fast cache is local generated state and should be treated as an iteration aid.
- The local TeX installation in this environment cannot build PDFs because required TeX format files are missing; the LaTeX sources themselves were written to be portable.

