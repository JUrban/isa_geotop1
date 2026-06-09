# Manual: `.dev34_fast_cache` and `check_dev34_fast.sh`

Date: 2026-06-09

This note explains the fast-checking workflow currently used for the Moise Sections 3-4 `dev34` work. It is intentionally a manual, not a progress report. The goal is to make the cache and checker predictable enough that future proof work can use it without turning each edit into a multi-minute rebuild.

The short version is:

* `check_dev34_fast.sh` is a wrapper around Isabelle builds, `process_theories`, full-index `rg` searches, and generated split theories.
* `.dev34_fast_cache/` stores freshness stamps and generated split sessions. The actual persistent heaps live in Isabelle's heap area because the script builds sessions with `system_heaps=true`.
* It is faster because it avoids rebuilding stable parent layers and because `slice-hot` can check only one top-level theorem/lemma after a cached prefix.
* The downside is that the fastest modes are development checks, not a replacement for final proof validation. They must be followed by broader builds, hole scans, and eventually a proof-forced check when we are closing a package.

As of this writing, `.dev34_fast_cache` contains 112 generated split directories, 254 SHA-256 stamp files, and uses about 44 MB in the working tree. The cache status for `dev34/GeoTop_3_4.thy` is good for the parent chain: `pre`, `prefix-base`, `prefix-graph-cache`, `prefix-graph`, `prefix-mid`, `prefix`, `facts`, `workfacts`, `linkfacts`, `graphfacts`, `graphwork`, `openstar`, and `core` are fresh. The full `dev34` layer itself is stale/missing, which is expected while `dev34/GeoTop_3_4.thy` has uncommitted proof edits.

## 1. Why This Exists

The old workflow was too expensive for the current kind of work. A small proof edit near the bottom of `dev34/GeoTop_3_4.thy` can sit behind tens of thousands of lines of imported local theory. Running a full Isabelle build after every change gives excellent confidence, but it burns most of the iteration budget on material that did not change.

The project has also reached the point where most remaining work is in a small number of named proof packages: graph local cutpoints, cyclic boundary realization, endpoint boundary-arc fan, semicircle separation, Section 3 fold/subdisk transfer, and D42/D44 arc/brick machinery. For those packages, the usual loop is:

1. Search the full index for existing facts.
2. Edit one helper or one theorem slice.
3. Check that slice against the already completed prefix.
4. Repeat.
5. Run broader checks before committing.

`check_dev34_fast.sh` supports exactly that loop. It bakes the layer order into a script, stores freshness stamps, generates temporary split theories, and gives named focus targets so we do not have to remember exact filenames and patterns every time.

The expert audits strongly reinforce this direction. They warn against treating each remaining `sorry` as an isolated local automation failure. The remaining work consists of theorem packages, and the productive workflow is to use full-index searches frequently, work on one package at a time, and validate small proof increments. The fast cache supports that workflow; it does not decide the mathematical strategy.

## 2. The Layer Model

The script knows the `dev34` layer stack in dependency order:

```text
pre
prefix-base
prefix-graph-cache
prefix-graph
prefix-mid
prefix
facts
workfacts
linkfacts
graphfacts
graphwork
openstar
core
dev34
```

Each layer corresponds to a session, for example:

```text
pre                 GeoTopPre3Dirty
prefix-graph-cache  GeoTop34PrefixGraphCacheDirty
prefix-mid          GeoTop34PrefixMidDirty
core                GeoTop34CoreDirty
dev34               GeoTop34Dev
```

The important rule is that a file is checked against its parent session. For example:

* `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` is processed with parent logic `GeoTop34PrefixGraphDirty`.
* `dev34_prefix/GeoTop_3_4_Prefix.thy` is processed with parent logic `GeoTop34PrefixMidDirty`.
* `dev34/GeoTop_3_4.thy` is processed with parent logic `GeoTop34CoreDirty`.

That is why the parent heap matters so much. If the `core` heap is fresh, a localized `dev34` proof check does not need to replay all earlier layers. If the `core` heap is stale, the script can rebuild the parent chain first, but that is the expensive path.

The command for inspecting this is:

```bash
./check_dev34_fast.sh cache-plan dev34/GeoTop_3_4.thy
```

At the current checkpoint it reports every parent through `core` fresh, and only the active `dev34` target stale. That is the desired state for endpoint-fan iteration.

## 3. What `.dev34_fast_cache` Contains

The cache directory has three main kinds of content.

First, layer freshness stamps:

```text
.dev34_fast_cache/core.sha256
.dev34_fast_cache/prefix-mid.sha256
.dev34_fast_cache/dev34.sha256
...
```

These are not Isabelle heaps. They are hashes saying, "the session heap for this layer was built from exactly these source files, with this session name and proof mode." The actual session heap is stored by Isabelle because the script passes:

```bash
-o system_heaps=true
```

Second, process-theory stamps:

```text
.dev34_fast_cache/proc-<hash>.sha256
```

These mark successful `process_theories` checks of a specific file against a specific parent logic, with the current file hash, parent digest, and proof/skip settings. If the file, ROOT, parent cache, or options change, the stamp no longer matches.

Third, generated split sessions:

```text
.dev34_fast_cache/split-<short-hash>/ROOT
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Prefix.thy
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Slice.thy
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Tail.thy
```

These are synthetic Isabelle theories. A split check takes a real theory file, finds a pattern, writes a prefix theory containing everything before that pattern, builds that prefix as a session, then checks either the next top-level declaration (`slice-hot`) or the rest of the file (`split-hot`) as a child theory.

This sounds elaborate, but the point is simple: if we are editing one theorem near line 17000, we can reuse a cached prefix through line 16999 and process only the theorem being edited.

## 4. How Freshness Is Computed

Freshness is deliberately conservative. The script hashes enough information to avoid reusing a cache after relevant source changes.

For a layer cache, `cache_digest` includes:

* target layer name,
* session name,
* `FORCE_PROOFS` setting,
* SHA-256 hashes of every source file up through that target layer.

For a `process_theories` cache, `proc_digest` includes:

* mode name,
* target file path,
* parent logic,
* `FORCE_PROOFS` and `SKIP_PROOFS`,
* the file hash,
* the file's layer ROOT hash if present,
* parent target name,
* parent target digest.

For split checks, the generated prefix and slice/tail files are also hashed. The split hash includes the file, pattern, chain pattern, proof options, prefix digest, and generated file contents.

This means the cache should invalidate when it matters:

* editing the active proof invalidates the active slice/tail stamp;
* editing an earlier theorem before the split point invalidates the prefix stamp;
* editing a parent layer invalidates child `process_theories` stamps;
* switching `FORCE_PROOFS` or `SKIP_PROOFS` produces different cache keys.

The cache is not semantic. It does not understand that a change was harmless. It only knows file hashes and dependency order. That is the right tradeoff for this workflow.

## 5. Main Modes

The most useful modes are these.

`holes`

```bash
./check_dev34_fast.sh holes
```

Runs `rg` for `sorry` and `sledgehammer` markers across the target `dev34` layers. This is the fastest honest status check. It should be run frequently.

`grep`, `scan`, `index`, `names`, `stmts`

```bash
./check_dev34_fast.sh scan "endpoint boundary edge chain"
./check_dev34_fast.sh index "convex hull insert"
./check_dev34_fast.sh names "old_hull"
./check_dev34_fast.sh stmts "geotop_is_subdivision"
```

These wrap full-index and source searches. `scan` searches `THEOREMS_AND_DEFS.txt`, `STMT_INDEX.txt`, and the target theories. This directly addresses the repeated problem that useful facts already exist but are easy to miss in a large theory.

`plan`

```bash
./check_dev34_fast.sh plan dev34/GeoTop_3_4.thy
```

Shows the parent logic and whether the reusable parent cache is fresh.

`cache-plan`, `cache-through`, `cache-parents`

```bash
./check_dev34_fast.sh cache-plan dev34/GeoTop_3_4.thy
./check_dev34_fast.sh cache-through dev34/GeoTop_3_4.thy
./check_dev34_fast.sh cache-parents dev34/GeoTop_3_4.thy
```

`cache-plan` reports freshness without building. `cache-through` builds all missing/stale layers through the target. `cache-parents` warms only reusable parents for the specified file.

`hot` / `proc`

```bash
./check_dev34_fast.sh hot dev34/GeoTop_3_4.thy
```

Processes the whole file against its parent logic. It auto-warms the parent by default. It skips work if both the parent target and process stamp are fresh.

`outline`

```bash
./check_dev34_fast.sh outline dev34/GeoTop_3_4.thy
```

Same idea as `proc`, but with `SKIP_PROOFS=1`. This is useful for scaffold/syntax checks after inserting `sorry`-first proof structure. It is not proof validation.

`slice-hot`

```bash
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_endpoint_boundary_edge_chain_old_hull_iff_dev34
```

This is the main proof-edit loop. It builds or reuses a generated prefix before the named pattern, then checks only the next top-level theorem/lemma slice. It is usually much faster than processing the entire active file.

`split-hot`

```bash
./check_dev34_fast.sh split-hot dev34/GeoTop_3_4.thy geotop_endpoint_boundary_edge_chain_cone_fan_from_chain_target_dev34
```

This is like `slice-hot`, but processes from the pattern through the end of the file. It is slower, but useful when downstream material may depend on the edited theorem.

`focus`

```bash
./check_dev34_fast.sh focus-list
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus-status dev34-fan
./check_dev34_fast.sh focus-prime dev34-fan dev34-semicircle
```

Focus modes encode the known remaining packages. A focus run first does a full-index/source scan using a relevant search phrase, then runs the right split or slice check. This is the mode that best matches the expert-audit advice: search first, then check the localized target.

## 6. Named Focus Targets

The script currently knows these focus names:

```text
graph-branch
graph-branch-local
graph-cycle-cut
mid-split-free
mid-fold
mid-support
mid-d42
prefix-d44
dev34-cycle
dev34-cycle-realization
dev34-fan
dev34-semicircle
```

Each maps to a file, a pattern, and a search phrase. For example:

* `dev34-fan` maps to `dev34/GeoTop_3_4.thy` at `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
* `dev34-cycle-realization` maps to the cyclic vertex listing boundary subdivision model.
* `dev34-semicircle` maps to the one-side semicircle separator and chains after the endpoint fan target.
* `mid-d42` starts at `Theorem_GT_4_2` and uses `Theorem_GT_3_7` as a chained prefix.

The chained-prefix feature matters for large files. Some later targets depend on substantial earlier sections in the same physical file. Rather than rebuilding the whole file prefix as one huge synthetic theory every time, the script can first cache an earlier prefix, then build the next prefix on top of it.

## 7. Is It Faster?

Yes, for the intended loop.

The expensive case remains expensive: if a parent layer is stale, Isabelle still has to rebuild it. The script cannot make a real dependency disappear. But when the parent chain is fresh, a localized theorem edit can avoid the cost of replaying all parent material.

The current endpoint-fan workflow is a good example. The active file `dev34/GeoTop_3_4.thy` is dirty, but `core` is fresh. A direct full build of `GeoTop34Dev` has to consider the active session. A `slice-hot` check of one helper can instead:

1. reuse the fresh `core` parent heap;
2. build or reuse a generated prefix before the helper;
3. process only the next top-level lemma/theorem.

Once the generated prefix exists, repeated edits inside the same slice usually only rerun the slice process. In the best case, a second identical run returns immediately with "skipped ... fresh process cache." In the common edit case, the prefix is skipped and only the slice is processed.

This does not turn a hard proof into a cheap proof. If the slice itself contains slow automation, the slice can still take time or time out. What it removes is unrelated replay cost.

The observed cache state supports the claim. The cache directory itself is only about 44 MB, but it tracks a much larger amount of reusable Isabelle work through system heaps and freshness stamps. The fact that parent layers through `core` are fresh means active `dev34` work can iterate without paying for the completed graph/facts/openstar/core layers unless those files change.

## 8. Downsides and Failure Modes

The main downside is that fast modes can give a false sense of completion if they are treated as final certification.

`slice-hot` checks one generated slice, not the whole theory file. It is ideal for "does this lemma body compile in context?" It does not prove that all later lemmas still work. After a helper is changed, run at least a downstream `split-hot` or `hot` check before committing.

Generated split prefix sessions use `quick_and_dirty` and `skip_proofs` for the cached prefix. This is intentional: the prefix has normally already been checked in its real layer, and the synthetic prefix exists to make local iteration fast. But it means a split prefix is not an independent proof certificate. The final authority remains the real theory/session build.

`outline` and `SKIP_PROOFS=1` are syntax/scaffold tools. They are useful under the `CLAUDE.md` workflow because new proof structure should be written with `sorry` first and compiled immediately. But outline success says only that the statements and structure fit; it does not validate proof terms.

The cache can grow. It is currently modest, but every new split pattern can create another split directory and stamp files. `cache-clean` removes freshness stamps, but generated split directories may remain unless cleaned separately. This is not urgent at 44 MB, but it is worth remembering.

Pattern selection matters. `slice-hot FILE PAT` uses the first `rg` match for `PAT`. If a pattern is too vague, the split point may be wrong. Use theorem names or distinctive strings, not generic words.

Line movement is normal. Split sessions are based on pattern search, not fixed line numbers, so they survive inserted lines. But if a theorem is renamed or duplicated, the cached split may become stale or select the wrong occurrence.

The script is repository-specific. It encodes the `dev34` layer names, session names, and current target focus packages. If new session files are added or moved, the arrays and parent mappings in `check_dev34_fast.sh` must be updated, and the theorem/statement indexes should be regenerated.

## 9. Recommended Daily Workflow

For ordinary proof work:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan "words from the goal"
./check_dev34_fast.sh focus-status dev34-fan
./check_dev34_fast.sh focus dev34-fan
```

For editing a specific helper:

```bash
./check_dev34_fast.sh scan "old hull cone endpoint"
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_endpoint_boundary_edge_chain_old_hull_iff_dev34
```

For checking downstream from a theorem:

```bash
./check_dev34_fast.sh split-hot dev34/GeoTop_3_4.thy geotop_endpoint_boundary_edge_chain_cone_fan_from_chain_target_dev34
```

For warming after a parent change:

```bash
./check_dev34_fast.sh cache-through dev34/GeoTop_3_4.thy
```

Before a commit:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh hot dev34/GeoTop_3_4.thy
bash gen_index.sh
bash gen_stmt_index.sh
git diff --check -- dev34/GeoTop_3_4.thy THEOREMS_AND_DEFS.txt THEOREMS_AND_DEFS.md STMT_INDEX.txt INDEX_THEORIES.txt
```

When closing a package rather than just making local progress, add a broader proof check. Depending on the package, that may be `split-hot` through file end, the exact dirty layer build, or a `FORCE_PROOFS=1` run. The faster the previous checks were, the more important it is to run one broader check before calling the package closed.

## 10. How This Fits the Current Goal

For the active endpoint-fan work, the cache strategy is:

1. Keep `core` and earlier parent layers fresh.
2. Use `scan` aggressively before writing lemmas, especially over `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`.
3. Check each new endpoint helper with `slice-hot`.
4. Check the target endpoint fan theorem with `slice-hot` or `split-hot` after helper batches.
5. Regenerate indexes after committed theorem additions.
6. Commit frequently with a detailed 10-30 line message explaining which Moise theorem package moved and what remains.

The current proof state already benefits from this. The old-hull and cone-separation endpoint helpers can be checked individually without replaying all of `dev34`. The next hard subproblem, the cone-hull iff direction for the endpoint fan, should be developed the same way: search full index first, write a small statement, `slice-hot` it, then connect it to the fan target.

## 11. Maintenance Notes

When adding new sessions or moving files, update these parts of `check_dev34_fast.sh` together:

* `target_theories`
* `hole_theories`
* `layer_rank`
* `target_rank`
* `target_layer_dir`
* `target_session`
* `layer_targets`
* `target_timeout`
* `target_dirs_args`
* `target_source_files`
* `parent_context`
* `parent_target_for_file`

When adding new long-running proof packages, add a focus target:

* add the name to `focus_target_names`;
* map it in `focus_target`;
* add a `focus_chain_pattern` if a prior same-file prefix should be cached first;
* add a `split_default_chain_pattern` if direct `split-hot` on the later theorem should automatically chain through the earlier one.

After adding or moving theorems, regenerate:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

This is important because the fast workflow depends on the full index being useful. The cache makes checking faster; the indexes make proof search and theorem discovery faster.

## 12. Bottom Line

The fast cache is a practical development accelerator. It is fastest when the parent chain is fresh and the edit is localized to one theorem. It is least helpful when an early parent layer changes, when the theorem slice itself is intrinsically slow, or when final certification is required.

The correct mental model is:

```text
full index grep     tells us what facts already exist
parent heap cache   avoids replaying stable layers
split prefix cache  avoids replaying stable earlier text in the same file
slice-hot           validates one local theorem edit quickly
split-hot/hot       checks downstream or whole-file consequences
final build         certifies the real target before closure
```

Used this way, the cache is faster and safe enough for proof development. It is not a substitute for final builds, and it should not be used to hide stale statements or broad dependencies. It should let us spend iteration time on the remaining Moise arguments themselves rather than repeatedly rebuilding material that is already done.
