# Manual: `.dev34_fast_cache` and `check_dev34_fast.sh`

Date: 2026-06-10

This note documents the local fast-check approach used for the Section 3-4 Isabelle work. It explains what is cached, how the cache is keyed, which commands are intended for ordinary proof iteration, and where the approach can save time or give a false sense of safety.

The short version is:

- `check_dev34_fast.sh` is a workflow wrapper around `isabelle build`, `isabelle process_theories`, `rg`, and generated temporary theory sessions.
- `.dev34_fast_cache` is not the heap store itself. It is a small local metadata and generated-theory directory. The actual reusable heaps are produced by Isabelle with `-b` and `system_heaps=true`.
- The script has three cache classes: layer heap stamps, per-file process stamps, and theorem-prefix split sessions.
- It is fastest when we repeatedly edit a late proof inside a large theory and can reuse a compiled parent heap plus a compiled prefix ending immediately before the theorem under work.
- It does not replace final validation. It is a proof-loop accelerator.

## 1. Why This Exists

The Section 3-4 development has very large theory files and a deep layer structure:

```
dev34_pre
dev34_prefix_base
dev34_prefix_graph/cache
dev34_prefix_graph
dev34_prefix_mid
dev34_prefix
dev34_facts
dev34_workfacts
dev34_linkfacts
dev34_graphfacts
dev34_graphwork
dev34_openstar
dev34_core
dev34
```

Running a full build after every small proof edit is too expensive. Even processing one large file from the beginning can be slow when the active theorem is near the bottom of the file. The wrapper tries to make the common loop cheaper:

1. Search the full theorem/statement indexes and relevant source files before inventing lemmas.
2. Reuse compiled parent layers.
3. For a large current file, compile the completed prefix before the target theorem once.
4. Reprocess only the theorem or tail that changed.
5. Record enough hashes to skip work when the same check has already been run.

The script is deliberately conservative about correctness of cache freshness: it hashes source files, ROOT files, proof options, selected parent digests, and generated split files. If those inputs change, the stamp becomes stale and the check reruns.

## 2. What `.dev34_fast_cache` Contains

At the time of writing, this checkout has:

```
14 layer stamp files
5 process stamp files
145 split session directories
about 67 MB in .dev34_fast_cache
```

The exact numbers will drift. The important categories are stable:

### Layer stamps

Examples:

```
.dev34_fast_cache/pre.sha256
.dev34_fast_cache/prefix-base.sha256
.dev34_fast_cache/prefix-graph-cache.sha256
.dev34_fast_cache/prefix-graph.sha256
.dev34_fast_cache/prefix-mid.sha256
.dev34_fast_cache/prefix.sha256
.dev34_fast_cache/dev34.sha256
```

Each file stores a digest for one logical dev34 layer. The digest is computed from:

- target name,
- Isabelle session name,
- `FORCE_PROOFS`,
- the ROOT and theory files up through that layer.

When a layer stamp is fresh, the script assumes the corresponding Isabelle heap was already built with `isabelle build -b`. The stamp is the script's local freshness proof; the heap itself is stored by Isabelle, not inside `.dev34_fast_cache`.

### Process stamps

Examples:

```
.dev34_fast_cache/proc-489d94b33fceb8b328f314dadf4c2e2efec63112238e4a352c655e6d8373876a.sha256
```

These record that `isabelle process_theories` has already succeeded for a specific file against a specific parent logic under specific proof options. The digest includes:

- mode: `process_theories`,
- file path,
- parent logic,
- `FORCE_PROOFS`,
- `SKIP_PROOFS`,
- file hash,
- local ROOT hash if present,
- parent target,
- parent target digest.

This is a skip cache. It does not create a reusable Isabelle heap for the target file; it only says "this exact process check already passed."

### Split session directories

Examples:

```
.dev34_fast_cache/split-06c9f3d3c66c/ROOT
.dev34_fast_cache/split-06c9f3d3c66c/GeoTop_3_4_Prefix_Mid_Split_06c9f3d3c66c_Prefix.thy
.dev34_fast_cache/split-06c9f3d3c66c/GeoTop_3_4_Prefix_Mid_Split_06c9f3d3c66c_Slice.thy
```

A split directory is a generated mini-session for one source file and one pattern. The prefix theory imports the normal parent session and copies the current source file up to the first matching line. The slice or tail theory imports that compiled prefix and copies only the target theorem slice or the rest of the file.

The generated ROOT resembles:

```
session GeoTop_3_4_Prefix_Mid_Split_<key>_Prefix_Session = GeoTop34PrefixGraphDirty +
  options [system_heaps, quick_and_dirty, skip_proofs, timeout = 240]
  theories
    GeoTop_3_4_Prefix_Mid_Split_<key>_Prefix
```

This is the main speed trick. If the target theorem is late in `GeoTop_3_4_Prefix_Mid.thy`, the script can cache everything before it as a generated heap and then process only the theorem being edited.

### Split stamps

Examples:

```
.dev34_fast_cache/split-01244268a7d542bd883d9b53d6613d2644f85cd04aed62e0202176f3445dbbf1.sha256
```

There are two separate ideas:

- prefix stamp: the generated prefix session has been built for the current file/pattern/parent digest,
- tail or slice stamp: the generated tail or slice has been processed successfully for the current prefix digest and proof options.

The split key uses the source file, pattern, parent logic, and optional chain pattern. The content digest also includes hashes of generated files and parent-layer digests. Editing lines above the target theorem invalidates the prefix cache; editing only inside the target theorem usually invalidates the slice process cache but can keep the prefix heap fresh.

## 3. Command Families

The wrapper has many modes, but most usage falls into a small set.

### Cheap status and search

```
./check_dev34_fast.sh quick
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan PAT
./check_dev34_fast.sh index PAT
./check_dev34_fast.sh names PAT
./check_dev34_fast.sh stmts PAT
./check_dev34_fast.sh loop PAT
```

Use these constantly. They do not build large sessions. The `scan` and `loop` modes search both generated indexes and the target dev34 theory files. This matters because the index only sees named theorem/definition statements, while some useful facts are local `have`s in source.

`quick` prints:

- target holes,
- dirty dev34 layer files,
- the layer that `auto` would build,
- cache freshness for that layer.

`holes` is just a focused `rg` for `sorry` and `sledgehammer` markers in active dev34 layers.

### Layer heap caching

```
./check_dev34_fast.sh cache-plan [FILES]
./check_dev34_fast.sh cache-through [FILES]
./check_dev34_fast.sh cache-parents [FILES]
./check_dev34_fast.sh cache-status [FILES]
./check_dev34_fast.sh cache-all
```

Layer caching builds Isabelle heaps with `isabelle build -b` and then writes a stamp file under `.dev34_fast_cache`.

For example, when editing `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`, the reusable parent target is `prefix-graph`, whose session is `GeoTop34PrefixGraphDirty`. If that parent is fresh, a hot check can process the mid file against `GeoTop34PrefixGraphDirty` instead of rebuilding everything before it.

`cache-through` builds every layer up to the target, skipping already fresh layers. This is useful after larger structural changes or after adding/updating ROOT/session files.

`cache-parents` builds only the reusable parent layers for the supplied dirty files. This is usually enough before a focused proof loop.

### Whole-file hot checks

```
./check_dev34_fast.sh plan [FILES]
./check_dev34_fast.sh warm [FILES]
./check_dev34_fast.sh hot [FILES]
./check_dev34_fast.sh proc [FILES]
./check_dev34_fast.sh outline [FILES]
```

`hot` is an alias for `proc`. It chooses the parent logic for each changed or explicit dev34 file, auto-warms the parent heap, and runs:

```
isabelle process_theories ... -l PARENT_LOGIC -o quick_and_dirty -f FILE
```

The process cache can skip this if the exact same file has already been processed against the same fresh parent.

`outline` sets `SKIP_PROOFS=1` and is intended for sorry-first scaffolding and syntax/type-shape validation. It is not a proof check.

### Split and slice checks

```
./check_dev34_fast.sh split-warm FILE PAT
./check_dev34_fast.sh split-hot FILE PAT
./check_dev34_fast.sh slice-hot FILE PAT
```

These are the most important commands for large late proofs.

`split-warm` builds only the generated prefix before the first occurrence of `PAT`.

`split-hot` builds or reuses that prefix and then processes the rest of the source file after `PAT`.

`slice-hot` builds or reuses that prefix and then processes only the next top-level theorem/lemma/corollary/proposition slice. This is usually the fastest meaningful check while editing one theorem.

For example:

```
./check_dev34_fast.sh slice-hot \
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
  geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
```

That command finds the first matching line, copies the theory prefix before that line into a generated prefix theory, builds it if stale, then copies only that theorem slice into a generated slice theory and processes the slice.

### Named focus targets

```
./check_dev34_fast.sh focus-list
./check_dev34_fast.sh focus mid-d42
./check_dev34_fast.sh focus-full mid-d42
./check_dev34_fast.sh focus-warm mid-d42
./check_dev34_fast.sh focus-status mid-d42
./check_dev34_fast.sh focus-prime mid-d42
```

Named focus targets are aliases for the current known hard holes. They also run a full index/source scan before checking, which matches the instruction to grep the full index frequently.

Current focus names include:

```
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

For `mid-d42`, the focus target is:

```
file:    dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
pattern: theorem Theorem_GT_4_2
chain:   theorem Theorem_GT_3_7
```

The chain matters because the theorem is late in the file. The script can build a chain of prefix sessions, rather than trying to process the entire file prefix in one large temporary session every time.

## 4. How Freshness Works

The script uses hashes rather than timestamps. This is good because git checkout, file touching, and editor save behavior do not accidentally invalidate caches unless content changes.

The central digest functions are:

- `cache_digest TARGET`
- `proc_digest FILE PARENT_TARGET LOGIC`
- `split_cache_key FILE PATTERN LOGIC CHAIN_PATTERN`
- split prefix and tail digests assembled inside `split_hot_one`

### Layer freshness

A layer is fresh when:

```
.dev34_fast_cache/<target>.sha256 == cache_digest(<target>)
```

The digest includes all source files up through the layer. This means a change in an earlier layer invalidates later layer stamps because later layer digests include earlier source files.

### Process freshness

A process check is fresh only if the parent layer is also fresh. This prevents reusing a "passed" process stamp after its imported facts might have changed.

### Split prefix freshness

A split prefix is fresh only if:

- the generated prefix file has the same hash,
- the generated ROOT has the same hash,
- the parent target digest is the same,
- chained prefix digest, if any, is the same,
- `FORCE_PROOFS` is the same.

### Split slice or tail freshness

A slice or tail process stamp additionally includes:

- prefix digest,
- generated slice/tail file hash,
- `SKIP_PROOFS`,
- `FORCE_PROOFS`.

This means ordinary edits inside the active theorem should invalidate only the slice/tail process stamp. Edits above the theorem invalidate the prefix. Edits in an imported parent layer invalidate both.

## 5. Is It Faster?

Yes, for the proof-loop cases it was designed for. It is not a universal speedup.

The main savings come from avoiding repeated work:

- `holes`, `scan`, `loop` are near-instant compared with Isabelle.
- A fresh parent heap avoids rebuilding earlier dev34 layers.
- A fresh split prefix avoids replaying thousands of lines before a target theorem.
- A fresh process stamp can turn an accidental repeated check into a no-op.

The current `mid-d42` status illustrates the shape:

```
cache: fresh prefix-graph (GeoTop34PrefixGraphDirty)
split-hot: stale/missing prefix cache before Theorem_GT_3_7
split-hot: stale/missing prefix cache before Theorem_GT_4_2
split-hot: stale/missing slice process cache for Theorem_GT_4_2
```

That is not the fastest possible state, but it is still better than starting from scratch because the parent `prefix-graph` heap is fresh. After warming the chain, repeated edits inside Theorem 4.2 should generally need only the slice process step.

The worst case is the first check after an edit above a target theorem. In that case the prefix cache must be rebuilt. A theorem near the end of a huge file can still take a while, because the generated prefix contains most of that file. The benefit appears on the second and later checks if the prefix remains unchanged.

## 6. Downsides and Failure Modes

### It is easy to confuse proof-loop validation with final validation

Most hot modes use `quick_and_dirty`. Some outline modes use `skip_proofs=true`. These are appropriate while structuring proof code and diagnosing local failures, but they are not the final certificate for a theorem package.

Final validation still needs the relevant normal build/proof mode. At minimum, before treating a package as closed, run the appropriate non-outline check and then the target layer or full session check required by the project policy.

### Split files can hide context assumptions

The split method copies a source-file prefix and then a theorem slice into generated theories. It is faithful for ordinary top-level theorem iteration, but it is still a generated environment. If the original file has unusual commands, local notation setup, attributes, bundles, or side effects spanning the split boundary, a split can fail even when the original file would pass, or occasionally pass in a way that does not test the exact remaining file tail.

This project mostly uses it for ordinary theory text and top-level theorem slices, where it works well.

### Pattern selection matters

`split-hot` and `slice-hot` split at the first line matching the supplied pattern. If the pattern is too broad, the split may start at the wrong theorem. Use named focus targets when available, or use a specific theorem name.

Bad:

```
./check_dev34_fast.sh slice-hot FILE component
```

Better:

```
./check_dev34_fast.sh slice-hot FILE geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
```

### Prefix caches churn when editing above the target

When a helper is inserted above a theorem, every split prefix below it changes. This is unavoidable because the source prefix changed. For late-file theorem work, keep new helper development localized where possible, and commit stable helper packages so later checks have stable prefix material.

### `.dev34_fast_cache` is disposable but not self-pruning

The directory accumulates split sessions. It can be removed with:

```
./check_dev34_fast.sh cache-clean
```

That removes local stamps and generated split theories. It does not delete Isabelle heaps. Cleaning is useful if the directory becomes confusing or if generated sessions are suspected stale in a way the hashes did not catch. The cost is that the next hot check has to warm caches again.

### Stamps assume matching Isabelle heap availability

A fresh layer stamp says the source digest matches the last successful build. It does not itself contain the heap. If Isabelle's heap storage was cleaned externally, the stamp can say "fresh" while the heap is missing. In that case, force a rebuild:

```
FORCE_CACHE=1 ./check_dev34_fast.sh cache-through FILE
```

or clean and rebuild:

```
./check_dev34_fast.sh cache-clean
./check_dev34_fast.sh cache-through FILE
```

### Environment options are part of the meaning

The script keys on `FORCE_PROOFS` and `SKIP_PROOFS`, but it assumes the same Isabelle binary and compatible environment. If `/project/bin/isabelle`, ROOT semantics, or imported sessions change substantially, rebuild the relevant caches.

## 7. Practical Workflow for Theorem 3-4 Work

For ordinary proof work on a known focus theorem:

1. Search first:

   ```
   ./check_dev34_fast.sh focus mid-d42
   ```

   or, if the search term should be custom:

   ```
   ./check_dev34_fast.sh focus mid-d42 "separated side closure arc"
   ```

2. If the output says the prefix cache is stale, warm it once:

   ```
   ./check_dev34_fast.sh focus-warm mid-d42
   ```

3. Edit the theorem body.

4. Re-run the focused slice:

   ```
   ./check_dev34_fast.sh focus mid-d42
   ```

5. If only the current theorem changed, subsequent runs should usually reuse the prefix and process just the slice.

6. When a local package is stable, run a broader hot check:

   ```
   ./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
   ```

7. Before committing, check holes and relevant layer status:

   ```
   ./check_dev34_fast.sh holes
   ./check_dev34_fast.sh cache-status dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
   ```

For new top-level lemmas or theorem declarations, regenerate indexes after the successful check:

```
bash gen_index.sh
./gen_stmt_index.sh
```

Then grep both indexes before adding another nearby lemma:

```
rg -i "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

## 8. Recommended Command Choices

Use this most of the time:

```
./check_dev34_fast.sh scan PAT
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus NAME
./check_dev34_fast.sh slice-hot FILE SPECIFIC_THEOREM_NAME
```

Use this when caches are stale:

```
./check_dev34_fast.sh focus-warm NAME
./check_dev34_fast.sh cache-parents FILE
./check_dev34_fast.sh cache-through FILE
```

Use this for scaffolding only:

```
./check_dev34_fast.sh outline FILE
./check_dev34_fast.sh focus-outline NAME
```

Use this when cache behavior is suspicious:

```
./check_dev34_fast.sh focus-status NAME
FORCE_CACHE=1 ./check_dev34_fast.sh cache-through FILE
./check_dev34_fast.sh cache-clean
```

Use final builds when a package is genuinely ready to rely on. The fast script is an accelerator, not the final project invariant.

## 9. What I Would Improve Next

The current approach has helped, but there are clear improvements available.

First, add a cache status summary that prints all three levels together for a focus target:

```
parent heap: fresh/stale
chained prefix heap: fresh/stale
target prefix heap: fresh/stale
slice process stamp: fresh/stale
```

The current output contains this information, but it is verbose and not normalized.

Second, add cache garbage collection for old split sessions. A simple policy would keep:

- all fresh split directories for named focus targets,
- the newest N stale split directories,
- all layer and process stamps that still match current source digests.

Third, add timing logs per command. The script currently optimizes by skipping work, but it does not maintain a clear historical view of how much time each cache layer saves. A small `.dev34_fast_cache/timing.tsv` would make it easier to decide when a split target is worth warming.

Fourth, expose the exact generated split directory in normal output. The directory can already be derived from the key, but printing it would make debugging generated theory failures faster.

Fifth, consider making named focus targets data-driven. They are currently hard-coded in `check_dev34_fast.sh`. That is workable while the active holes are few, but a small table file would be easier to update as Section 3-4 moves.

## 10. Bottom Line

The approach is worth keeping. It addresses the real bottleneck: repeatedly replaying large theory prefixes while working on a single late proof. The speedup is largest after the first warm run and smallest after edits above the target theorem. Its main risk is procedural: a fast green slice is not the same as a final certified build.

For the current Section 3-4 work, the best discipline is:

- grep indexes and source often,
- use named focus targets for proof loops,
- warm parent and prefix caches when entering a hard theorem,
- avoid moving large helper blocks above active targets unless needed,
- commit stable packages with detailed messages,
- finish each package with broader validation before relying on it.

