# Manual: `.dev34_fast_cache` and `check_dev34_fast.sh`

Last reviewed against the script on 2026-06-10.

This note documents the fast checking workflow used for the GeoTop Sections 3-4 development. It is intentionally about the local implementation in `check_dev34_fast.sh`, not a general Isabelle caching guide. The short version is that the script turns the large `GeoTop` development into a sequence of reusable dirty sessions, records content hashes in `.dev34_fast_cache`, and generates temporary split theories so that a proof can be checked against a cached prefix instead of reparsing and replaying the whole active stack on every iteration.

The mechanism is useful, and it is faster for the kind of work we are doing now. It also has real limits. It is a development accelerator, not a replacement for final full builds, and the split modes can only certify the slice that they actually process. The right workflow is to use the fast modes many times while editing, then run broader checks whenever a named proof package closes or a statement changes.

At the time of this review, the local `.dev34_fast_cache` directory is about
71 MB and contains hundreds of stamps plus roughly 150 generated split
directories. That is normal for this style of development. The large proof
objects are still Isabelle heaps, stored by Isabelle's heap mechanism; the
cache directory mostly contains hashes and small generated theories.

## 1. The Problem It Solves

The Sections 3-4 files are large and layered. The current target stack is not one clean, small theory; it is split across:

```text
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

Each later layer imports earlier work. A naive verification loop tends to do too much: after changing a few lines in `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`, a broad build can replay unrelated graph cache work, prefix-base work, later facts, and sometimes the active `dev34` layer. That is expensive. Worse, the cost is paid repeatedly while the local edit is still just a proof skeleton or a small statement-shape experiment.

The script attacks this in three ways.

First, it maps each file to the smallest session that can check it. For example, `dev34_prefix_mid/...` is processed with parent logic `GeoTop34PrefixGraphDirty`, while `dev34_prefix/...` is processed with parent logic `GeoTop34PrefixMidDirty`. The parent context is chosen by `parent_context`, and the reusable parent target is chosen by `parent_target_for_file`.

Second, it records SHA-256 stamps for successfully built layer heaps. If the inputs for `prefix-graph` have not changed, the script can skip rebuilding that heap and reuse it as the parent for `prefix-mid` checks. These stamps live in `.dev34_fast_cache/*.sha256`.

Third, for long files it can split a theory at a named theorem or lemma. The prefix before the target is copied into a generated temporary theory and built once. Then only the target slice, or the tail from the target to the end of the file, is processed against that generated prefix session. This is the job of `split-hot`, `slice-hot`, `focus`, and related modes.

## 2. What Lives in `.dev34_fast_cache`

The cache directory contains three main classes of artifacts.

Layer stamps are files such as:

```text
.dev34_fast_cache/pre.sha256
.dev34_fast_cache/prefix-base.sha256
.dev34_fast_cache/prefix-graph-cache.sha256
.dev34_fast_cache/prefix-graph.sha256
.dev34_fast_cache/prefix-mid.sha256
.dev34_fast_cache/prefix.sha256
.dev34_fast_cache/core.sha256
.dev34_fast_cache/dev34.sha256
```

Each layer stamp records a digest computed from the target name, the Isabelle session name, the `FORCE_PROOFS` setting, and the source files that belong to that layer and its predecessors. The digest is not the heap itself. Isabelle stores the actual heap in its normal heap location because the build uses `-o system_heaps=true`. The stamp says, in effect, "the corresponding heap was successfully built for exactly these tracked inputs."

Process stamps have names like:

```text
.dev34_fast_cache/proc-<sha256>.sha256
```

These represent a successful `process_theories` run for one file against a particular parent logic. The digest includes the file, its layer `ROOT` if present, parent target, parent digest, `FORCE_PROOFS`, and `SKIP_PROOFS`. If none of that changes, `hot` can skip the file-level process check.

Split cache entries are directories and stamps such as:

```text
.dev34_fast_cache/split-06c9f3d3c66c/
.dev34_fast_cache/split-06c9f3d3c66c/ROOT
.dev34_fast_cache/split-06c9f3d3c66c/GeoTop_3_4_Prefix_Mid_Split_06c9f3d3c66c_Prefix.thy
.dev34_fast_cache/split-06c9f3d3c66c/GeoTop_3_4_Prefix_Mid_Split_06c9f3d3c66c_Slice.thy
.dev34_fast_cache/split-<long sha>.sha256
```

The short split directory key is derived from the file, the target pattern, the parent logic, and any chained split pattern. The generated `ROOT` defines a temporary session. The generated prefix theory imports the real parent or another generated prefix session. The generated slice or tail theory imports the prefix session and contains only the target region being checked.

This is why the directory can contain many split folders. They are cheap compared to Isabelle heaps, and they make repeated checks of a specific large theorem much faster once the prefix is warm.

The split directories are intentionally content-addressed by a short key. A
change to the file, split pattern, parent logic, or chained split pattern leads
to a different key or a stale stamp. The old directory can remain on disk
without being trusted, because freshness is decided by the stamp digest rather
than by the directory name alone.

There are also process stamps:

```text
.dev34_fast_cache/proc-<hash>.sha256
```

These are useful when asking "has this exact file already processed against
this exact fresh parent?". They are less useful when asking "how long does this
take?", because a fresh process stamp will skip the run. Disable that behavior
with `DEV34_FAST_PROC_CACHE=0` when measuring runtime.

## 2.1. How the Script Chooses a Parent

The central engineering decision is the parent mapping. `parent_context` maps a
file to the logic that should already be available, and `parent_target_for_file`
maps the same file to the cache layer that can be warmed.

The important mappings are:

```text
file under dev34_prefix_base     parent logic GeoTopPre3Dirty
file under dev34_prefix_graph    parent logic GeoTop34PrefixBaseDirty
file under dev34_prefix_mid      parent logic GeoTop34PrefixGraphDirty
file under dev34_prefix          parent logic GeoTop34PrefixMidDirty
file under dev34_facts           parent logic GeoTop34PrefixDirty
file under dev34_workfacts       parent logic GeoTop34FactsDirty
file under dev34_linkfacts       parent logic GeoTop34WorkFactsDirty
file under dev34_graphfacts      parent logic GeoTop34LinkFactsDirty
file under dev34_graphwork       parent logic GeoTop34GraphFactsDirty
file under dev34_openstar        parent logic GeoTop34GraphWorkDirty
file under dev34_core            parent logic GeoTop34OpenStarDirty
file under dev34                 parent logic GeoTop34CoreDirty
```

This is why `hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` does not need to
start from the original `GeoTop` base every time. It can load the graph prefix
heap and then process the mid-prefix theory.

The `auto_target` function is separate. It maps dirty or explicit files to the
smallest layer build target that would cover them. That is what powers `quick`,
`dirty`, `auto`, `cache`, and `cache-through`.

## 3. The Main Modes

`holes` is the cheapest status command:

```bash
./check_dev34_fast.sh holes
```

It runs `rg` for `sorry` and `sledgehammer` markers in the target dev34 theories. It does not build anything and therefore cannot prove that the files compile. It is a map of remaining executable holes.

`index`, `names`, `stmts`, `grep`, and `scan` are search helpers:

```bash
./check_dev34_fast.sh index "free 2 simplex"
./check_dev34_fast.sh scan "subdisk selected edge"
```

They grep the full generated indexes, and `scan` also searches the active target theories. This matters because a large fraction of wasted proof time comes from reproving or restating facts that are already in another layer. The right habit is to scan before adding a helper, and to scan again when a proof gets stuck.

`plan` shows what parent heap would be used for a file:

```bash
./check_dev34_fast.sh plan dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

It prints the parent logic and whether the parent layer cache is fresh or stale. This is the fastest way to decide whether a slow run is likely to be a cold-cache problem.

`warm` builds the parent heap for one or more files:

```bash
./check_dev34_fast.sh warm dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

For a mid-prefix file, this warms `prefix-graph`. It does not process the file itself.

`hot` is the normal file-level proof check:

```bash
./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

It auto-warms the parent layer unless disabled, then runs `process_theories` against the parent logic. With the process cache enabled, an identical successful run can be skipped later. This is faster than rebuilding the layer session, but it still processes the whole file.

`outline` is a scaffold check:

```bash
./check_dev34_fast.sh outline dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

It runs the same path with `SKIP_PROOFS=1`, which is useful for statement plumbing and `sorry`-first skeletons. It is not a proof check.

`split-hot` and `slice-hot` are the important long-file accelerators:

```bash
./check_dev34_fast.sh split-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix
./check_dev34_fast.sh slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix
```

`split-hot` builds a generated prefix before the first matching line, then processes the generated tail from the target through the end of the original theory. `slice-hot` does the same prefix build, but processes only from the target through the line before the next top-level lemma, theorem, corollary, or proposition. For our current work, `slice-hot` is usually the best iteration command because the Section 3 packages are large but still top-level-bounded.

`focus` wraps `slice-hot` with named targets and a full-index scan:

```bash
./check_dev34_fast.sh focus mid-split-free
./check_dev34_fast.sh focus-status mid-split-free
./check_dev34_fast.sh focus-warm mid-split-free
```

The known focus targets are listed by:

```bash
./check_dev34_fast.sh focus-list
```

The focus list encodes the currently important Moise packages: graph branch/cycle work, mid-prefix split/free/fold/support/D42 work, prefix D44 work, and active `dev34` cycle/fan/semicircle work.

There are two graph-specific compatibility commands:

```bash
./check_dev34_fast.sh graph-focus "branch vertex local component"
./check_dev34_fast.sh graph-warm
```

These use the active graph target variables in the script. For the present
branch-local work, the more exact named focus target is usually better:

```bash
./check_dev34_fast.sh focus graph-branch-local
```

That command scans the full indexes for the target's scan phrase and then runs
the corresponding `slice-hot`.

`cache-through`, `cache-parents`, `cache-status`, and `cache-all` control layer heap stamps:

```bash
./check_dev34_fast.sh cache-status dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-parents dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-all
```

Use these when switching targets or after a broad statement change. `cache-all` is intentionally heavier; it is for preparing the whole stack, not for every edit.

## 3.1. Environment Flags

Several options are controlled by environment variables rather than command
line flags. The ones worth remembering are:

```text
TIMEOUT=120s
  Override the default timeout. Later layers have larger defaults.

FORCE_PROOFS=1
  Pass skip_proofs=false into builds and include that choice in cache digests.
  Use this for stricter milestone checks, not for every small edit.

SKIP_PROOFS=1
  Used by outline paths. This is for scaffold and statement checking only.

DEV34_FAST_PROC_CACHE=0
  Disable process-result skipping. Use when measuring actual runtime or when
  you want Isabelle to rerun an otherwise identical process_theories command.

DEV34_FAST_AUTOWARM=0
  Do not automatically warm parent heaps before hot/split checks.

DEV34_FAST_DEEP_AUTOWARM=0
  Warm only the immediate parent instead of the whole parent chain.

DEV34_FAST_SKIP_FRESH_TARGET=0
  Force a file-level process even when the whole target layer cache is fresh.

FORCE_CACHE=1
  Rebuild a layer cache even if its stamp currently matches.

DEV34_FAST_VERBOSE=1
  Print generated split-session details while running split-hot/slice-hot.
```

The default settings favor fast theorem iteration. The stricter settings are
for milestone verification and timing audits.

## 4. Why It Is Faster

The speedup comes from avoiding repeated replay of stable text. If the parent of a target file is already built, Isabelle can load the parent heap and process only the current layer. If a long target file is split before the active theorem, Isabelle can load a generated heap for the completed prefix and process only the target theorem. If an identical process run has already succeeded, the script can skip it entirely.

The biggest gain is in `slice-hot` and `focus` modes. A top-level theorem near the end of a 10,000-line theory no longer requires replaying the first 9,000 lines on every tiny edit. The first run still has to build the generated prefix. Later runs only rebuild the prefix if the copied prefix text, parent digest, split pattern, or proof settings change. When the edit is inside the target slice, the prefix remains fresh.

There are also smaller gains from using `rg` for hole and index scans, from choosing the smallest dirty layer automatically, and from skipping fresh process checks. These are not mathematically deep optimizations; they are engineering friction reductions. They matter because our actual work requires many small edits and immediate compile feedback.

The observed practical pattern is:

```text
Cold broad build: slowest; useful for milestone validation.
Hot file process: faster; good after ordinary file edits.
Slice-hot with warm prefix: fastest meaningful proof check for one theorem.
Holes/index/plan/status: near-instant; use constantly.
```

The script does not promise a fixed runtime. A target slice can still be slow if the theorem itself contains expensive automation, if the generated prefix is stale, if the parent heap is stale, or if the machine has lost Isabelle heap locality. But it changes the default iteration from "recheck too much" to "recheck the named package I am actually editing."

The first run after a target switch is often not representative. If output says
`cache build`, `cache warm-through`, or `building prefix cache`, the script is
buying future speed. The run to compare is the next one after the parent and
prefix are fresh. If the next run still spends most of its time after
`processing slice`, the slow part is inside the active theorem.

## 5. Correctness Boundaries

The fast cache is conservative about content hashes for the files it knows are relevant. It includes source checksums, `ROOT` files, parent digests, and proof-mode flags. That makes stale-cache false positives unlikely for the normal dev34 stack.

Still, several boundaries matter.

First, `holes`, `quick`, `plan`, `cache-status`, and `focus-status` are status commands. They do not prove anything. A fresh stamp means "this exact cached check previously succeeded", not "the whole project is currently fully certified."

Second, `outline` uses `skip_proofs=true`. It is good for finding syntax, statement, import, and dependency mistakes quickly. It is not good enough to close a proof package.

Third, `quick_and_dirty` and `skip_proofs` are development settings. The normal fast process path uses `quick_and_dirty` for speed. The final gate for a closed package should still include broader verification, and final project completion requires a real build policy consistent with the project rules.

Fourth, split theories are generated approximations of a region of a file. They work well for top-level theorem slices whose dependencies are above the split point. They are not a substitute for checking the original full theory after moving declarations, changing notation, adding global attributes, or changing something that affects later material outside the slice.

Fifth, pattern selection matters. `slice-hot FILE PAT` splits at the first `rg` match. If the pattern is too broad and matches a comment, an earlier helper, or an old generated name, the split point can be wrong. Use exact theorem names where possible. `focus` helps by encoding known good patterns.

Sixth, the cache is local. `.dev34_fast_cache` records local successful checks and generated helper theories. It should not be treated as a portable proof artifact. Another clone or machine needs to rebuild.

Seventh, generated split theories intentionally run with a generated session
that imports a prefix session. That means error line numbers can point into a
generated file under `.dev34_fast_cache/split-*`. The source text is copied
from the real theory, so the usual fix is still made in the original file. Use
the printed source line interval, or search the copied phrase in the original
file, when translating an error back.

Eighth, cache freshness is content based, but only over files the script knows
to hash. If we add new session files, move theory files, or change index
generation conventions, the script's file lists and session mappings may need
to be updated. This is why `CLAUDE.md` now explicitly reminds us to refresh
the index-generating scripts when session layout changes.

## 6. Downsides and Failure Modes

The main downside is cognitive overhead. There are many modes because there are several different loops: search, hole inventory, parent warming, file processing, split processing, focus processing, and milestone builds. The practical answer is to use a small default subset:

```bash
./check_dev34_fast.sh scan PATTERN
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus TARGET
./check_dev34_fast.sh slice-hot FILE EXACT_THEOREM_NAME
./check_dev34_fast.sh cache-parents FILE
```

The second downside is cache churn. A statement near the top of a large file invalidates split prefixes below it. This is correct, but it means a first check after such a change can again be expensive. The cache is best when the current edit is inside or after the target slice, not when the imports or early prefix text are changing every few minutes.

The third downside is disk clutter. `.dev34_fast_cache` accumulates split folders for old patterns and old prefixes. `./check_dev34_fast.sh cache-clean` removes the cache, but it also throws away useful warm state. A manual cleanup policy could be added later, but for now the clutter is acceptable because generated theories are small compared with the time saved.

The fourth downside is that a skipped process check can hide the fact that the user wanted a fresh timing measurement. Disable process-cache skipping with:

```bash
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh focus mid-split-free
```

Force a layer cache rebuild with:

```bash
FORCE_CACHE=1 ./check_dev34_fast.sh cache dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

Force proof checking options through the wrapper with:

```bash
FORCE_PROOFS=1 ./check_dev34_fast.sh prove dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

The fifth downside is that generated split sessions may fail for reasons the original file would not, especially if the target theorem depends on local context that is not preserved by a top-level split. The current splitter is designed for the style of these theories: top-level declarations between `begin` and `end`. It is not a general Isabelle document slicer.

The sixth downside is that the tool can make us over-focus. A fast theorem
slice is exactly what we want while closing one Moise theorem, but it can hide
breakage in later layers until we broaden the check. The antidote is procedural:
after a meaningful package closes, run a layer/cache-through check, regenerate
the indexes, and record the plan and result in the commit message.

## 7. Recommended Workflow for the Current Goal

For a Section 3 or Section 4 proof package, start with a scan:

```bash
./check_dev34_fast.sh scan "selected edge side witness free simplex"
```

Read the existing facts. Then edit with the `sorry`-first discipline from `CLAUDE.md`: add the statement or proof skeleton with `sorry`, compile immediately, and only then replace small batches of holes with bounded tactics.

For the current Section 3 split/free package, use:

```bash
./check_dev34_fast.sh focus mid-split-free
```

or, when bypassing the named target:

```bash
./check_dev34_fast.sh slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix
```

After a statement change, regenerate indexes:

```bash
bash gen_index.sh && ./gen_stmt_index.sh
```

Then use the indexes again before adding more helpers:

```bash
./check_dev34_fast.sh index "polygon disk chord subdisk induction"
```

When a package is plausibly closed, broaden the check:

```bash
./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh holes
```

For final completion, do not rely on the cache directory. Run the project-level build required by the main instructions, regenerate indexes, and commit the exact source changes. The cache is a way to get there faster; it is not the end condition.

## 8. Practical Answers

Is it faster? Yes, for focused iteration. The largest speedup comes from `slice-hot` after the generated prefix is warm. The first run may still be expensive, but subsequent runs avoid replaying the completed prefix. File-level `hot` is also faster than broad builds when the parent heap is fresh.

Does it make proofs weaker? The source proofs are unchanged. The risk is not proof weakness in the source; the risk is overinterpreting a narrow check. A slice check says the generated slice processed successfully against its generated prefix. It does not say every later theory in the project still works.

When should I clean it? Clean it when cache behavior seems confusing, when generated split directories are stale enough to waste attention, or when testing the script itself. Do not clean it during normal theorem iteration unless the cache is suspected to be wrong.

Which modes should I use most often? `scan`, `holes`, `focus`, `slice-hot`, and `hot`. Use `cache-through` at package boundaries. Use broad builds at milestones.

What is the main operational rule? Search first, edit narrowly, check with the narrowest meaningful proof command, then broaden verification before claiming a theorem package is closed.

## 9. Confidence Ladder

It is useful to treat the commands as a ladder rather than as synonyms.

The first rung is pure inspection. `quick`, `holes`, `dirty`, `plan`, and
`focus-status` do not ask Isabelle to validate new proof text. They answer
questions about where the remaining holes are, which files are dirty, and
whether a cache looks fresh. They are appropriate before editing and after
commits.

The second rung is search. `scan`, `index`, `names`, and `stmts` are part of
proof development because they prevent duplicate lemmas. They carry no proof
confidence by themselves, but they strongly affect whether the next proof edit
is pointed at the right existing fact.

The third rung is scaffold checking. `outline` and `focus-outline` use
`SKIP_PROOFS=1`. They are for the `sorry`-first phase: statement shape, imports,
local context, and generated split structure. They are not evidence that a
tactic replacement works.

The fourth rung is hot processing. `hot`, `proc`, `split-hot`, `slice-hot`, and
`focus` process proof text against a warmed parent. This is the main iteration
loop. A successful `slice-hot` result is meaningful for the active generated
slice, but it says nothing about later top-level declarations outside the slice.

The fifth rung is layer building. `auto`, `cache-through`, and explicit layer
commands such as `prefix-mid` check a wider session boundary. Use this after
statement changes, after closing a named package, or before trusting a sequence
of local slice successes.

The sixth rung is proof-forced building. `FORCE_PROOFS=1 ./check_dev34_fast.sh
prove FILE` is the wrapper's stricter milestone check. It is slower and should
be used when a theorem package is being claimed as closed, not after every
line-level edit.

The final rung is the project build policy outside the fast helper. The fast
cache is there to make this reachable without wasting days on duplicate
iteration, but the end condition for Sections 3-4 is still source-level closure:
no target `sorry`s, no stale generated indexes, and a broad Isabelle build that
matches the project's final verification requirement.

## 10. Timing Playbook

When an iteration still takes too long, first decide whether the slowness is a
cold-cache cost or an active-proof cost.

Cold-cache cost is visible when the output says it is building a parent cache or
a split prefix. This is expected after changing text before a split point,
changing parent layers, cleaning `.dev34_fast_cache`, or switching
`FORCE_PROOFS`. The fix is usually to let the warm step finish once, then keep
edits inside the active slice.

Active-proof cost is visible when the prefix is skipped but the slice processing
itself runs for a long time. That is a proof-engine problem, not a cache
problem. The remedy is to split the proof step, replace broad automation with
bounded methods such as `by (by100 blast)` or restricted `rule`/`erule` steps,
and use the indexes to find a sharper lemma.

Process-cache skips are useful but can hide timing measurements. If the question
is "did this exact content already pass?", leave the process cache on. If the
question is "how long does this proof actually take now?", run with:

```bash
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh slice-hot FILE PATTERN
```

For the current Section 3 work, the practical rhythm is:

```bash
./check_dev34_fast.sh scan "contact cover selected boundary edge"
./check_dev34_fast.sh slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy "theorem Theorem_GT_3_3"
```

When the local `Theorem_GT_3_3` bridge changes statements or moves facts above
the active split point, expect one slower prefix rebuild. When only the proof
inside the current bridge changes, the warmed `slice-hot` path should be much
faster than a layer build.
