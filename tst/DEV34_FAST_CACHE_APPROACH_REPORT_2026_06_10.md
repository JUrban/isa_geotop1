# `.dev34_fast_cache` and `check_dev34_fast.sh`: Report and Manual

Date: 2026-06-10

This report explains the fast-checking approach currently used for the
GeoTop Sections 3-4 work. It covers the local cache directory
`.dev34_fast_cache`, the driver script `check_dev34_fast.sh`, the many
available modes, where the speedup comes from, what is and is not certified by
each command, and the downsides that matter for closing the remaining Moise
Theorems 3.3, 3.4, 3.7, 4.2, and 4.4 packages.

The short answer is: yes, it is faster for focused proof iteration. The main
speedup comes from reusing finished Isabelle heaps and from building a
generated prefix of a long theory once, then processing only the active theorem
slice. It is not a replacement for final verification. It is a way to make the
edit-check loop short enough that we can keep proving the remaining hard
geometric steps without spending minutes on unchanged context every time.

As of this review, the local cache directory under `tst/.dev34_fast_cache` is
about 72 MB. It contains 153 generated `split-*` directories, 339 top-level
SHA-256 stamp files, and 5 process-cache stamp files. Those numbers are
descriptive, not goals. They show the normal scale of the current development
cache. The actual Isabelle heap images are managed by Isabelle because the
script builds with `system_heaps=true`; `.dev34_fast_cache` mostly stores
freshness stamps and generated split theories.

## 1. Why the Fast Cache Exists

The GeoTop Sections 3-4 proof stack is split into many local development
sessions:

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

This layering is useful because it lets us avoid rebuilding all of `GeoTop`
after every small edit. Without the fast helper, a verification attempt near
the end of `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` may replay thousands
of lines that have not changed. That cost is tolerable at milestones but too
expensive for the normal proof loop, especially when the current proof is still
being developed with `sorry`-first skeletons, sledgehammer probes, and bounded
tactic replacements.

The script addresses two different sources of repeated work.

First, it chooses the smallest useful parent heap. When editing a file in
`dev34_prefix_mid`, the parent logic is `GeoTop34PrefixGraphDirty`, not the
entire final `GeoTop34Dev` stack. If the `prefix-graph` heap is fresh, Isabelle
can load that heap and process the mid-prefix file from there.

Second, it can split a long theory at a named theorem or lemma. The generated
prefix before the target is built once. The active theorem slice is then
processed against that generated prefix session. For example, the named focus
target `mid-split-free` splits
`dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` at `theorem Theorem_GT_3_3`.
When the edit is inside that theorem package, the already-finished prefix above
it does not need to be replayed on every run.

This is the core idea: cache stable context, then recheck only the part that
changed.

## 2. The Cache Directory

The cache directory is local to `tst/`:

```text
tst/.dev34_fast_cache/
```

It is disposable. It is not a proof artifact and should not be treated as part
of the mathematical result. If removed, the source theories remain the source
of truth; the script will rebuild the needed cache entries as work continues.

There are four main kinds of cache entries.

### 2.1 Layer stamps

Layer stamps are small files such as:

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

Each stamp records a SHA-256 digest computed from the target name, the Isabelle
session name, the proof-forcing setting, and the source files that feed that
layer. The stamp does not contain the heap. It says that the corresponding
Isabelle heap was successfully built for the exact inputs represented by the
digest.

Freshness is content-based. If an input theory or `ROOT` file changes, the
digest changes and the layer is stale. If the digest still matches, the script
can skip rebuilding that layer.

### 2.2 Process stamps

Process stamps have names like:

```text
.dev34_fast_cache/proc-<hash>.sha256
```

They record that a file-level `process_theories` check succeeded against a
particular parent logic and parent digest. These stamps are useful when running
the same `hot` command twice without source changes. The second run can be
skipped because the previous process result is still fresh.

The important practical point is that process stamps are proof-loop
accelerators, not timing measurements. If the question is "how long does this
proof slice actually take now?", disable process-cache skipping:

```bash
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh focus mid-split-free
```

### 2.3 Split directories

Split directories are generated sessions:

```text
.dev34_fast_cache/split-<12hex>/
```

A typical split directory contains:

```text
ROOT
GeoTop_3_4_Prefix_Mid_Split_<key>_Prefix.thy
GeoTop_3_4_Prefix_Mid_Split_<key>_Slice.thy
```

The prefix theory copies the original theory up to the split point and imports
the real parent logic or a previous chained generated prefix. The slice theory
imports that prefix session and copies only the active top-level theorem or
lemma range. A full-tail check creates a `_Tail.thy` instead of checking only
one top-level slice.

The generated files explain why error locations sometimes point into
`.dev34_fast_cache/split-*`. The text is copied from the real source, so the
fix still belongs in the original theory file. The printed line interval from
the script is the guide for mapping the generated error back to the source.

### 2.4 Split stamps

Split stamps have names like:

```text
.dev34_fast_cache/split-<longhash>.sha256
```

These record freshness for generated split prefixes and split slice/tail
process runs. The digest includes the original file, split pattern, generated
`ROOT`, generated prefix or slice file, parent digest, chained prefix digest
when applicable, and proof-mode flags.

This means an edit before the split point invalidates the generated prefix,
while an edit inside the target theorem usually invalidates only the slice.
That distinction is the main reason the current loop is faster after the first
warm run.

## 3. Parent Heaps and Layer Mapping

The script has two closely related mappings.

`parent_context` maps a file to the Isabelle logic and `-d` directories used
by `process_theories`. For example:

```text
dev34_prefix_mid/* -> parent logic GeoTop34PrefixGraphDirty
dev34_prefix/*     -> parent logic GeoTop34PrefixMidDirty
dev34_core/*       -> parent logic GeoTop34OpenStarDirty
dev34/*            -> parent logic GeoTop34CoreDirty
```

`parent_target_for_file` maps a file to the cache layer that should be fresh
before processing that file:

```text
dev34_prefix_mid/* -> prefix-graph
dev34_prefix/*     -> prefix-mid
dev34_core/*       -> openstar
dev34/*            -> core
```

This is why a `focus mid-split-free` run can say that `prefix-graph` is fresh
and then jump directly to the generated prefix/slice work for the mid-prefix
file. It is not rebuilding the full dev34 stack.

The script can also warm the whole parent chain. By default
`DEV34_FAST_DEEP_AUTOWARM=1`, so if a parent is stale, the script walks through
the earlier layers and rebuilds the missing or stale pieces. That first cold
run can still be slow, but it is buying future fast runs.

## 4. The Commands Worth Knowing

The script exposes many modes because the development loop has several
different tasks: search, hole inventory, parent warming, file processing,
split processing, named target focus, and milestone builds. In practice, a
small subset handles most work.

### 4.1 Search and inventory

Use these frequently:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan "selected boundary edge"
./check_dev34_fast.sh index "polygon disk chord subdisk"
./check_dev34_fast.sh names "free_triangle"
./check_dev34_fast.sh stmts "finite linear graph"
```

`holes` greps the active dev34 target theories for `sorry` and `sledgehammer`.
It is a status map, not a build.

`scan` greps the generated indexes and the active target theories. This is the
command that answers the user's point about searching the full index. It should
be used before adding helpers and again when a proof direction stalls. It is
cheap, and it prevents wasted work.

`index`, `names`, and `stmts` narrow the search to index files. They are useful
when the pattern is noisy in source files.

### 4.2 Planning and cache status

Use these to understand what will be checked:

```bash
./check_dev34_fast.sh dirty
./check_dev34_fast.sh plan dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-status dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh focus-status mid-split-free
```

`plan` shows the parent logic and whether the reusable parent cache is fresh.
`focus-status` checks the named split target without building. It tells whether
the parent, split prefix, and slice process stamps are fresh.

### 4.3 Warming

Use these when switching targets or before a longer proof session:

```bash
./check_dev34_fast.sh warm dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh focus-warm mid-split-free
./check_dev34_fast.sh focus-prime mid-split-free mid-d42
./check_dev34_fast.sh cache-parents dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

`warm` prepares the parent heap for a file. `focus-warm` prepares the generated
prefix before a named focus target. `focus-prime` does that for one or more
named targets. The first warm pass can be expensive, but the next target check
is usually much faster.

### 4.4 Normal proof checks

These are the main iteration commands:

```bash
./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy "theorem Theorem_GT_3_3"
./check_dev34_fast.sh focus mid-split-free
```

`hot` processes the whole file against its parent heap. It is narrower than a
layer build but still replays the whole file.

`slice-hot` builds or reuses a generated prefix and processes only the next
top-level theorem/lemma slice beginning at the first pattern match. It is the
best loop when we are editing one hard theorem in a long file.

`focus` is a named wrapper around `slice-hot` plus a full-index scan. The named
focus targets currently include:

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

For the current Moise 3.3 work, the normal command is:

```bash
TIMEOUT=240s ./check_dev34_fast.sh focus mid-split-free
```

### 4.5 Scaffold checks

Use these only for `sorry`-first structure checks:

```bash
./check_dev34_fast.sh outline dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh focus-outline mid-split-free
```

These paths set `SKIP_PROOFS=1`. They are useful after adding a statement
skeleton with `sorry`, but they do not validate proof replacements.

### 4.6 Broader checks

Use these at package boundaries:

```bash
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh auto dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
FORCE_PROOFS=1 ./check_dev34_fast.sh prove dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

`cache-through` builds all cache layers through the target layer, skipping
fresh layers. `auto` builds the smallest dirty or explicit layer. `prove`
forces proof checking options through the wrapper. These are slower than
`focus`, but they provide a wider confidence boundary.

The final end condition is still broader than the fast helper: all target
`sorry`s closed, indexes regenerated, and a real Isabelle build consistent
with the project instructions.

## 5. Environment Options

Important environment variables:

```text
TIMEOUT=240s
  Override command timeout. Useful for current hard targets.

FORCE_PROOFS=1
  Pass proof-forcing options into the wrapper and include the setting in cache
  digests. Use for milestone checks, not every tiny edit.

SKIP_PROOFS=1
  Used by outline modes. Good for skeleton checking only.

DEV34_FAST_PROC_CACHE=0
  Disable skipping of previously successful process runs. Use when measuring
  actual runtime or when a truly fresh process check is wanted.

DEV34_FAST_AUTOWARM=0
  Do not automatically warm parent heaps before hot or split checks.

DEV34_FAST_DEEP_AUTOWARM=0
  Warm only the immediate parent target instead of the whole parent chain.

DEV34_FAST_SKIP_FRESH_TARGET=0
  Process a file even if the whole target layer cache is already fresh.

FORCE_CACHE=1
  Rebuild a layer cache even when its stamp matches.

DEV34_FAST_VERBOSE=1
  Print generated split-session details.
```

The default settings favor fast theorem iteration. The stricter settings are
for milestone validation, debugging the wrapper, or measuring runtime.

## 6. Is It Faster?

For the current workflow, yes. The gain is largest when all of these are true:

1. The target theorem is late in a large file.
2. The edit is inside the target theorem or a nearby local helper.
3. The parent heap is fresh.
4. The generated split prefix is fresh.
5. The active theorem slice does not contain a tactic that itself takes
   minutes.

The expected timing pattern is:

```text
Cold parent build: slow; prepares reusable heap state.
Cold split-prefix build: still slow; prepares the prefix before the target.
Warm slice check: much faster; checks only the active theorem slice.
Fresh process-cache rerun: near-instant; skips an identical successful run.
```

This explains why a first run after a target switch may still take a long time.
If output says `cache build`, `cache warm-through`, or `building prefix cache`,
the script is doing setup work. The meaningful comparison is the next run after
the prefix and parent are fresh.

If output says `skipped prefix cache` and then spends a long time on
`processing slice`, the cache is not the bottleneck. The bottleneck is inside
the active proof text. At that point the right response is to split the proof
more finely, replace broad automation with bounded methods such as
`by (by100 blast)` or explicit rule steps, and search the full index for
sharper facts.

## 7. Downsides and Risks

The main downside is that there are many modes. That is manageable if we use a
small default set:

```bash
./check_dev34_fast.sh scan PATTERN
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus TARGET
./check_dev34_fast.sh focus-status TARGET
./check_dev34_fast.sh cache-through FILE
```

The second downside is cache invalidation. Edits above a split point invalidate
the generated prefix. This is correct, but it means a large statement move or
early-helper edit can make the next run expensive again.

The third downside is local clutter. The cache accumulates split directories
for old targets and old patterns. `./check_dev34_fast.sh cache-clean` removes
the directory, but that also discards useful warm state. Normal theorem
iteration should not clean it unless the cache behavior is confusing or the
script itself is being debugged.

The fourth downside is narrow confidence. A successful `focus mid-split-free`
means the generated slice for the named target processed against its generated
prefix. It does not mean later theories or other sections still build. That is
why package-level progress should be followed by `cache-through`, hole scans,
index regeneration, and eventually a broader build.

The fifth downside is pattern sensitivity. `slice-hot FILE PATTERN` uses the
first `rg` match. If the pattern is too broad and matches a comment or earlier
helper, the split point is wrong. Named `focus` targets reduce this risk by
encoding exact patterns for the known hard proof packages.

The sixth downside is script maintenance. The script hashes the files and
session structure it knows about. If we add new session files, move theory
files, or change index generation conventions, `check_dev34_fast.sh`,
`gen_index.sh`, and `gen_stmt_index.sh` need to be reviewed together. This
matches the current instruction to refresh the index scripts when session
files change.

## 8. Correctness Boundaries

The cache is conservative about local freshness, but it is not a proof system.
The source theories and Isabelle are the proof system.

The commands form a confidence ladder:

```text
holes / scan / plan / focus-status
  Inspection only. No proof validation.

outline / focus-outline
  Statement and skeleton validation with skip_proofs=true.

hot / slice-hot / focus
  Main proof-loop validation for a file or generated theorem slice.

cache-through / auto
  Wider layer validation through a target layer.

FORCE_PROOFS=1 prove
  Stricter wrapper-level milestone check.

Full project build
  Final confidence boundary for the source tree.
```

The important operational rule is to match the command to the claim. A slice
check is enough to say "this edit compiles in the active slice." It is not
enough to say "Moise Section 3 is closed." A theorem package closure needs a
broader check and the live hole map must go down.

## 9. Recommended Workflow for the Remaining Moise Work

For the active Theorem 3.3 split/free package:

```bash
./check_dev34_fast.sh scan "subdisk free triangle carrier count"
TIMEOUT=240s ./check_dev34_fast.sh focus-status mid-split-free
TIMEOUT=240s ./check_dev34_fast.sh focus mid-split-free
```

Before adding a helper, search the full index. If an exact lemma exists, use
it. If no exact lemma exists, add only the next faithful Moise bridge, first
with `sorry`, then compile immediately. After that, replace small groups of
`sorry`s with bounded proof methods or sledgehammer suggestions.

After a meaningful change:

```bash
bash gen_index.sh && bash gen_stmt_index.sh
./check_dev34_fast.sh holes
git commit
```

The commit message should carry the plan and the outcome: which Moise theorem
was targeted, which bridge was attempted, what checked, what remained open,
and whether a previous strategy had to be corrected. This is better than
continually appending to progress reports because the history remains tied to
the source changes.

When a named package closes:

```bash
TIMEOUT=240s ./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh holes
bash gen_index.sh && bash gen_stmt_index.sh
```

Then move to the next live hole using the same pattern.

## 10. Bottom Line

The `.dev34_fast_cache` approach is a local development accelerator. It gives
fast feedback by separating stable parent context, stable in-file prefixes, and
the active theorem slice. It is faster when used on a named target with a warm
parent and a warm split prefix. It has downsides: extra modes, local clutter,
pattern sensitivity, narrow confidence, and maintenance requirements when the
session layout changes.

The right use is not to trust it blindly. The right use is to run it constantly
for focused proof work, search the full index frequently, broaden checks at
package boundaries, regenerate the indexes after source changes, and reserve
full builds for milestone certification. Used that way, it directly addresses
the 2-3 minute iteration problem without changing the proof obligations we
still have to close.
