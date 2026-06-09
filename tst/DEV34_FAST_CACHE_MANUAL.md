# Manual: `.dev34_fast_cache` and `check_dev34_fast.sh`

Date: 2026-06-09

This manual explains the fast-checking workflow used for the Moise Sections 3-4
`dev34` proof work. It is not a progress report. It is a technical description
of the cache, the wrapper script, the intended iteration loop, the performance
tradeoffs, and the failure modes.

The short version is:

* `check_dev34_fast.sh` wraps Isabelle builds, `process_theories`, full-index
  `rg` searches, hole scans, and generated split theories.
* `.dev34_fast_cache/` stores freshness stamps and generated split sessions.
  The durable Isabelle heaps are stored by Isabelle itself because the script
  builds sessions with `-o system_heaps=true`.
* The speedup comes from avoiding replay of stable parent sessions and, for
  large files, avoiding replay of stable earlier text in the same file.
* The fastest modes are development checks. They are not final certification.
  A closed package still needs broader checks, a hole scan, regenerated indexes,
  and eventually proof-forced or real-session validation.

At the current checkpoint, `.dev34_fast_cache` is about 66 MB in the working
tree, with 318 top-level stamp files, 144 generated split directories, and 751
files at depth two. `cache-plan dev34/GeoTop_3_4.thy` reports `pre`,
`prefix-base`, `prefix-graph-cache`, and `prefix-graph` fresh, and
`prefix-mid` onward stale or missing. That means the cache is useful for
`prefix-mid` work only after warming the relevant parent chain, while earlier
graph and prefix-base work can still reuse existing heaps.

## 1. Why This Exists

The ordinary Isabelle build loop is too expensive for the current shape of the
project. A one-line proof edit near the bottom of `dev34/GeoTop_3_4.thy` sits
behind a large stack of local theory files. A full build gives strong
confidence, but it spends most of the iteration time replaying material that did
not change.

The remaining work is also not evenly distributed. It is concentrated in a
small number of Moise theorem packages: Section 3 polygon disk/fold transfer,
the D42 arc-separation argument, the D44 two-arc brick transfer, graph
branch/cycle cut facts, and the endpoint fan/semicircle material in the final
`dev34` layer. For that kind of work, the productive loop is:

1. Search the full theorem/statement indexes and local target files.
2. Edit one helper lemma or one theorem slice.
3. Check only that slice against a cached parent context.
4. Run a broader downstream check before committing.
5. Regenerate indexes after adding or moving declarations.

`check_dev34_fast.sh` automates that loop. It bakes the layer order into one
place, gives named focus targets, stores conservative freshness hashes, and
generates synthetic split theories when a single file is too large to replay on
every edit.

The important limitation is that the script is an iteration accelerator. It
does not choose the mathematical proof. It does not replace the book-aligned
proof strategy, full-index search discipline, or final validation.

## 2. The Layer Model

The script knows this dependency stack:

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

Each layer maps to a session. Examples:

```text
pre                 GeoTopPre3Dirty
prefix-base         GeoTop34PrefixBaseDirty
prefix-graph-cache  GeoTop34PrefixGraphCacheDirty
prefix-graph        GeoTop34PrefixGraphDirty
prefix-mid          GeoTop34PrefixMidDirty
prefix              GeoTop34PrefixDirty
core                GeoTop34CoreDirty
dev34               GeoTop34Dev
```

The key operational rule is that an edited file is processed against the heap
for its parent layer:

```text
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
  parent logic: GeoTop34PrefixGraphDirty
  reusable parent target: prefix-graph

dev34_prefix/GeoTop_3_4_Prefix.thy
  parent logic: GeoTop34PrefixMidDirty
  reusable parent target: prefix-mid

dev34/GeoTop_3_4.thy
  parent logic: GeoTop34CoreDirty
  reusable parent target: core
```

This is where most of the speed comes from. If the parent target is fresh, a
localized check does not replay earlier layers. If the parent target is stale,
the script can warm it, but that is a real build and may take time.

Useful inspection commands:

```bash
./check_dev34_fast.sh plan dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-plan dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-plan dev34/GeoTop_3_4.thy
```

`plan` tells you the immediate parent context for a file. `cache-plan` walks the
layer chain through the target and reports which stamps are fresh.

## 3. What the Cache Directory Contains

`.dev34_fast_cache/` contains three main classes of files.

First, layer freshness stamps:

```text
.dev34_fast_cache/pre.sha256
.dev34_fast_cache/prefix-graph.sha256
.dev34_fast_cache/prefix-mid.sha256
.dev34_fast_cache/core.sha256
.dev34_fast_cache/dev34.sha256
```

These files are only hashes. They are not heaps. A stamp says that the
corresponding Isabelle session heap was built from exactly the source set,
session name, and proof options represented by that digest. The actual heap is
managed by Isabelle because every build uses:

```bash
-o system_heaps=true
```

Second, process-theory stamps:

```text
.dev34_fast_cache/proc-<hash>.sha256
```

These record a successful `process_theories` run for a particular file, parent
logic, parent digest, ROOT hash, and proof/skip setting. If the file changes, or
the parent cache changes, or `FORCE_PROOFS`/`SKIP_PROOFS` changes, the process
stamp no longer matches.

Third, generated split sessions:

```text
.dev34_fast_cache/split-<short-hash>/ROOT
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Prefix.thy
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Slice.thy
.dev34_fast_cache/split-<short-hash>/<Base>_Split_<hash>_Tail.thy
```

These are synthetic Isabelle theories. A split check finds a pattern in a real
theory, writes a prefix theory containing everything before the pattern, builds
that prefix as its own temporary session, then processes either the next
top-level declaration (`slice-hot`) or the remainder of the file (`split-hot`).

The split directories are deliberately visible on disk. That makes the system
debuggable: when a split behaves oddly, you can open the generated `Prefix`,
`Slice`, `Tail`, or `ROOT` file and see exactly what Isabelle was asked to
process.

## 4. Freshness and Invalidation

Freshness is file-hash based, not semantic. The script does not try to know that
a change was harmless. It hashes enough context to avoid reusing stale results
when the relevant source or option set changed.

For a layer stamp, `cache_digest` includes:

* target layer name;
* Isabelle session name;
* `FORCE_PROOFS` setting;
* SHA-256 hashes of every source file up through that layer.

For a `process_theories` stamp, `proc_digest` includes:

* target file path;
* parent logic;
* `FORCE_PROOFS` and `SKIP_PROOFS`;
* target file hash;
* the target directory `ROOT` hash, if present;
* parent target name;
* parent target digest.

For split checks, the digest includes:

* real source file;
* split pattern;
* optional chained split pattern;
* proof/skip settings;
* generated prefix file hash;
* generated slice/tail file hash;
* generated `ROOT` hash;
* parent target digest;
* chained-prefix digest, when chaining is used.

The practical consequences are:

* editing a proof body invalidates the active process or split stamp;
* editing text before a split point invalidates the generated prefix;
* editing a parent layer invalidates child checks;
* switching `FORCE_PROOFS=1` or `SKIP_PROOFS=1` uses different cache keys;
* renaming or duplicating a pattern can move the split point, so patterns should
  be theorem names or otherwise distinctive strings.

This conservative invalidation is the right tradeoff. It may rebuild more than
strictly necessary after harmless edits, but it should not silently reuse a
result after a relevant source change.

## 5. The Main Modes

The fastest status command is:

```bash
./check_dev34_fast.sh holes
```

It runs `rg` for `sorry` and `sledgehammer` markers across the target `dev34`
layers. It is not a build, but it is the quickest honest hole map.

The index/search commands are:

```bash
./check_dev34_fast.sh index "component_at"
./check_dev34_fast.sh names "broken_line"
./check_dev34_fast.sh stmts "frontier"
./check_dev34_fast.sh scan "polygon arc component frontier"
./check_dev34_fast.sh grep "Theorem_GT_4_2"
```

`scan` and `grep` search both generated indexes and target theory files. This
matters because many useful facts are already present, and full-index search is
often cheaper than inventing a new lemma.

The parent/cache commands are:

```bash
./check_dev34_fast.sh plan FILE
./check_dev34_fast.sh cache-plan FILE
./check_dev34_fast.sh cache-parents FILE
./check_dev34_fast.sh cache-through FILE
./check_dev34_fast.sh cache-all
./check_dev34_fast.sh cache-clean
```

`cache-parents` warms reusable parents for a file. `cache-through` warms every
layer through the selected target. `cache-all` attempts every known layer.
`cache-clean` removes local freshness stamps; it does not need to delete the
generated split directories to invalidate the cache, because the stamps control
reuse.

The file-processing commands are:

```bash
./check_dev34_fast.sh proc FILE
./check_dev34_fast.sh hot FILE
./check_dev34_fast.sh outline FILE
```

`hot` is an alias for `proc`: it processes the whole file against its cached
parent logic and auto-warms the parent unless disabled. `outline` runs through
the same path with `SKIP_PROOFS=1`, so it is useful for syntax/scaffold checks
after inserting a `sorry`-first proof skeleton. It is not proof validation.

The split commands are:

```bash
./check_dev34_fast.sh slice-hot FILE PATTERN
./check_dev34_fast.sh split-hot FILE PATTERN
./check_dev34_fast.sh split-warm FILE PATTERN
```

`slice-hot` checks only the next top-level theorem/lemma/corollary/proposition
starting at the first match of `PATTERN`. `split-hot` checks from the pattern
through the end of the file. `split-warm` builds the generated prefix but does
not process the slice/tail.

## 6. Named Focus Targets

Focus targets encode the theorem packages that have been active in Sections
3-4. The current list is:

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

Useful focus commands:

```bash
./check_dev34_fast.sh focus-list
./check_dev34_fast.sh focus-status mid-d42
./check_dev34_fast.sh focus mid-d42
./check_dev34_fast.sh focus-full mid-d42
./check_dev34_fast.sh focus-warm mid-d42
./check_dev34_fast.sh focus-prime mid-d42 prefix-d44
./check_dev34_fast.sh focus-warm-all
```

A `focus` run first performs a full-index/source scan with a target-specific
phrase, then runs `slice-hot` on the mapped theorem. `focus-full` does the same
scan and then runs `split-hot`. `focus-status` is no-build status for the
generated prefix/slice caches.

Some focus targets use chained prefixes. For example, `mid-d42` maps to
`Theorem_GT_4_2` in `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` and chains
through `Theorem_GT_3_7`. The purpose is to avoid repeatedly building one huge
synthetic prefix in a large file. The script first warms an earlier prefix, then
builds the later prefix on top of that temporary session.

Chaining is also used by `dev34-semicircle`, which chains through the endpoint
fan target before checking the later semicircle theorem.

## 7. Options and Environment Variables

The script has a small number of important environment switches:

```bash
TIMEOUT=180s ./check_dev34_fast.sh slice-hot FILE PATTERN
FORCE_PROOFS=1 ./check_dev34_fast.sh prove FILE
SKIP_PROOFS=1 ./check_dev34_fast.sh proc FILE
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh hot FILE
DEV34_FAST_AUTOWARM=0 ./check_dev34_fast.sh hot FILE
DEV34_FAST_DEEP_AUTOWARM=0 ./check_dev34_fast.sh hot FILE
DEV34_FAST_SKIP_FRESH_TARGET=0 ./check_dev34_fast.sh hot FILE
DEV34_FAST_VERBOSE=1 ./check_dev34_fast.sh split-warm FILE PATTERN
```

`TIMEOUT` controls the timeout used by most commands. The default is `90s`, but
later layer builds have larger target-specific defaults: `facts` uses `120s`,
`workfacts`/`linkfacts` use `150s`, `graphfacts`/`graphwork` use `180s`,
`openstar`/`core` use `210s`, and `dev34` uses `240s`.

`FORCE_PROOFS=1` sets `skip_proofs=false` for builds and creates a distinct
cache key. Use it when a package is supposed to be genuinely closed, not for
every edit.

`SKIP_PROOFS=1` affects `process_theories` paths and is used by `outline` and
`focus-outline`. It is a scaffold check.

`DEV34_FAST_PROC_CACHE=0` disables process/split process stamp reuse. This is
useful if you want to force Isabelle to rerun the current slice while still
reusing parent heaps.

`DEV34_FAST_AUTOWARM=0` stops automatic parent warming. This is useful for a
quick "tell me what is stale" run that should not start a build.

`DEV34_FAST_DEEP_AUTOWARM=0` warms only the immediate parent target rather than
walking the whole parent chain.

`DEV34_FAST_SKIP_FRESH_TARGET=0` makes `proc` run even if the whole target layer
stamp is fresh.

`DEV34_FAST_VERBOSE=1` prints the generated split session stanza, which helps
debug imports and temporary sessions.

## 8. Is It Faster?

Yes, when used for its intended loop.

The biggest win is when the parent chain is fresh. For example, checking a
single theorem in `dev34/GeoTop_3_4.thy` can reuse `GeoTop34CoreDirty` instead
of replaying all earlier `dev34` layers. Checking a theorem in
`dev34_prefix_mid` can reuse `GeoTop34PrefixGraphDirty`.

The second win is within a large file. Once a generated prefix is built, a
repeat `slice-hot` only needs to process the current slice, unless the text
before the split point changed. If the slice is unchanged too, the process stamp
lets the command return immediately with a "skipped ... fresh process cache"
message.

The speedup is not magic. These cases remain expensive:

* the parent layer is stale and must be rebuilt;
* the slice itself has slow automation;
* the split pattern is near the bottom and the prefix has never been warmed;
* final proof-forced validation is required;
* a change in an early layer invalidates many child stamps.

The right expectation is that the script removes unrelated replay cost. It does
not make a hard local proof cheap, and it does not eliminate real dependencies.

## 9. Downsides and Failure Modes

The main risk is mistaking a fast development check for final certification.

`slice-hot` checks one generated theorem slice. It is excellent for "does this
proof body compile in this context?" It does not prove that later declarations
in the real file still compile. After changing a helper used downstream, run
`split-hot`, `hot`, or a layer build before committing.

Generated split prefix sessions use `quick_and_dirty` and `skip_proofs`:

```text
options [system_heaps, quick_and_dirty, skip_proofs, timeout = 240]
```

That is intentional. The generated prefix exists to accelerate local iteration,
not to certify the prefix independently. The real session remains the authority.

`outline`, `focus-outline`, and any `SKIP_PROOFS=1` run are syntax/scaffold
checks only. They are valuable under the `CLAUDE.md` workflow because new proof
structure should be written with `sorry` first and compiled immediately. But
they do not validate proof terms.

Pattern ambiguity can waste time or check the wrong slice. `slice-hot FILE
frontier` is risky. `slice-hot FILE
geotop_polygon_arc_opposite_boundary_theta_component_split_prefix` is much
better. The split code uses the first `rg` match.

The cache can grow. At 66 MB it is small compared with the Isabelle heap store,
but repeated experimentation creates more split directories. `cache-clean`
removes stamps but leaves generated files. That is usually fine; stale generated
files are ignored unless their stamps match. A manual cleanup of old
`split-*` directories is possible when disk use becomes annoying, but it is not
part of ordinary proof work.

The script is repository-specific. If new dev34 session files are added or a
layer moves, these sections of `check_dev34_fast.sh` must be updated together:

```text
target_theories
hole_theories
layer_rank
target_rank
target_layer_dir
target_session
layer_targets
target_timeout
target_dirs_args
target_source_files
parent_context
parent_target_for_file
focus_target_names / focus_target
focus_chain_pattern / split_default_chain_pattern
```

The index scripts also matter. `gen_index.sh` and `gen_stmt_index.sh` now track
ROOT files, session/signature files, local advice/report notes, and bounded
session transcripts. After new session files or advice reports appear, regenerate
both indexes so `scan`, `index`, `names`, and `stmts` search the right universe.

## 10. Recommended Workflows

For ordinary proof iteration:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan "words from the current goal"
./check_dev34_fast.sh focus-status mid-d42
./check_dev34_fast.sh focus mid-d42
```

For a known theorem:

```bash
./check_dev34_fast.sh scan "broken line component frontier"
./check_dev34_fast.sh slice-hot \
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
  geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
```

For checking downstream consequences in the same file:

```bash
./check_dev34_fast.sh split-hot \
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
  theorem\ Theorem_GT_4_2
```

For warming after a parent change:

```bash
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

Before a proof-progress commit:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh slice-hot FILE DISTINCTIVE_PATTERN
bash gen_index.sh
bash gen_stmt_index.sh
git diff --check -- FILE THEOREMS_AND_DEFS.txt THEOREMS_AND_DEFS.md STMT_INDEX.txt INDEX_THEORIES.txt
```

Before claiming a package closed, add a broader check appropriate to the layer:

```bash
./check_dev34_fast.sh split-hot FILE DISTINCTIVE_PATTERN
./check_dev34_fast.sh hot FILE
FORCE_PROOFS=1 ./check_dev34_fast.sh prove FILE
```

The exact command depends on the package and how much downstream material could
depend on the changed theorem.

## 11. How It Fits the Current Moise Work

For D42 (`Theorem_GT_4_2` in `dev34_prefix_mid`), the useful loop is:

```bash
./check_dev34_fast.sh scan "Theorem_GT_4_2 broken line component frontier theta"
./check_dev34_fast.sh focus-status mid-d42
./check_dev34_fast.sh focus mid-d42
```

The focus target chains through `Theorem_GT_3_7`, which avoids repeatedly
building the entire prefix-mid file from the beginning for one Section 4 theorem.

For D44 (`prefix-d44`), the focus target is the two-disjoint-endpoint-arcs brick
component transfer lemma in `dev34_prefix`. It depends on `prefix-mid`, so a
stale `prefix-mid` parent means the first iteration will have to warm that
parent before localized checks become cheap.

For endpoint fan and semicircle work in `dev34`, the useful loop is:

```bash
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus dev34-semicircle
```

`dev34-semicircle` chains through the endpoint fan target because it appears
later in the same large final file.

The current cache status, with `prefix-mid` onward stale, says that immediate
D42 work should expect a warming cost unless the relevant split prefix is still
usable through the fresh `prefix-graph` parent. That is still better than a
blind full build, and it keeps the cost explicit.

## 12. Bottom Line

The mental model is:

```text
full-index grep     finds existing facts before new lemmas are invented
parent heap cache   avoids rebuilding stable earlier layers
process stamps      skip identical whole-file process_theories checks
split prefix cache  avoids replaying stable earlier text in one large file
slice-hot           validates one local theorem edit quickly
split-hot/hot       checks downstream or whole-file consequences
final build/prove   certifies closure when a package is actually done
```

Used this way, the cache makes iteration materially faster and more disciplined.
It turns "wait for the whole project" into "pay for the changed proof slice plus
any genuinely stale parent." The downsides are manageable as long as fast modes
are treated as development checks, pattern names are precise, indexes are kept
fresh, and broader validation is run before a theorem package is called closed.
