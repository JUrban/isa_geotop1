# Manual: `.dev34_fast_cache` and `check_dev34_fast.sh`

Date: 2026-06-10

This note explains the fast-checking workflow used for the GeoTop Section
3-4 development. It is written as a practical manual for the current
`codex-dev34-cache` branch, not as a general Isabelle guide. The two main
objects are:

* `.dev34_fast_cache/`, a local, disposable cache directory under `tst/`.
* `check_dev34_fast.sh`, the shell driver that computes cache freshness,
  warms Isabelle parent heaps, builds temporary split theories, searches the
  full index, and runs focused `process_theories` checks.

The core idea is simple: avoid rebuilding or re-processing all of GeoTop after
each proof edit. The script turns the large Section 3-4 development into a
chain of smaller Isabelle sessions and then adds two more levels of caching:
whole-layer heap stamps and temporary split/slice proof checks. The result is
that many proof iterations take seconds instead of minutes, provided the
parent heaps and split prefixes are fresh.

This is a speed tool, not a replacement for final verification. The final
goal is still zero target `sorry`s plus a successful real build.

As of this review, the local cache directory is about 71 MB, with 153
generated split directories and 338 top-level SHA-256 stamp files. Those
numbers are not a target; they just show the expected scale. Most of the
large proof state is still in Isabelle heap images outside this directory.
`.dev34_fast_cache` mostly records freshness and stores generated theory
fragments.

## 1. Why This Exists

The GeoTop Section 3-4 files are large, and the difficult proof obligations
are usually located late in a theory. A plain Isabelle build has to replay a
large amount of already-finished context before it reaches the edited proof.
That is reasonable for certification but painful for interactive iteration.

The fast script solves two separate problems:

1. It reduces the amount of Isabelle context that must be replayed after a
   small edit.
2. It records enough content hashes to skip checks that were already run
   against the same inputs.

The most important practical distinction is between a parent heap and a split
prefix:

* A parent heap is an Isabelle heap image for a completed layer before the
  current file. For example, when editing
  `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`, the parent logic is
  `GeoTop34PrefixGraphDirty`.
* A split prefix is a temporary theory generated from the same file up to a
  selected line. For example, when checking only `Theorem_GT_3_3`, the script
  may create a new theory that contains all of
  `GeoTop_3_4_Prefix_Mid.thy` before the theorem, build it once, and then
  process only the theorem slice against that temporary heap.

The first level avoids rebuilding earlier files. The second level avoids
replaying the earlier part of the same large file on every edit.

## 2. The Layer Model

`check_dev34_fast.sh` knows the active Section 3-4 stack in dependency order:

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

Each layer has a corresponding target name such as `prefix-mid`, `prefix`, or
`dev34`, and a corresponding Isabelle session such as
`GeoTop34PrefixMidDirty` or `GeoTop34Dev`. The script maps files to parent
sessions with `parent_context`. For example:

```text
file in dev34_prefix_mid/
  parent logic: GeoTop34PrefixGraphDirty
  directories: -d . -d dev34_pre -d dev34_prefix_base
               -d dev34_prefix_graph -d dev34_prefix_mid
```

The naming is a little counterintuitive: a file's parent logic is the session
that contains everything before that file's own layer. That is exactly what
`process_theories` needs when it checks a single file.

The script also maps each file to a reusable parent cache target. For
`dev34_prefix_mid/*`, the parent target is `prefix-graph`. For
`dev34/GeoTop_3_4.thy`, the parent target is `core`. This lets `hot` and
`slice-hot` automatically warm the right heap before processing the edit.

## 3. What Is Stored in `.dev34_fast_cache`

The cache directory contains several kinds of files.

### 3.1 Layer stamps

Files like these are layer freshness stamps:

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

Each stamp stores a digest computed from:

* the target name;
* the Isabelle session name;
* whether `FORCE_PROOFS=1` was used;
* all source files that feed the target up to that layer, including relevant
  `ROOT` files and `.thy` files.

If the digest still matches, the script treats the heap as fresh. The heap
itself is managed by Isabelle through `system_heaps=true`; the `.sha256` file
is the script's own record that the heap corresponds to the current source
state.

### 3.2 Process stamps

Files named `proc-<hash>.sha256` record focused `process_theories` checks.
They are not Isabelle heaps. They say: this single file was processed against
this parent logic with these options and this file content, and the check
succeeded.

The process digest includes:

* the checked file;
* the parent target and parent digest;
* the parent logic;
* the file's content hash;
* the layer `ROOT` file hash, when present;
* `FORCE_PROOFS` and `SKIP_PROOFS`.

This is useful when rerunning `hot` after no relevant content changed. The
script can skip the process step and print that the process cache is fresh.

### 3.3 Split directories

Directories named `split-<12hex>/` are temporary Isabelle sessions generated
by `split-hot`, `slice-hot`, and the focus commands. A typical directory
contains:

```text
ROOT
GeoTop_3_4_Prefix_Mid_Split_<key>_Prefix.thy
GeoTop_3_4_Prefix_Mid_Split_<key>_Slice.thy
```

For full-tail checks, it may contain a `_Tail.thy` instead of, or in addition
to, a `_Slice.thy`.

The generated prefix theory imports the normal parent logic or a previous
chained split prefix. It then copies the original theory from the beginning
through the line immediately before the requested pattern. The generated slice
theory imports the prefix session and copies only the selected theorem or
lemma range.

This is the main source of the very large speedup for late-file proofs.
Instead of replaying thousands of lines each time, Isabelle reuses the split
prefix heap and checks only the active slice.

### 3.4 Split stamps

Files named `split-<longhash>.sha256` record freshness for generated split
prefixes, slices, and tails. The split prefix digest includes:

* the original file path;
* the selected pattern;
* the generated prefix theory and generated `ROOT`;
* the parent cache digest;
* any chained prefix digest;
* `FORCE_PROOFS`.

The slice or tail digest additionally includes:

* the generated slice or tail file content;
* the prefix digest;
* `SKIP_PROOFS`;
* `FORCE_PROOFS`.

Because these keys are content-based, small edits before a target invalidate
the relevant split prefix. Small edits inside the current theorem usually only
invalidate the slice process, not the parent heap.

## 4. The Main Modes

The script has many modes, but they fall into a few categories.

### 4.1 Inventory and search modes

Use these constantly:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan "polygon disk boundary free simplex"
./check_dev34_fast.sh index "free_2_simplex"
./check_dev34_fast.sh names "boundary_subdivision"
./check_dev34_fast.sh stmts "finite linear graph"
./check_dev34_fast.sh loop "selected edge transfer"
```

`holes` runs `rg` over the target theory set for `sorry` and `sledgehammer`.
This is intentionally cheap.

`scan` searches both generated indexes and all target dev34 theories. This is
the mode that answers the recurring question "did we already prove something
close to this?" It should be used before adding new lemmas.

`index` and `names` search `THEOREMS_AND_DEFS.txt`; `stmts` searches
`STMT_INDEX.txt`. These are generated by `gen_index.sh` and
`gen_stmt_index.sh`, which now include local imports, advice/report notes, and
bounded session transcript inputs in their invalidation signatures. That is
why full-index grep is often better than hand-browsing nearby files.

`loop` combines a full-index/source scan, hole inventory, and dirty-file plan.
`loop --hot` also runs a hot check.

### 4.2 Whole-layer cache modes

These build or inspect reusable layer heaps:

```bash
./check_dev34_fast.sh cache-status dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-parents dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh cache-all
```

`cache-parents` warms only the reusable parent layers for the target file.
`cache-through` builds each layer through the dirty or explicit target,
skipping fresh ones. `cache-all` does this for the whole known dev34 chain.

The script uses `system_heaps=true`, so these modes are intended to create
real Isabelle heaps that can be reused across subsequent checks.

### 4.3 File processing modes

These process a changed or explicit theory against its parent heap:

```bash
./check_dev34_fast.sh proc dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh outline dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

`hot` is the everyday alias. It auto-warms parents unless disabled, then runs
`process_theories`. If the process stamp is fresh, it skips the run.

`outline` is the scaffold mode. It uses `SKIP_PROOFS=1`, so it is useful for
checking statement shape, imports, syntax, and theorem structure quickly. It
does not validate proof bodies in the normal way.

### 4.4 Split and slice modes

These are the most important modes for long files:

```bash
./check_dev34_fast.sh split-hot FILE PAT
./check_dev34_fast.sh slice-hot FILE PAT
./check_dev34_fast.sh split-warm FILE PAT
```

`split-hot` builds a prefix heap before the first line matching `PAT`, then
processes the rest of the file as a generated tail theory.

`slice-hot` builds the same prefix heap, but processes only the next top-level
theorem, lemma, corollary, or proposition slice. This is usually much faster
and is the preferred mode for proof iteration inside one theorem.

`split-warm` only prepares the prefix heap. This is useful when the next check
would otherwise spend its time building the prefix.

The pattern is found with `rg`, so it can be a theorem name, a top-level
declaration prefix, or a stable phrase near the target. Prefer stable theorem
names where possible.

### 4.5 Focus modes

The script knows named proof targets:

```bash
./check_dev34_fast.sh focus-list
./check_dev34_fast.sh focus mid-split-free
./check_dev34_fast.sh focus-full mid-d42
./check_dev34_fast.sh focus-warm mid-fold
./check_dev34_fast.sh focus-status mid-split-free mid-fold mid-d42
./check_dev34_fast.sh focus-prime mid-split-free mid-fold
```

The focus table currently includes targets such as:

```text
graph-branch-local
mid-split-free
mid-fold
mid-support
mid-d42
prefix-d44
dev34-cycle-realization
dev34-fan
dev34-semicircle
```

`focus` runs a full-index/source scan using a target-specific search phrase,
then `slice-hot` on the named target. This directly addresses the workflow
problem the team noticed: always grep the full index before making local proof
moves, then immediately run the narrow check.

Some focus targets use chained prefixes. For example, `mid-d42` first warms
the completed prefix before `Theorem_GT_3_7`, then warms the prefix before
`Theorem_GT_4_2`. This prevents the split prefix from becoming enormous and
lets several late-file targets reuse intermediate work.

## 5. Does It Make Things Faster?

Yes, when the workload is a late-file or late-layer proof edit and the parent
caches are warm.

The speedup comes from four places:

1. Parent heaps avoid replaying earlier layer sessions.
2. Split prefix heaps avoid replaying the earlier part of the same large file.
3. Slice checks avoid processing unrelated later theorems.
4. Freshness stamps skip checks whose exact inputs already succeeded.

The recent Section 3 work illustrates the intended use. A narrow
`slice-hot` check for `Theorem_GT_3_3` in
`dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy` finished in about 5 elapsed
seconds after the relevant prefix was warm. A broad build or full-file process
would be much slower, and a cold cache can still spend minutes warming parent
heaps or building a split prefix.

The important qualification is "after the relevant prefix was warm." The first
run of a target can still be expensive because it has to build the parent heap
and the generated prefix. The payoff appears on the second and later
iterations, especially when edits are confined to the current theorem slice.

For practical iteration, the best sequence is:

```bash
./check_dev34_fast.sh scan "keywords for the intended lemma"
./check_dev34_fast.sh focus-warm mid-split-free
./check_dev34_fast.sh focus mid-split-free
# edit a small proof batch
./check_dev34_fast.sh focus mid-split-free
```

When the focus target is already warm, the repeated check should usually be
much closer to seconds than minutes.

## 6. Important Options and Environment Variables

The script exposes several controls.

```bash
TIMEOUT=120s ./check_dev34_fast.sh focus mid-fold
```

`TIMEOUT` changes the timeout used by most layer and process checks. Some late
targets have larger defaults, but `TIMEOUT` is still the main knob when a
valid proof needs more time.

```bash
FORCE_PROOFS=1 ./check_dev34_fast.sh prove dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

`FORCE_PROOFS=1` adds `-o skip_proofs=false`. It also changes cache digests,
so proof-forced caches do not get confused with quick-and-dirty caches.

```bash
SKIP_PROOFS=1 ./check_dev34_fast.sh hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
```

`SKIP_PROOFS=1` affects `process_theories` only when `FORCE_PROOFS` is not
set. It is useful for scaffold checks. Do not treat it as proof validation.

```bash
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh focus mid-d42
```

`DEV34_FAST_PROC_CACHE=0` disables process/slice skip stamps. The check still
uses parent heaps and split prefixes, but it reruns the process step.

```bash
DEV34_FAST_AUTOWARM=0 ./check_dev34_fast.sh hot FILE
```

`DEV34_FAST_AUTOWARM=0` stops the script from automatically warming parent
caches. This is useful if you only want to see a failure quickly or avoid
unexpected long cache builds.

```bash
DEV34_FAST_DEEP_AUTOWARM=0 ./check_dev34_fast.sh focus mid-fold
```

`DEV34_FAST_DEEP_AUTOWARM=0` warms only the immediate parent target instead of
the whole parent chain.

```bash
DEV34_FAST_VERBOSE=1 ./check_dev34_fast.sh slice-hot FILE PAT
```

`DEV34_FAST_VERBOSE=1` prints generated session details for split checks.

```bash
DEV34_FAST_SKIP_FRESH_TARGET=0 ./check_dev34_fast.sh hot FILE
```

`DEV34_FAST_SKIP_FRESH_TARGET=0` forces `proc`/`hot` to process the explicit
file even when the whole target layer cache is already fresh. This is useful
when measuring local runtime or when you want a direct `process_theories`
check rather than relying on the coarser layer stamp.

```bash
FORCE_CACHE=1 ./check_dev34_fast.sh cache prefix-mid
```

`FORCE_CACHE=1` rebuilds a layer cache even if the stamp says it is fresh.

## 7. Downsides and Failure Modes

The fast cache has real downsides. Most are manageable if we remember what the
tool is and what it is not.

### 7.1 It can hide the cost of earlier proof text

A `slice-hot` check can make the current theorem look cheap because the prefix
was already built with `quick_and_dirty` and `skip_proofs` options in the
temporary prefix session. That is appropriate for local iteration, but it does
not measure the final cost of replaying all proofs in order.

Use focused checks for development. Use layer builds and final builds for
certification.

### 7.2 Generated split theories are approximate development artifacts

The split prefix is produced by copying ranges of the original file. This
works because Isabelle theories have a clear `begin`/`end` structure and our
targets are top-level theorem boundaries. It is still a text transformation.

Bad split patterns can produce misleading failures or accidentally check a
larger or smaller region than intended. Prefer exact top-level names such as
`theorem Theorem_GT_4_2` or stable lemma names.

### 7.3 Caches can become stale or overgrown

The cache directory accumulates split directories and stamps. This is normal,
but it can become large and cluttered. The script has:

```bash
./check_dev34_fast.sh cache-clean
```

This removes `.dev34_fast_cache`, including local freshness stamps and
generated split theories. It does not remove Isabelle's system heap images.
It does not need to be run often. If a cache behaves suspiciously, first rerun
with `DEV34_FAST_PROC_CACHE=0`; if that is not enough, clean or force the
relevant cache.

### 7.4 `quick_and_dirty` is not final verification

Many modes pass `-o quick_and_dirty`, and generated prefix sessions also use
`skip_proofs`. This is intentional: the tool is for fast iteration and
statement/proof-shape checking. The zero-sorry goal still requires serious
verification once the proof text is closed.

### 7.5 Full indexes are separate from proof caches

`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` are generated by separate scripts.
The fast checker searches them but does not automatically regenerate them after
every theorem edit. When statements move, new lemmas are added, or session
files change, run:

```bash
./gen_index.sh
./gen_stmt_index.sh
```

Then commit the index refresh separately when useful. Keeping indexes fresh is
what makes the `scan` and `focus` workflow effective.

## 8. Recommended Day-to-Day Workflow

For a proof target, use this pattern:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh scan "mathematical keywords for the target"
./check_dev34_fast.sh focus-status mid-split-free
./check_dev34_fast.sh focus-warm mid-split-free
./check_dev34_fast.sh focus mid-split-free
```

Then edit in small batches and rerun:

```bash
./check_dev34_fast.sh focus mid-split-free
```

If a proof times out:

```bash
TIMEOUT=180s ./check_dev34_fast.sh focus mid-split-free
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh focus mid-split-free
```

If a theorem statement or helper declaration changed, refresh indexes:

```bash
./gen_index.sh
./gen_stmt_index.sh
```

Before a meaningful commit, run:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus-status mid-split-free mid-fold mid-d42 prefix-d44
git diff --check -- <changed files>
```

For a larger milestone, use the relevant layer:

```bash
./check_dev34_fast.sh cache-through dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy
./check_dev34_fast.sh prefix-mid
```

At the end of the whole zero-sorry goal, focused checks are not enough. Run
the appropriate full build command from `CLAUDE.md` or the strongest practical
GeoTop build for the target stack.

## 9. How This Should Guide the Remaining Moise Work

The current remaining Section 3-4 holes are not best attacked with repeated
full builds. The intended pattern is:

1. Use `scan` aggressively to avoid reproving existing helpers.
2. Use focus targets to keep each proof package hot.
3. Prove small extracted obligations and commit them with detailed messages.
4. Regenerate indexes after statement-level changes.
5. Periodically run broader layer checks so the split-cache view does not
   drift away from the real session.

The cache is especially helpful for the current `dev34_prefix_mid` work,
because the open Section 3 and D42 packages live deep enough in the file that
plain iteration is expensive. It is less helpful for genuinely new
infrastructure that changes early layers, because early changes invalidate
many downstream caches.

In short: the fast cache is not magic, but it changes the economics of proof
development. It makes the right workflow affordable: full-index search first,
small proof edits second, narrow validation third, and broader verification at
milestones.
