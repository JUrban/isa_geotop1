# Manual: the dev34 fast cache and check_dev34_fast.sh

This note explains the local fast-check system built around
`check_dev34_fast.sh` and `.dev34_fast_cache`.  The short version is that the
script trades a single large Isabelle build for smaller, repeatable checks
against cached parent heaps and cached generated prefix theories.  It is useful
for proof development in the `dev34` split because the active proof files are
deep in a long dependency stack, and replaying that whole stack for every small
proof edit is too slow.

The important qualification is that this is a development accelerator, not the
final proof standard.  The fast modes deliberately use Isabelle options such as
`quick_and_dirty`, `skip_proofs` in generated prefix sessions, and
`process_theories` for small local slices.  Those options are exactly what make
the loop fast, but they also mean a fast green result should be treated as
"this local edit is syntactically and logically plausible in the intended
context", not as "the full project has been completely rechecked from first
principles."  Before closing a theorem or committing a major proof step, the
right discipline is still to run the relevant focused downstream checks, scan
for markers, refresh the indexes when needed, and eventually do stronger
session-level checks.

## 1. The problem this solves

The `dev34` work is split into many Isabelle sessions and directories:

1. `dev34_pre` builds `GeoTopPre3Dirty`.
2. `dev34_prefix_base` builds `GeoTop34PrefixBaseDirty`.
3. `dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy` builds
   `GeoTop34PrefixGraphCacheDirty`.
4. `dev34_prefix_graph` builds `GeoTop34PrefixGraphDirty`.
5. `dev34_prefix_mid` builds `GeoTop34PrefixMidDirty`.
6. `dev34_prefix` builds `GeoTop34PrefixDirty`.
7. `dev34_facts` builds `GeoTop34FactsDirty`.
8. `dev34_workfacts` builds `GeoTop34WorkFactsDirty`.
9. `dev34_linkfacts` builds `GeoTop34LinkFactsDirty`.
10. `dev34_graphfacts` builds `GeoTop34GraphFactsDirty`.
11. `dev34_graphwork` builds `GeoTop34GraphWorkDirty`.
12. `dev34_openstar` builds `GeoTop34OpenStarDirty`.
13. `dev34_core` builds `GeoTop34CoreDirty`.
14. `dev34` builds `GeoTop34DevDirty`.

The active Section 3-4 proofs usually live near the end of this chain.  For
example, `dev34/GeoTop_3_4.thy` is checked against the parent heap
`GeoTop34CoreDirty`, with all earlier layer directories supplied by `-d`
options.  A naive full rebuild after every edit may spend most of its time
replaying already-finished material.  That is especially painful when the edit
is only one local proof step near line 15,000.

The fast script attacks this in three complementary ways.

First, it uses layer caches.  A layer cache records that a named layer heap is
fresh with respect to the files that feed it.  If `core` is fresh, a local
`dev34/GeoTop_3_4.thy` check can start from `GeoTop34CoreDirty` instead of
rebuilding all parent material.

Second, it uses process caches.  A process cache records that a specific file
was already run through `isabelle process_theories` with the same file contents,
parent target, root file, and proof options.  If nothing relevant changed, the
script can skip reprocessing that exact file.

Third, and most importantly for proof iteration, it uses split caches.  A split
cache creates a temporary theory containing everything before a target theorem,
builds that prefix once as its own heap, and then checks either the theorem
slice or the remainder of the file by importing that prefix heap.  This is why
rechecking a theorem after the prefix is built can fall from minutes to a few
seconds.

## 2. What lives in .dev34_fast_cache

`.dev34_fast_cache` is a local, disposable directory.  It is not theorem source
and should not be treated as a durable proof artifact.  In the current working
tree it is around 32 MB, which is small compared with Isabelle heap directories
but large enough to contain many generated split theories and digest stamps.

The main contents are:

- Layer stamp files such as `core.sha256`, `dev34.sha256`,
  `prefix-mid.sha256`, and similar.  These say "the layer cache for this target
  matched this digest when it was last built."
- Process stamp files named like `proc-<sha256>.sha256`.  These record
  successful `process_theories` checks for individual files under particular
  parent/proof-option combinations.
- Split directories named like `split-2ad225ba9cbd`.  Each contains a generated
  `ROOT`, a generated `..._Prefix.thy`, and usually a generated
  `..._Slice.thy` or `..._Tail.thy`.
- Split stamp files named like `split-<sha256>.sha256`.  These record that a
  generated prefix, slice, or tail was already built/processed with the matching
  digest.

An example split directory for `dev34/GeoTop_3_4.thy` has this shape:

```text
.dev34_fast_cache/split-2ad225ba9cbd/
  ROOT
  GeoTop_3_4_Split_2ad225ba9cbd_Prefix.thy
  GeoTop_3_4_Split_2ad225ba9cbd_Slice.thy
```

The generated `ROOT` declares a temporary session roughly like:

```isabelle
session GeoTop_3_4_Split_2ad225ba9cbd_Prefix_Session = GeoTop34CoreDirty +
  options [system_heaps, quick_and_dirty, skip_proofs, timeout = 240]
  theories
    GeoTop_3_4_Split_2ad225ba9cbd_Prefix
```

That temporary session is the key speed trick.  The prefix theory imports the
real parent context and contains the source of the original file only up to the
target theorem.  Once Isabelle has built that generated prefix heap, the active
theorem can be checked as a tiny theory importing the prefix.  Rechecking a
small slice no longer requires reparsing and reprocessing the whole source file
before it.

It is safe to delete `.dev34_fast_cache`; the script can recreate it.  The
`cache-clean` mode does exactly that with `rm -rf .dev34_fast_cache`.  Deleting
it costs time, not proof work.

## 3. The script defaults and environment switches

The script uses `/project/bin/isabelle` by default, unless `ISABELLE` is set:

```bash
ISABELLE=/some/other/isabelle ./check_dev34_fast.sh holes
```

The default command timeout is `90s`, controlled by `TIMEOUT`:

```bash
TIMEOUT=180s ./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy target_name
```

All Isabelle invocations include `-o system_heaps=true`.  This encourages
reusable heap images and is part of why warm layers help later iterations.

Proof-option behavior is controlled by two variables:

- `FORCE_PROOFS=1` passes `-o skip_proofs=false`.  This is the stronger mode
  for proof-bearing checks.
- `SKIP_PROOFS=1`, when `FORCE_PROOFS` is not set, passes
  `-o skip_proofs=true`.  This is useful for scaffold and outline iteration.

The generated split-prefix sessions always use `quick_and_dirty` and
`skip_proofs` in their `ROOT` options.  That is intentional: completed material
above the target line is being used as context for local iteration, not being
re-certified on every proof edit.

There are also internal switches used by modes:

- `DEV34_FAST_PREFIX_ONLY=1` builds or checks only the split prefix.
- `DEV34_FAST_SLICE_ONLY=1` checks only the next theorem/lemma slice instead of
  the whole file tail.
- `DEV34_FAST_STATUS_ONLY=1` reports freshness without building.
- `DEV34_FAST_PROC_CACHE=0` disables process-cache skipping.
- `DEV34_FAST_AUTOWARM=0` disables automatic parent warming.
- `DEV34_FAST_DEEP_AUTOWARM=0` warms only the immediate parent instead of the
  whole parent chain.

These are normally set by named modes, not typed manually.

## 4. The everyday modes

The cheap discovery modes should be used constantly:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh grep geotop_segment_chain
./check_dev34_fast.sh index boundary_edge
./check_dev34_fast.sh names closed_segment_face
./check_dev34_fast.sh stmts geotop_is_complex
```

`holes` scans the dev34 target layers for remaining `sorry` and proof-search
markers.  `grep` searches both the target source theories and the generated
indexes.  `index`, `names`, and `stmts` narrow that search to
`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`.

This matters because the full index is often faster than rediscovering facts by
memory.  For the current Moise 3-4 work, it is usually worth running a full
index grep before attempting a proof step.  It catches already-proved wrappers,
endpoint lemmas, linear-graph facts, and one-off helper lemmas that are easy to
miss when staring only at the active theory.

The planning and warming modes answer "what parent heap will this file use?"
and "is that parent heap fresh?":

```bash
./check_dev34_fast.sh dirty
./check_dev34_fast.sh plan dev34/GeoTop_3_4.thy
./check_dev34_fast.sh cache-status dev34/GeoTop_3_4.thy
./check_dev34_fast.sh cache-parents dev34/GeoTop_3_4.thy
```

For actual local checking, the normal modes are:

```bash
./check_dev34_fast.sh hot dev34/GeoTop_3_4.thy
./check_dev34_fast.sh outline dev34/GeoTop_3_4.thy
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy theorem_name
./check_dev34_fast.sh split-hot dev34/GeoTop_3_4.thy theorem_name
./check_dev34_fast.sh split-warm dev34/GeoTop_3_4.thy theorem_name
```

`hot` runs the whole file through `process_theories` against the right parent
heap, after warming parent caches if necessary.  It can skip if the target or
process cache is fresh.

`outline` is a fast scaffold check with `skip_proofs=true`; it is useful when a
new theorem skeleton contains `sorry`s and the immediate concern is whether the
statements, proof structure, and names type-check.

`slice-hot FILE PAT` is the best mode for a single active theorem.  It finds
the first line in `FILE` matching `PAT`, builds a prefix before that line, and
then processes only until the next top-level `lemma`, `theorem`, `corollary`,
or `proposition`.  This catches errors inside the active theorem without
spending time on the rest of the file.

`split-hot FILE PAT` uses the same prefix but processes from `PAT` through the
end of the original theory.  It is slower than `slice-hot`, but it catches
downstream breakage in later theorems.

`split-warm FILE PAT` builds only the prefix.  Use it before a longer editing
session when the target line is stable and the first check would otherwise be
spent building the prefix.

## 5. How split-hot and slice-hot actually work

The split modes are line-based but content-digested.

First, the script searches for the first matching line:

```bash
rg -n -- "$pattern" "$file" | head -n 1
```

That first match is the split point.  This is convenient but also a source of
mistakes: if the pattern is too broad, the script may split at a comment,
earlier helper, or different theorem.  Good patterns are theorem names, not
generic phrases.

Next, the script finds the original theory's `begin` and final `end`.  It then
writes a generated prefix theory.  Without chaining, the prefix keeps the
original imports and all source text before the target line, and closes with
`end`.  With chaining, it imports an earlier generated prefix session and only
includes the text between the chain target and the current target.  Chaining is
used for selected focus targets to avoid repeatedly building enormous prefixes.

The script computes a digest for the prefix from:

- the original file path;
- the pattern;
- `FORCE_PROOFS`;
- the generated prefix theory hash;
- the generated `ROOT` hash;
- the parent target digest, if there is a parent layer;
- the chained prefix digest, if chaining is active.

If the matching split stamp exists, the prefix build is skipped.  Otherwise,
the script runs:

```bash
isabelle build -o system_heaps=true ... -b <generated-prefix-session>
```

After the prefix is ready, the script writes either a tail or a slice theory.
The generated theory imports the prefix session and contains source from the
target line onward.  In tail mode it goes to the original final `end`.  In slice
mode it stops just before the next top-level theorem-like command.

The tail/slice digest includes:

- tail or slice mode;
- the original file path;
- the pattern;
- `FORCE_PROOFS`;
- `SKIP_PROOFS`;
- the prefix digest;
- the generated tail/slice file hash.

If the tail/slice process stamp is fresh, the process step is skipped.  If not,
the script runs:

```bash
isabelle process_theories -o system_heaps=true ... \
  -l <generated-prefix-session> -o quick_and_dirty -f <generated-slice-or-tail>
```

This means a failing line number may refer to a generated file under
`.dev34_fast_cache/split-...`, or to Isabelle's temporary copy of that file
under `/tmp`.  When the mapping is unclear, open the generated
`..._Slice.thy`; it contains the exact source slice being checked.

## 6. Is it faster?

Yes, when used for the right job.

The first split check for a theorem still has to build the prefix.  For a deep
target in `dev34/GeoTop_3_4.thy`, recent prefix builds have often been in the
rough range of 20-30 seconds elapsed, with more CPU time spent internally by
Isabelle.  That first run is not free.

The payoff comes after the prefix is fresh.  Subsequent `slice-hot` iterations
on the same theorem commonly process only the small generated theorem slice,
and recent checks have been around a few seconds.  That is the practical
difference between a proof loop that is usable and one where every attempt costs
one or more minutes.

It is also faster because it lets us choose the blast radius:

- `grep` and `holes` answer search/status questions without building anything.
- `focus-status` and `cache-status` answer cache freshness questions without
  building anything.
- `slice-hot` checks the current theorem only.
- `split-hot` checks from the current theorem through the end of the file.
- `hot` checks a whole changed file against its parent heap.
- `cache-through` or `cache-all` spends time intentionally to make later loops
  cheaper.

This selective verification is the main improvement over running one large
build command after every edit.  The large build is still valuable, but it is a
bad inner loop for exploratory proof development.

## 7. Downsides and failure modes

The first downside is proof strength.  Prefix sessions are generated with
`quick_and_dirty` and `skip_proofs`.  That is acceptable for reusing a
previously-developed context during local iteration, but it is not the final
standard for a closed theorem.  A local theorem that passes `slice-hot` should
still be followed by downstream checks and stronger proof-forced checks at
appropriate milestones.

The second downside is pattern sensitivity.  `slice-hot FILE PAT` splits at the
first `rg` match.  A broad pattern can silently check the wrong slice.  The
habit should be: use a full theorem name, read the reported line range, and if
the result is surprising inspect the generated slice.

The third downside is that slice mode intentionally does not check later
dependencies.  It stops at the next top-level theorem-like command.  This is
excellent while fixing one theorem, but it will not tell us whether a later
wrapper theorem still composes.  Use `split-hot` or focused downstream slices
after the local theorem turns green.

The fourth downside is cache churn.  The split key includes the file, pattern,
logic, and chain pattern, and the prefix digest includes generated source.
Moving the target line, changing source above it, changing a parent layer, or
changing proof options can make an old prefix stale.  Line movement can also
produce new split directories.  This is normal, but it means `.dev34_fast_cache`
will grow over time.  `cache-clean` is the reset button.

The fifth downside is possible confusion from "skipped" output.  If a process
cache is fresh, the script may skip the check entirely.  That is good when
nothing changed.  It is bad if the human expected Isabelle to rerun.  In that
case, disable process-cache skipping for one run:

```bash
DEV34_FAST_PROC_CACHE=0 ./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy theorem_name
```

The sixth downside is that the generated context can hide source-location
intuition.  Isabelle errors may point at generated theory lines, not original
file lines.  The generated file is readable, and the reported split range tells
which original line interval it came from, but it adds a translation step.

The seventh downside is operational complexity.  There are many modes because
there are several different questions: search, hole count, parent freshness,
parent warming, whole-file processing, slice processing, full-tail processing,
and milestone builds.  The practical answer is not to memorize every mode.  Use
the small workflow recipes below.

## 8. Recommended workflows

For a new proof target:

```bash
./check_dev34_fast.sh grep exact_or_related_name
./check_dev34_fast.sh plan dev34/GeoTop_3_4.thy
./check_dev34_fast.sh split-warm dev34/GeoTop_3_4.thy exact_theorem_name
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy exact_theorem_name
```

For an inner proof-edit loop:

```bash
./check_dev34_fast.sh grep fact_name_or_concept
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy exact_theorem_name
```

When the theorem slice turns green:

```bash
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy immediate_wrapper_name
./check_dev34_fast.sh split-hot dev34/GeoTop_3_4.thy exact_theorem_name
./check_dev34_fast.sh holes
rg -n "sledgehammer|try0|oops" dev34 dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34_core
git diff --check
```

When indexes may be stale, regenerate them using the local index scripts and
then use:

```bash
./check_dev34_fast.sh index concept
./check_dev34_fast.sh grep theorem_fragment
```

For a longer session after many edits:

```bash
./check_dev34_fast.sh cache-parents dev34/GeoTop_3_4.thy
./check_dev34_fast.sh focus-status
./check_dev34_fast.sh focus-prime
```

For the current segment-chain area, the typical focused command is:

```bash
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_segment_chain_vertices_complex_dev34
```

Once that complex lemma compiles, the downstream wrapper checks should include
the listing theorem and the endpoint boundary-edge target, because those are
the consumers that convert the finite ordered segment family into the Moise
boundary-edge conclusion.

## 9. When to distrust a fast green result

A fast green result is weakest when:

- it came from `outline`, `focus-outline`, `graph-outline`, or any run with
  `SKIP_PROOFS=1`;
- it skipped due to a process cache and no Isabelle process actually ran;
- it checked only a slice and the theorem has important downstream consumers;
- it depended on a broad pattern that may have matched the wrong line;
- the generated prefix used material above the target that was recently edited
  but not strongly rechecked;
- the change affects statements, definitions, imports, notation, or simp rules,
  not just a local proof body;
- the target is being prepared for a milestone or final zero-sorry claim.

The response is not to abandon the fast cache.  The response is to escalate the
check level deliberately: inspect the generated slice, rerun with process cache
disabled if needed, run `split-hot`, run the downstream focus targets, force
proofs for a relevant layer when appropriate, and eventually run the session
build expected for milestone confidence.

## 10. Bottom line

The fast cache is worth using.  It turns many Section 3-4 proof iterations from
minute-scale rebuilds into second-scale local checks after the first prefix is
warm.  It also encourages better workflow: search the full index first, check a
small theorem slice, then widen to downstream checks instead of repeatedly
asking Isabelle to rebuild everything.

The cost is that the workflow has more states: fresh parent heaps, stale parent
heaps, fresh process stamps, generated prefix sessions, generated slices, and
different proof-skip options.  Those states are manageable if the script output
is read literally.  "Skipped" means the cache answered the question.  "Building
prefix" means the first run is paying the setup cost.  "Processing slice" means
the local theorem is actually being checked.  "Processing tail" means later
theorems are being checked too.

For daily work, the recommended stance is:

- use `grep`/`index` frequently;
- use `slice-hot` for the active theorem;
- use `split-hot` or downstream `slice-hot` before claiming the local target is
  really integrated;
- use `holes`, marker scans, and `git diff --check` before commits;
- use detailed commit messages to record which Moise theorem or helper was
  attacked, what proof strategy worked, and what remains.

That gives us a fast inner loop without pretending it is the final verifier.
