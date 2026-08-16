---
name: gobra-debug-perf
description: Find the performance bottleneck in a slow Gobra verification. Use whenever verifying Go/Gobra code takes minutes, hangs, diverges, or hits a timeout, and whenever someone asks "why is Gobra so slow here", "which method is slow to verify", "why does verification never finish", or wants to profile verification time, SMT queries, branching, or quantifier instantiations. Use this before changing anything — it produces the diagnosis that gobra-improve-perf then acts on.
---

# Diagnosing Gobra verification performance

Gobra translates annotated Go to Viper and verifies it with Silicon, a symbolic
execution engine backed by Z3. Almost all the time is spent inside Z3, so
verification time is essentially:

    time  ≈  (number of symbolic execution paths)  ×  (cost of each SMT query)

and the cost of a query is dominated by the **proof context**: every axiom,
function definition, path condition, and heap chunk that Silicon hands to Z3
alongside the actual proof goal. Almost every real bottleneck is "too many
paths" or "too much context", and the two multiply each other.

Your job in this skill is to say **which member is slow** and **which of those
two factors explains it**, backed by measurements. Do not start fixing things
along the way — a hypothesis you haven't measured is usually wrong, and
optimizations that are not measured tend to make things slower.

## Calibration: what "slow" looks like

Numbers from a fully verified 45-minute Gobra project (~2300 Viper members)
are a useful yardstick when reading your own measurements:

| Observation | Typical healthy value |
|---|---|
| Verification time distribution | 95% of methods < 9s; 95% of pure functions < 2s; predicates ~all < 1s |
| Share of time inside Z3 | ~77% of total |
| Share of SMT time on heap obligations | ~77% (quantified permissions are the most expensive per query by far) |
| Slowest single SMT query | tens of ms is normal; seconds means something is wrong |
| Total time | dominated by a handful of members, not spread evenly |

Two consequences worth internalizing. First, a member that takes minutes is an
outlier, not "a big function" — look for a structural cause. Second, slow
verification is usually **many cheap queries**, not a few expensive ones; a high
query count with a low 99th percentile points at path explosion, not at a hard
proof goal.

## Workflow

### 1. Measure the whole package once

Ask Gobra to dump per-member statistics, and keep the run deterministic so the
numbers mean something:

```bash
gobra -p ./path/to/pkg \
      --gobraDirectory ./gobra-out \
      --packageTimeout 30min \
      2>&1 | tee gobra-run.log
```

`--gobraDirectory` makes Gobra write `gobra-out/stats.json`, containing every
Gobra member, its Viper members, and the verification time of each in
milliseconds. It is written from a JVM shutdown hook, so **you still get it if
you Ctrl-C or the run is killed** — which is exactly the situation where you
need it most. Members that never terminated simply have no successful entry,
and Gobra logs `did not terminate` errors for them on exit.

Measurement hygiene that matters:

- Do **not** use `--parallelizeBranches` while measuring. It speeds things up
  but changes SMT variable names between runs, which makes results unstable and
  occasionally produces spurious errors.
- Silicon verifies methods in parallel by default, so wall-clock time for the
  package hides which member is expensive; that is what `stats.json` is for.
- Re-run a suspicious measurement at least twice. Differences below ~10% are
  noise, not signal.

### 2. Rank the members

```bash
python3 .claude/skills/gobra-debug-perf/scripts/rank_members.py gobra-out/stats.json
```

The script sums Viper member times per Gobra member, skips imported members,
and prints the slowest ones plus members that never finished. Expect a very
skewed distribution. If it *isn't* skewed — everything moderately slow, no
outlier — suspect the shared proof context rather than any single member, and
jump to the `--chop` comparison below.

### 3. Isolate one member and get a fast reproduce loop

Gobra can verify individual members by line number, using its slicing
("chopper") analysis to keep only the declarations that member can depend on:

```bash
# pass every file of the package; attach @line only to the one you target
gobra -i pkg/a.go pkg/b.go@412 --gobraDirectory ./gobra-out
```

The line number must be a line of the member (its signature line is the safe
choice). This is the single most valuable habit in this skill: it turns a
45-minute feedback loop into a 30-second one, needs no code changes, and is
sound — the slice over-approximates what the member's proof obligations can
depend on.

`--chop N` is the related bulk mode: it splits the package into at most `N`
Viper programs with smaller contexts. Useful to confirm that context size (not
the member itself) is the problem: if the sum of the parts is much faster than
the whole, irrelevant context is your bottleneck.

#### Inside the member: `assume false`

`assume false` is the same idea one level down, and it is not only a tool for
hangs (step 7). Everything after it verifies vacuously, so a run reports the
cost and the errors of the **prefix alone**. Three uses, all cheap:

- **Cost profile.** Walk it down the body and diff the run times. That turns
  "this member takes 15 minutes somewhere" into a per-region number — and the
  region where the time jumps is usually not the one you would have guessed.
- **Which obligations already hold.** Put it at the top of a loop body and
  every loop-free path — the early returns and their postconditions, the
  invariant's establishment, the exit — is checked on its own. That answers
  "does this postcondition hold on the `return 0` path?" with evidence instead
  of an argument, in one run.
- **Splitting a failure from a slowdown.** If the prefix is fast and correct,
  whatever you are chasing is downstream of the cut.

It costs one run per position, so bisect rather than scan, and remember the
results are only about the prefix: a variant that cuts earlier finishes sooner
for a trivial reason.

### 4. Get per-query data for the slow member

The question that classifies almost every bottleneck is: **many cheap queries,
or a few expensive ones — and of what kind?** Two ways to answer it, in order
of preference.

**A. Silicon's per-query recorder (best).** [Silicon PR #966](https://github.com/viperproject/silicon/pull/966)
adds `--recordProofQueries <file.csv>`, which logs every solver interaction
with its member, source position, category, duration, and outcome. If it isn't
in your Silicon yet, build that branch — for a real diagnosis it pays for
itself quickly:

```bash
git fetch origin pull/966/head:pr966 && git checkout pr966
git submodule update --init --recursive
sbt -batch assembly          # -> target/scala-2.13/silicon.jar
```

If that fails with `NoClassDefFoundError: Could not initialize class
sbt.internal.parser.SbtParser$`, the pinned sbt is too old to parse your JDK's
class files (silicon has pinned 1.6.2, whose Scala 2.12 cannot read JDK 21
bytecode). Bump `project/build.properties` to the version Gobra itself uses —
1.12.4 works on JDK 21 — rather than installing an older JDK.

Run it on the Viper file of the isolated member:

```bash
# --printVpr writes the slices as <input>.chopped<i>.vpr next to the source
# (chopping happens inside the verification step, so don't add --noVerify —
# that skips chopping and dumps the whole unsliced package).
gobra -i pkg/b.go@412 --printVpr
# --assertTimeout should match the package's assert_timeout, otherwise queries
# Gobra cuts off run to completion here and the durations do not correspond
silicon --numberOfParallelVerifiers 1 --assertTimeout 30000 \
        --recordProofQueries queries.csv pkg/b.go.chopped0.vpr
python3 .claude/skills/gobra-debug-perf/scripts/summarize_queries.py queries.csv
```

The CSV columns are `kind,member,file,line,column,category,durationMs,succeeded,description`;
`category` is one of `Consistency`, `Heap`, `FunctionalCorrectness`,
`PathInfeasibility`, `ScopeManagement`. The bundled script aggregates time and
count per category and member and lists the slowest individual queries with
their source positions. Readings:

- **`PathInfeasibility` dominating the count** → path explosion; Silicon is
  spending its time pruning branches.
- **`Heap` dominating the time** → heap obligations, very likely quantified
  permissions (see the common culprits below).
- **A few slow `FunctionalCorrectness` queries at one position** → a genuinely
  hard proof goal (arithmetic, quantifiers) — the position column tells you
  exactly which assertion.
- **Push/pop (`ScopeManagement`) count** is a rough proxy for how much
  branching and scoped work happened.

**B. Fallback: the prover log.** Without the PR, approximate the same numbers
from the SMT-LIB2 stream:

```bash
# writes query-00.smt2 (one file per verifier instance, hence -00)
silicon --numberOfParallelVerifiers 1 --proverLogFile query pkg/b.go.chopped0.vpr
grep -c '(check-sat)' query-00.smt2   # ≈ number of SMT queries
grep -c '(push' query-00.smt2         # ≈ scopes opened: branches and scoped ops
```

### 5. Classify the bottleneck

| Symptom | Likely cause | How to confirm |
|---|---|---|
| Many queries, each fast; `PathInfeasibility` dominates the count | **Path explosion.** Silicon forks on `if`, on impure implications `b ==> acc(...)`, on impure conditionals, and temporarily when evaluating `unfolding P(x) in e` | Count branching sources in the member *and in the predicates it unfolds*: a predicate with N impure implications in its body costs up to 2^N paths at every unfold site |
| `Heap` queries dominate the time; the slowest queries are heap-related | **Quantified permissions.** Computing the permission held for a location covered by several quantified chunks makes Z3 case-split, worst case exponentially in the number of chunks that may provide permission | Look for several `acc(s)` / `forall i int :: ... acc(&s[i])` footprints live at the same time — especially byte slices that might overlap (see the culprits below) |
| Slow despite a tiny body and short contract | **Inherited cost.** The member unfolds an expensive predicate, or calls a function whose body is inlined into the context | Follow the `dependencies` field in `stats.json` and verify the dependency in isolation |
| Everything moderately slow, no outlier | **Context size.** Package-level axioms, imported specs, and one quantified axiom per pure function sit in the context of every query | Compare total time with `--chop N` against the unsliced run |
| Diverges, or times swing wildly between runs | **Quantifier blow-up / matching loop** | SMTScope on a trace, step 6 |
| Results change when unrelated code changes | **Instability**, not performance | Check whether `--parallelizeBranches` is on; reducing context usually helps here too |

Two easy misreadings to avoid. Long *Go* functions are suspicious mainly
because they accumulate context and branches, not because of their line count —
a 100-line function with no branching and a small footprint can be fast. And an
expensive predicate is dangerous even when the predicate itself verifies in
milliseconds: the cost appears at every site that unfolds it.

#### Common culprits worth checking by sight

Before deeper profiling, look for these two patterns — in slice-heavy Go code
they account for a large share of real-world Gobra slowness:

**Bare quantified permissions for `[]byte` buffers.** Carrying
`forall i int :: 0 <= i && i < len(s) ==> acc(&s[i])` (i.e. `acc(s)`) through
contracts means every heap query must consider how the quantified chunks of
*all* live buffers might overlap. On the SCION router this alone blew up
verification time; the cure was a slice library that wraps the permissions in
a predicate (`sl.Bytes(s, 0, len(s))`) that is folded almost all the time and
unfolded only around the few statements that index the buffer. Diagnostic
signal: several byte slices in scope at once + `Heap` queries dominating time.
If the QPs are already behind a predicate, check it isn't unfolded over long
stretches of the body — an unfolded predicate is as expensive as no predicate.

**Reslicing.** Gobra often hangs or slows down *right after* a reslicing
operation `x[a:b]`, because the verifier cannot immediately relate the
elements of the new slice to those of the original — the connection
`&x[a:b][i] == &x[a+i]` must be established by quantifier reasoning that may
not fire on its own. Experienced users leave a breadcrumb assertion right
after the reslice to force it:

```go
assert forall i int :: 0 <= i && i < len(x[a:b]) ==> &x[a:b][i] == &x[a+i]
```

If a member slows down or diverges at a line containing a subslice expression,
suspect this first; the matching assertion is also the fix, so confirm by
adding it and re-measuring.

**Sequence slicing inside pure functions.** A spec function whose body slices a
sequence — `q[j:j+len(pat)] == pat` — encodes to nested `Seq_take`/`Seq_drop`
terms, and equalities over those are among the most expensive obligations Z3
sees. The cost lands on every *caller*, not on the function, so it is invisible
in per-member stats. Diagnostic signal: `FunctionalCorrectness` dominating the
time, and every hot query's source position containing a `[a:b]` expression.
See `gobra-improve-perf` for the range-form rewrite.

#### "Assert might fail" does not always mean the property is false

Before treating a failing assertion as a proof gap, check for an
`assert_timeout` in the package's `gobra.json` (or `--assertTimeout`). With one
set, a query that exceeds the budget is reported exactly like a refuted one.
Two tells that you are looking at a timeout rather than a false property:

- The step is trivial — the goal is a loop invariant modulo linear arithmetic,
  or follows by congruence from a fact asserted on the line above.
- It is the *last* obligation in a long member, where the context is largest.

Confirm by re-running that member with a much larger `assert_timeout`. If it
then passes, the property holds and the problem is probably context size. If
Z3 instead runs for tens of minutes and dies with `ProverInteractionFailed:
Interaction with prover yielded null` (an out-of-memory kill), more time is not
the answer either — the proof annotations (and potentially the spec) have to
change.

#### Invalid triggers: Gobra accepts patterns Viper rejects

Gobra does not run Viper's consistency check, so a quantifier can carry a
trigger that Silicon considers invalid. Z3 then gets an effectively untriggered
quantifier — the standard recipe for a blow-up — with no diagnostic anywhere in
the Gobra output.

`--checkConsistency` exists but **conflicts with `--config`**, which is what
`gobra-action` and most CI setups use. Get the check by dumping the Viper
program and running Silicon on it directly:

```bash
gobra -i pkg/file.go@412 other.gobra -I src -m <module> --printVpr
silicon --numberOfParallelVerifiers 1 --logLevel ERROR pkg/file.go.chopped0.vpr
# "{ ... } is not a valid Trigger (file.vpr@811.17--813.58)"
```

Restricting Silicon to a method that does not exist makes this a ~5s check
rather than a full verification, since consistency is checked before anything
is verified:

```bash
gobra -i <all pkg files> --printVpr --noVerify
silicon --numberOfParallelVerifiers 1 --logLevel ERROR \
        --includeMethods 'NoSuchMethod' pkg/file.go.vpr
```

Worth running once on any package with hand-written triggers: a real one had
six invalid triggers nobody knew about, one of them the *only* pattern on its
quantifier.

The cause is **interpreted arithmetic anywhere inside the pattern**.
`{&s[i-n:i][k]}` is rejected because the slice bound `i-n` is a subtraction
inside the trigger term, and `{seq(s)[lo+k]}` is rejected too — a sequence
index `Seq_index(q, lo+k)` is arithmetic exactly like a slice bound
`Seq_take(Seq_drop(q, j), hi-j)`. What *is* accepted: `{&s[:n][k]}` and
`{&s[lo:hi][k]}`, because `0`, `n`, `lo`, `hi` are not arithmetic and the
`sadd` in the encoding of `&x[k]` is not an interpreted operator at the
pattern level; and program-function applications such as
`{MatchesAt(q, pat, j)}`. `gobra-improve-perf` has the fix — and the warning
that "fix" is not automatic: replacing a rejected pattern with a valid but
very permissive one (`{pat[k]}`) measured *worse* than leaving the dead
trigger in place.

#### Ways to fool yourself while measuring

- **Reading a green isolated run as a green package run.** `-i file@line`
  verifies the chopper's slice for that member, and a slice is a *smaller*
  proof context than the package — it drops the axioms of every member the
  target cannot depend on. So a member can verify in isolation and still blow
  the assert budget in the package run, at an assertion the isolated run
  discharged in milliseconds. This is not a rare edge case; it is the normal
  failure mode of a member that is close to the budget. Use the isolated loop
  for iteration speed, never for the verdict, and re-run the package before
  believing a fix.
- **Comparing a run that aborts early against one that completes.** Silicon
  stops a member at its first failing obligation, so a variant that fails
  earlier finishes sooner and looks like a speed-up. Only compare runs that
  fail at the *same* place, or that both succeed. A "26× speed-up" that moved
  the first error earlier in the function is a 0× speed-up.
- **Comparing standalone Silicon against Gobra.** The two do not run the same
  experiment. Gobra passes the package's `assert_timeout`, so an expensive
  obligation is cut off; standalone Silicon defaults to no budget and lets the
  same query run for minutes. Gobra also verifies members in parallel, while
  profiling wants `--numberOfParallelVerifiers 1`. Both differences inflate
  standalone wall-clock — enough that a 13-minute package took 25 minutes to
  profile, and a 40-minute cap expired before the CSV was written at all. Pass
  `--assertTimeout <same value>` when you want the numbers to correspond, and
  do not read a standalone duration as "how long Gobra spends here".
- **Trigger stripping is *not* the distortion it looks like.** Deleting a
  rejected `{...}` from the dumped `.vpr` to get past the consistency check
  leaves the quantifier untriggered — but a trigger Viper rejects was never
  usable as a pattern in the first place, so the original was effectively
  untriggered too. Silicon may infer a different pattern for the stripped
  version (it says so: "Might not be able to use trigger ..."), so the two are
  not guaranteed identical, but stripping does not by itself make the program
  slower. Strip freely to keep debugging; just fix the trigger in the source
  before drawing conclusions about that quantifier specifically.

### 6. Get evidence at the Viper / Z3 level when needed

For the top one or two members, run Silicon directly on the dumped `.vpr` — it
exposes knobs Gobra doesn't forward:

```bash
silicon --numberOfParallelVerifiers 1 \
        --includeMethods 'someMethodPattern' \
        --logLevel INFO \
        pkg/b.go.chopped0.vpr
```

Useful Silicon flags when diagnosing: `--includeMethods` / `--excludeMethods`
to target one member, `--timeout` and `--assertTimeout` to bound the damage,
`--enableBranchconditionReporting` to see which branch a failure comes from,
`--printMethodCFGs`, and `--proverLogFile <path>` for the SMT-LIB2 log.

#### Hunting matching loops with SMTScope

When the classification points at quantifiers (divergence, unstable times,
huge instantiation counts), use [SMTScope](https://github.com/viperproject/smt-scope)
— the successor of the Axiom Profiler — on a Z3 trace. `cargo install smt-scope`
provides two CLI binaries, `smt-scope` and `z3-scope`.

Get the SMT2 file for the member from Silicon, then let `z3-scope` run Z3 and
analyze the trace in one step:

```bash
# writes query-00.smt2 (one file per verifier instance)
silicon --numberOfParallelVerifiers 1 --proverLogFile query pkg/b.go.chopped0.vpr

SCOPE_TRACE_FILE=trace.log SCOPE_DUMP_FILE=analysis.json \
SCOPE_SIZE_LIMIT=2000000000 \
z3-scope query-00.smt2
```

`z3-scope` invokes Z3 with `trace=true proof=true`, then reports detected
problems — matching loops included, with the offending quantifiers and their
triggers — as text on stderr and as JSON in `SCOPE_DUMP_FILE`. It exits
non-zero when it finds errors (set `SCOPE_NO_ERROR` to suppress that).

Trace size is the practical constraint: SMTScope struggles with traces
approaching ~4 GB. A *prefix* of a trace is valid input, and matching loops
almost always show up early, so cap the analysis with `SCOPE_SIZE_LIMIT`
(bytes) / `SCOPE_LINE_LIMIT` (lines) as above — or kill Z3 once the trace is a
couple of GB and analyze what you have (copy the file before killing Z3; on
some systems the contents vanish otherwise).

**`SCOPE_SIZE_LIMIT` caps what SMTScope reads, not what Z3 writes.** On a
badly-instantiating member, `z3-scope` will happily let Z3 emit tens of
gigabytes and then be killed before it analyzes anything — one run produced a
29.6 GB trace and no output, which on a sandbox with a disk quota is its own
incident. Bound the *producer* instead, and run the analysis separately:

```bash
timeout 40 z3 trace=true proof=true trace-file-name=tr.log query-01.smt2
smt-scope stats tr.log -k 12       # instantiation counts per quantifier
smt-scope redundancy tr.log        # duplicate ratios; flags multiplicative patterns
```

40 seconds is enough: a member that is instantiation-bound will have produced
gigabytes by then, and that fact is itself the measurement. `smt-scope
redundancy` is the higher-signal of the two — it prints a duplicate ratio per
quantifier and marks multiplicative patterns explicitly, so
`qp.$FVF<f>-eq-outer: 820 duplicate, ratio 86.7%! Multiplicative pattern
(2.3x)!` tells you in one line that quantified permissions, not your own
quantifiers, are what Z3 is drowning in. Also make sure Gobra's
`--z3APIMode` is off anywhere in the pipeline: with it there is no separate Z3
process, hence no `.smt2` file to replay.

Complementary uses:

- `smt-scope stats trace.log -k 10` prints total instantiation counts and the
  ten most-instantiated quantifiers — a quick blow-up check without the full
  analysis (tens of thousands is normal for the slice of a small member; tens
  of millions is a blow-up).
- The [web GUI](https://viperproject.github.io/smt-scope/) loads the same
  trace for interactive exploration of the instantiation graph — the right
  tool once you know which quantifier to stare at.

When a loop is found, note **whose quantifier it involves**: user-provided
ones (your triggers) are fixable and worth chasing; loops inside Z3's
algebraic-datatype theory or Silicon's built-in collection axiomatizations are
not fixable from your source — recognizing them saves wasted effort.

### 7. Special case: verification never terminates

Divergence is common while a member still has verification errors, and it gives
you no output to work with. Do not wait it out — shrink the problem:

1. Isolate the member with `-i file@line`.
2. Bisect inside the body: put `assume false` partway through and move it. The
   half that still hangs contains the cause.
3. Wrap the suspicious region in an `outline` statement with a contract. This
   verifies that region against its own contract, so errors get localized to
   the region and reported instead of the verifier spinning forever. This was
   the standard tool for exactly this situation in VerifiedSCION.
4. Cheap checks with a high hit rate: a quantified assertion in the region with
   no trigger or a bad one, or a reslicing operation `x[a:b]` in the region
   (see the common culprits in step 5) — either alone can explain a hang.
5. If the region still hangs and the cause isn't visible, run SMTScope on it
   (step 6): divergence produces an unbounded trace, so cap it with
   `SCOPE_SIZE_LIMIT` or kill Z3 after a couple of GB — a matching loop will be
   visible in the prefix.

## Report the diagnosis

Finish with something the next step can act on — for each bottleneck:

- **Member** (file:line) and its measured time, plus the share of package time.
- **Classification** from the table above, in one sentence.
- **Evidence**: the numbers you measured, not an argument from the source.
- **Reproduce command**: the exact isolated `gobra -i ...@line` invocation, so
  any fix can be measured against the same baseline.
- **Uncertainty**, if any: say what you could not confirm rather than guessing.

Then hand over to `gobra-improve-perf` for the fixes — it expects exactly this
information and will re-measure against your baseline.
