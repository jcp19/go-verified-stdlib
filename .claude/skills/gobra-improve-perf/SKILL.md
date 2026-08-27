---
name: gobra-improve-perf
description: Speed up slow Gobra verification and validate that each fix actually helped, reverting the ones that don't. Use whenever Gobra verification is too slow, times out, or diverges and someone wants it fixed or asks how to make it faster — including requests about outline statements, opaque functions, predicates, the chopper/slicing, moreJoins, exhaleMode, quantified permissions, or triggers. If available, pair this skill with `gobra-debug-perf`, which locates the bottleneck first.
---

# Improving Gobra verification performance

Gobra verifies Go via Viper/Silicon and Z3. Verification time is roughly the
**number of symbolic execution paths** times the **cost of each SMT query**,
and query cost is dominated by the **proof context** (every axiom, function
body, path condition, and heap chunk shipped to Z3 alongside the real goal),
and by the theories in which the generated assertions fall (assertions about
non-linear integer arithmetic are extremely slow). When talking about the context,
quantified assertions are very costly as they relly on e-matching and triggering
to be instantiated, and it may often lead to matching loops (read about it here:
https://viper.ethz.ch/tutorial/quantifiers.html).

When a part of the program is too slow, there are a few things to try out:
cut paths, or cut context.

Two facts should shape how you work here, both learned the hard way on a large
Gobra project:

- **No configuration is universally best.** The same flag that gives a 3.5×
  speed-up on one function makes another 10× slower or introduces spurious
  errors. Optimization is per-member and empirical.
- **Unmeasured changes usually cost more than they save**, in verification time
  *and* in annotation burden that someone has to maintain forever.

Hence the protocol below is not ceremony; it's the part that makes the rest work.

## The protocol: one change, measured, kept or reverted

1. **Get a baseline.** Use the isolated-member command from `gobra-debug-perf`
   (`gobra -i pkg/file.go@412 --gobraDirectory ./gobra-out`), run it twice, and
   record the time. Without an isolated reproduce loop you will be waiting
   45 minutes per experiment and will stop measuring.
2. **Apply exactly one change.**
3. **Re-measure the same way**, twice. Differences under ~10% are noise.
4. **Keep it only if it wins.** Otherwise `git checkout` the change and say so.
   A change that adds annotations for a 3% gain is a loss.
5. **Re-verify the whole package before you finish.** Per-member speed-ups can
   slow down or break other members, and some options change *completeness* —
   a member can start reporting a spurious error.

Record what you tried and what it did, including the failures. "Making `Bytes`
transparent times out after 6h" is as valuable to the next person as any win.

## Pick a strategy from the diagnosis

If `gobra-debug-perf` classified the bottleneck, start here rather than reading
the whole catalogue:

| Diagnosis | Try, in order |
|---|---|
| Path explosion | `moreJoins(impure)` (§4) → `outline` the branchy region (§3) → split branchy predicates (§2) |
| Quantified-permission cost | Wrap footprints in predicates (§2) → `outline` the unfold/fold region (§3) → `exhaleMode(0)` if the member has no disjunctive aliasing (§4) |
| Context size / everything slow | `--chop N` (§1) → `opaque` on big pure functions (§2) |
| Inherited cost from a dependency | Fix the predicate or function itself (§2) — optimizing the caller won't help |
| Quantifier blow-up or matching loop | Triggers (§5) first; nothing else matters until the loop is gone |

## Strategy catalogue

Ordered by how much they typically buy relative to what they cost you. Start at
the top; stop when the member is fast enough.

### 1. Automatic slicing (free, no annotations)

`--chop N` splits the package into at most `N` Viper programs, each carrying
only the context its members can depend on, and verifies them separately. On a
large project this alone gave ~11% off the total: the number of SMT queries
goes *up* (context is duplicated across slices) while total SMT time goes
*down*, and long queries (>1s) nearly halve.

Try this first because it costs nothing and touches no source. It also composes
with everything below — and it gets more effective the more information hiding
you do (next section), since hidden bodies are pruned from slices.

### 2. Hide information (the biggest lever)

The proof context is the root cause of most slowness, and these are the tools
that shrink it.

**Abstract predicates instead of quantified permissions.** Quantified
permissions are the most expensive proof obligations in practice: computing the
permission held for a location covered by several quantified chunks makes Z3
case-split, in the worst case exponentially in the number of chunks that may
provide permission. Wrapping them in a predicate keeps them out of the context
until you unfold:

```go
// instead of threading `forall i int :: 0 <= i && i < len(s) ==> acc(&s[i])`
// (i.e. acc(s)) through every contract that touches the slice:
pred Bytes(s []byte) {
    forall i int :: 0 <= i && i < len(s) ==> acc(&s[i])
}
```

This is the highest-value single change on byte-slice-heavy code — inlining such
a predicate and dropping its `fold`/`unfold`s pushed a 45-minute verification
past a 6-hour timeout. It matters most when several slices are live at once,
because Silicon must then consider that they may overlap.

**`opaque` functions with explicit `reveal`.** Every non-opaque pure function
contributes a universally quantified axiom equating calls to its body. Mark
functions whose body is large or needed only in a few places as `opaque`, and
reveal them where the definition is genuinely required:

```go
ghost
decreases i
opaque
pure func fac(i int) int { return i <= 1 ? 1 : i * fac(i-1) }

// at the (few) places that need the definition:
tmp := reveal fac(3)
```

Used at scale this is decisive: on VerifiedSCION, removing all `opaque`/`reveal`
annotations pushed verification past a 6-hour timeout.

**Split branchy predicates.** A predicate whose body contains N impure
implications (`d.f != nil ==> acc(P(d.f))`) forks 2^N paths at *every* unfold
site — a predicate that itself verifies in 3 seconds can dominate the package
this way. Moving each implication into its own predicate, unfolded on demand,
removes that branching. Weigh it honestly: it is a large annotation change to a
central data structure, and it may not be worth it if the backend options in §4
already cut the paths.

### 3. `outline` statements (split a function without touching the code)

An `outline` statement verifies a block of statements against its own contract
and treats it as opaque where it occurs — the frame rule applied at statement
level. It has the effect of extracting a helper function, but shares the
enclosing scope, so no arguments or return tuples to thread:

```go
requires Bytes(s)
ensures  Bytes(s)
ensures  /* functional spec of the block */
outline (
    unfold Bytes(s)
    // statements that read and modify the slice
    fold Bytes(s)
)
```

This is the right tool when you cannot refactor the Go code (verifying existing
code as-is), and it does four things: the precondition prunes context for the
block; facts established inside — especially quantified ones — do not leak into
the rest of the function; branching inside the block is hidden from the
enclosing member; and each outline can be verified independently.

Realistic expectations: measured speed-ups ranged from ~1.4× down to slight
slowdowns. The consistent win is elsewhere — **`outline` localizes errors and
tames divergence.** A member that spins forever with no output often terminates
with a precise error once the suspect region is outlined. Many outlines are
worth introducing while proving a member and deleting once it verifies.

Restrictions: no `return` inside an outline, and no `break`/`continue` targeting
a loop outside it. Use `before(x)` (not `old(x)`) to refer to the pre-state of
the block.

#### Prefer a ghost lemma to an `outline` when the block allows it

The context-pruning is not special to `outline`: **a lemma's proof context is
exactly its precondition**, so a ghost lemma with the same contract prunes
identically. What it adds is that it is reusable across call sites, lives in
`lemmas.gobra` where ghost code belongs, and can be verified on its own in
seconds instead of by re-running the enclosing member.

The `return` restriction is the reason to care, not a detail. In a loop that
searches and returns on success, the branch that most needs a small context is
the one containing the `return` — and that is exactly the branch `outline`
cannot cover. On a Rabin-Karp search, outlining the fall-through was the first
thing that made the member verify in isolation, and the package run still
failed, in the `return` branch that had to stay inline. Moving the same
contracts into two lemmas — one per branch — verified the package. Reach for
`outline` when the block genuinely cannot be a lemma (it needs locals the rest
of the function uses, or `before(x)`); otherwise write the lemma.

### 4. Backend algorithm options (cheap to try, per-member)

These change how Silicon generates proof obligations. Set them **per member**
with `#backend[...]`, placed with the member's specification — that keeps the
knowledge attached to the code that needs it instead of in someone's shell
history:

```go
requires acc(x) && acc(y)
ensures  acc(z)
#backend[moreJoins(impure), exhaleMode(1)]
func f(x, y, z *int) { ... }
```

`#backend` also works on `outline` statements and closures. The same options
exist globally on the CLI: `--moreJoins off|impure|all`, `--mceMode off|od|on`
(`on` = `exhaleMode(1)`, `od` = `exhaleMode(2)`), and
`--conditionalizePermissions`. Prefer per-member annotations for exceptions and
CLI flags only for the project-wide default.

| Option | What it does | When it helps |
|---|---|---|
| `moreJoins(impure)` | Joins paths right after impure implications/conditionals | The first thing to try on branchy members. Cut one function from 118 terminal paths / 71s to 16 paths / 20s |
| `moreJoins(all)` | Also joins after `if` statements | Only for extreme path counts. Frequently *much* worse (one function: 20s → 194s) and can introduce spurious errors |
| `moreJoins(off)` | Gobra's default — no extra joining | Restore when joining hurts |
| `exhaleMode(0)` (greedy) | Cheaper heap obligations, incomplete under disjunctive aliasing | Members with no disjunctive aliasing. Only switch a member to greedy *after* it verifies, or you cannot tell incompleteness from a real error |
| `exhaleMode(1)` (mce) | Complete but more expensive heap reasoning | Gobra's default (`--mceMode on`). Required when a reference may alias one of several others |
| `exhaleMode(2)` (on demand) | Greedy first, consolidate and retry on failure | Sounds ideal, measured badly: heap queries nearly tripled and total time went from ~2650s to ~3800s with runs timing out. Don't reach for it by default |
| `--conditionalizePermissions` | Rewrites `b ==> acc(e, p)` to `acc(e, b ? p : none)`, joining without merging states | Mixed results per member, but often good globally. Blocked when the resource mentions a heap location (e.g. `P(x.f)`) |
| `stateConsolidationMode(...)` | Tunes when Silicon merges heap chunks | Last resort, measure carefully |

Because these interact, a small grid over `{moreJoins} × {conditionalizePermissions}`
on the isolated member is a reasonable use of time when one member dominates.
Global default that worked well in practice: joins on impure expressions plus
permission conditionalization, with per-member overrides for the stragglers.

Two cautions. `moreJoins` is currently not applied when verifying predicates and
pure functions, so a member dominated by those will not respond to it. And
`--parallelizeBranches` genuinely speeds things up but causes SMT variable
renamings across runs, which surfaces instability and spurious errors — treat
its speed-up as unavailable unless stability is measurably fine.

### 5. Quantifier and trigger hygiene

Most of what makes SMT-based verification unpredictable is quantifier
instantiation. This is standard across verifiers, and the advice transfers:

- **Always give explicit triggers** on quantified assertions, and choose the
  most restrictive ones that still fire. `--requireTriggers` enforces this
  project-wide and is worth turning on.
- **A fact with the wrong trigger is not a fact.** A quantified hypothesis
  whose pattern names a term the *goal* never mentions sits in the context and
  never fires — indistinguishable, from the error message, from a fact you
  forgot to establish. Before adding a missing step, check whether the step is
  already there under a pattern nothing matches. When one hypothesis serves two
  consumers that write the window differently, give it both patterns as
  alternatives rather than duplicating the assertion:

  ```go
  // {&s[lo:hi][k]} for the permission reasoning, which writes addresses;
  // {seq(s)[lo+k]} for the pointwise reasoning, which never mentions them
  assert forall k int :: {&s[lo:hi][k]} {seq(s)[lo+k]} 0 <= k && k < hi-lo ==>
      &s[lo:hi][k] == &s[lo+k]
  ```

  Arithmetic in an *index* (`seq(s)[lo+k]`) is a legal pattern; only arithmetic
  in a slice *bound* (`s[i-n:i]`) is rejected — see the trigger notes in
  `gobra-debug-perf`.
- **Establish a fact before the branch that consumes it**, not merely where the
  invariant needs it. A lemma call at the end of a loop body re-establishes the
  invariant, but every branch *inside* the body ran without it. In a Rabin-Karp
  search the rolling-hash step sat at the end of the body, so the window test
  did not know `h` to be the hash of the window it was about to compare — which
  is precisely the fact that refutes a match on the common path. Moving the
  same lemma call above the test cost nothing and unblocked a proof that had
  been written off as too slow. Symptom to watch for: an obligation inside a
  branch that looks like it should follow from the invariant "one step later".
- **Watch for matching loops**: a trigger whose instantiation produces a new
  term matching the same trigger diverges. If profiling shows a *user-provided*
  matching loop, fix it — that is a real bug, not a tuning issue. Loops
  originating in Z3's datatype theory or Silicon's collection axiomatizations
  cannot be fixed from your source; recognize and move on.
- **Keep quantifiers out of ambient context**: put them inside predicates or
  opaque function bodies and expose them only where needed. This is the same
  idea as §2, applied to logic rather than to permissions.
- **Prefer many small proofs over one big one.** In Gobra, use ghost lemma
  functions (with `requires`/`ensures`) or an `outline` block to keep an
  intermediate proof's facts from leaking into the rest of the member. Note
  `assert P by { ... }` (the proof form) is currently rejected by Gobra's type
  checker; `assert P by contra { ... }` and `asserting e1 in e2` do work.
- **Avoid non-linear arithmetic** where you can; prove it in small steps in
  dedicated lemmas. `--disableNL` keeps it out of everything else.
- **Do not "repair" a rejected trigger by adding a permissive valid one.** When
  `gobra-debug-perf`'s consistency check reports an invalid pattern, the
  tempting move is to swap in something that parses. Measured on a Rabin-Karp
  search: replacing `{seq(s)[lo+k]}` with `{pat[k]}` — a pattern that matches
  nearly everywhere — took the package from 738s and verifying to 578s and
  *failing*. Deleting the invalid pattern with no replacement was the variant
  that helped (standalone Silicon went from failing at 8m22s to verifying in
  7m24s), which `--requireTriggers` will not let you write if it was the
  quantifier's only pattern. Treat an invalid trigger as a diagnosis, not a
  to-do: it tells you the quantifier is firing on something other than what
  you intended.

### 5c. Never make a caller prove a disjunction

A lemma precondition of the form `A || B` is the single most expensive shape
found in a real Gobra proof: on a Rabin-Karp search, one such clause was
**65% of the package's entire prover time** — five queries, 321s, the worst
91s — and it failed often enough to make the run time bimodal (~330s or ~750s
for identical source).

The reason is structural. Given a path condition like `!(h == hashsep &&
Equal(w, sep))`, proving `h != H || seq(w) != pat` is one goal with no branch
for Z3 to take: it has to connect both disjuncts to the negated conjunction at
once. Each disjunct *on its own path* is a one-step goal.

The shape to reach for is one lemma per failure mode, selected by a `ghost if`
on the discriminating condition:

```go
//@ ghost if h != hashsep {
//@ 	lemmaExtendByHash(...)     // arithmetic only, no slices
//@ } else {
//@ 	lemmaExtendByWindow(...)   // the byte-level path
//@ }
```

Be honest about the outcome, though: on that codebase the split *fixed the hot
query and made the member slower overall* (1960s, new failure elsewhere),
because the extra branch multiplied the surrounding context. So treat this as
a strong diagnostic signal — a disjunctive precondition is where to look
first — and measure the split like any other change rather than assuming it
wins.

### 5b. Rewrite the specification, not just the proof

The costliest thing in a slow member is often a modelling choice in the spec
functions it mentions. These rewrites are worth checking before any tuning
flag, because each removes a whole class of terms from *every* obligation
rather than shaving one query. On a Rabin-Karp search over byte slices they
compounded to 42m → 10m41s with no change to the Go code.

**Know which of the two "window" terms you are writing.** For a byte slice `s`,
`seq(s[lo:hi])` (reslice, then convert) and `seq(s)[lo:hi]` (convert, then
slice the sequence) denote the same bytes and cost wildly different amounts:
the first is a plain slice-to-seq term, the second is nested
`Seq_take`/`Seq_drop`. You will meet both, because contracts like `Equal`'s
hand you the first while specifications written over `seq(s)` want the second,
and the obvious bridge is one ground equality:

```go
assert seq(s[lo:i]) == seq(s)[lo:i]   // verifies in seconds, and is a trap
```

It does verify. It is also enough on its own to take a Rabin-Karp search loop
from 32s to an out-of-memory kill of Z3 — measured *before* any new
postcondition was added — because from that line on, every obligation in the
loop carries the `Seq_take`/`Seq_drop` terms. Bridge pointwise instead, inside
a lemma, so no sliced sequence ever enters the caller's context. The general
form of the mistake: a cheap-looking assertion that introduces one expensive
*term* is not cheap, because terms persist and assertions do not.

**Replace sequence slicing with a recursive range form.** A definition like

```go
pure func MatchesAt(q, pat seq[byte], j int) bool {
	return q[j : j+len(pat)] == pat          // nested Seq_take/Seq_drop
}
```

makes every obligation mentioning it expensive. The range form has no slicing
and, being recursive rather than quantified, needs no trigger at all:

```go
pure func MatchesAtRange(q, pat seq[byte], j, k int) bool {
	return k == 0 ? true : (q[j+k-1] == pat[k-1] && MatchesAtRange(q, pat, j, k-1))
}
opaque pure func MatchesAt(q, pat seq[byte], j int) bool {
	return MatchesAtRange(q, pat, j, len(pat))
}
```

Then give callers lemmas whose *contracts* are pointwise, so slicing never
enters the caller's context. Both directions are needed in practice: one lemma
from pointwise equality to the range form, and — for refutation, where a
sequence disequality gives you no witness index — one taking the window
sequence and closing by contradiction through extensionality.

**State contracts in one heap.** Sequence equalities relating two heaps, as in
`ensures seq(s) == old(seq(s))`, are a minefield: every obligation carries two
parallel families of terms plus the bridge between them. When the callee only
*reads* a buffer and the caller keeps a fraction of the permission across the
call, the caller gets value stability from framing for free, so the clause is
redundant — drop it and phrase every postcondition against the current state.
Watch for contracts that are inconsistent about this (some clauses in `old`,
some not); those pay the cost without anyone having decided to.

Inside a loop this feels unsafe, because Viper havocs the values covered by the
invariant's permissions and `acc(s, p)` alone does not pin them. It is fine as
long as *every* fact is stated against the current heap: the invariant carries
its facts relative to whatever the current heap is, the body reads from that
same heap and re-establishes them there, and nothing ever compares two heaps.
The framing conjunct is only load-bearing when other clauses are phrased in
`old`.

**Name arithmetic out of trigger patterns.** When `gobra-debug-perf` reports a
trigger Silicon rejects, the cause is usually an interpreted operation in the
pattern, and a ghost variable for the offending subterm fixes it without
touching the Go code:

```go
//@ ghost lo := i - n
//@ assert forall k int :: {&s[lo:i][k]} 0 <= k && k < n ==> &s[lo:i][k] == &s[lo+k]
```

`{&s[i-n:i][k]}` is invalid because the bound `i-n` is a subtraction inside the
pattern; `{&s[lo:i][k]}` is legal, and `lo == i-n` links the two by congruence.
Arithmetic in the quantifier *body* is unrestricted. The alternative idiom — a
dummy pure function over the quantified variables, used as the trigger — is
worth knowing, but prefer renaming when it applies: a helper only fires where
you mention it, and the terms Silicon generates internally (e.g. `ShArrayloc`
when computing permissions) will not mention it.

**The same trap in a loop invariant.** Pinning part of an abstraction with
`s[:k]` or `s[k:]` in an invariant re-derives the slice through those same
take/drop axioms on every iteration. Track a ghost accumulator and state a
full-sequence equality instead:

```go
//@ invariant l.Es() == es0 ++ nes && len(nes) == len(oes0) - i   // cheap
//@ invariant l.Es()[:len(es0)] == es0                            // diverges
```

On `container/list` this took `PushFrontList` from not terminating to a
whole-package run under four minutes, and the accumulator form is the
*stronger* spec — it names the new elements, which the method returns as a
ghost result.

### 6. Borrowed wisdom from Dafny and Verus

These verifiers hit the same wall and document the same cures — useful both as
corroboration and for ideas Gobra users under-use:

- **Dafny**: hide function bodies with `opaque` + `reveal`; scope local proofs
  with `assert P by { ... }`; move proof sequences into lemmas; make
  preconditions and invariants opaque via labels; break large definitions into
  small ones with clean contracts; `--isolate-assertions` to find the expensive
  assertion; judge cost by Z3 **resource count** (deterministic) rather than
  wall-clock time, and treat high variance across random seeds
  (`dafny measure-complexity --iterations N`) as a predictor of future
  breakage. The framing worth stealing: give the solver *exactly* the facts it
  needs — missing facts fail, irrelevant facts are just as fatal.
- **Verus**: `--time` / `--time-expanded` for per-function breakdowns,
  `--profile` (on timeout) and `--profile-all` (on slow successes) to rank
  quantifiers by instantiation count, `--rlimit 1` to keep profiling data
  small, `--verify-function` to target one function; `assert(F) by { P }` so
  `P`'s facts prove `F` and nothing else; `opaque`/`reveal`; conservative
  trigger selection.

The Gobra analogue of "isolate assertions" is `-i file@line` plus `outline`;
the analogue of `--profile` is a Silicon prover log analyzed for quantifier
instantiations. The mental model is identical.

### 7. Reshape the loop invariant

An invariant rewrite that is about proof *shape* rather than about which terms
a spec function builds (for that, see §5b).

**Split the invariant by mode instead of relating two structures.** When a
loop can walk its receiver or a separate object (`other == l` vs `other != l`),
the tempting invariant is one clause phrased over the *walked* object, e.g.
"the cursor `e` is `other.Es()[i-1]`". That clause is cheap in one mode and
poisonous in the other: when `other == l`, `other.Es()` is the sequence the
loop body is *mutating*, so the clause has to be re-derived every iteration by
pushing the aliasing equality through the callee's postcondition — and because
it is one clause, the solver repeats that case split for every use of it.
Stating each mode separately makes each disjunct follow directly from a
postcondition the callee already gives you, with no aliasing step:

```go
// walking `other` to prepend onto `l` (PushFrontList)
//@ invariant i > 0 && other != l ==> e == oes0[i-1]                // frozen: index the snapshot
//@ invariant i > 0 && other == l ==> l.Es()[len(oes0)-1] == e      // aliased: index l, at a fixed spot
```

The second clause is not a translation of the first. `other != l` freezes
`other`, so the snapshot `oes0` taken before the loop still describes it. Under
`other == l` there is nothing frozen to index, so the invariant instead names
where the cursor sits *in the growing list* — a constant index, because each
round prepends exactly one element ahead of it. Finding that constant is the
work; once found, both clauses are one-step.

## Things that don't work (don't rediscover them)

- **Moving heap-independent ghost work before the heap writes.** Plausible
  story, no effect. The idea: sequence-shape assertions (`len`, index mappings)
  mention only ghost sequences, so hoisting them above the pointer surgery
  should prove them against a smaller context. Measured on `container/list`,
  moving the block of six such assertions across the four writes in `insert`
  gave 30.4s → 29.7s, and the same move in `remove` gave 27.6s → 29.4s. Both
  are inside the noise band. Order the ghost code for readability instead.

  The rule is self-defeating, which is visible from the obligations alone.
  Silicon evaluates such an assertion to a goal over local sequence terms —
  no heap read, no permission check — so moving it past a field write leaves
  the **goal term identical** and only grows the context (`π_before ⊆
  π_after`). Two things follow: hoisting can never fix a failure, only shave
  cost; and the cost it shaves is not "number of new facts" but *number of new
  ground terms matching a trigger of a quantifier reachable from the goal*.
  Four scalar writes contribute about one (`es0[inv(at)]`, from resolving
  `acc(at.next)` against the quantified chunk) — and the breadcrumb asserts
  that name the neighbours already fired those quantifiers at the same
  indices, before the writes, in *both* arrangements.

  So: if the work really is heap-independent, a write cannot invalidate it and
  there is nothing to buy. If it is heap-*dependent* — it mentions `l.Es()` or
  a field — placement matters enormously, because a heap-dependent function
  application carries a snapshot argument and `l.Es()` after a write is a
  different term. But that case is not "heap-independent ghost work"; it is
  the ordinary discipline of snapshotting before you mutate. The name asserts
  the precondition under which the justification cannot apply.

  Where the context-size channel *does* pay is when the intervening code adds
  volume or fresh symbols: a loop (its head havocs everything outside the
  invariant, so facts are lost rather than diluted — hoisting is mandatory
  there, not an optimization), a method call, QP writes inside a loop, or an
  intervening `unfold` of another predicate.

- **Selecting heap algorithms per member before the member verifies.** You
  usually cannot predict whether a function exhibits disjunctive aliasing, so
  you cannot tell an incompleteness from a genuine error. Switch a member to
  `exhaleMode(0)` only after it verifies with mce.
- **`exhaleMode(2)` (greedy with fallback) as a global default** — see the
  table; it made things substantially worse and less stable.
- **Buying speed with `trusted`, `assume`, or deleted postconditions.** That is
  not an optimization, it is a hole in the proof. If you ever do this
  deliberately as a temporary measure, say so loudly in the report.

  A weakened postcondition is the subtler version: still sound, but a spec
  regression, and usually a symptom rather than a cause. Before you drop a
  clause, re-encode the invariant that supports it (§5b, §7) — in
  `container/list` the postcondition that "looked too expensive to keep" was
  cheap under a ghost accumulator, and the **stronger** spec verified in 3m41s
  where the weaker one took 5–9 minutes. Stronger does not imply slower.

  The same asymmetry bites when you weaken a contract for *tidiness* rather
  than for speed. Dropping `e.next == old(e.next) && e.prev == old(e.prev)`
  from a postcondition — on the correct reasoning that no client can observe
  either field — left the caller holding an element with two symbolic pointers,
  and took a test chain from 1m44 to a 20s assert timeout. Removing a fact the
  solver was using costs time even when the fact was invisible in the API.
  Measure a weakening exactly like a strengthening.

- **Assuming breadcrumb assertions are free.** They are a change like any
  other and must be measured. An `assert` restating a whole abstraction
  equality can cost more than the step it was meant to cheapen: adding six of
  them to a test chain took a package from 4m02 to 6m28 *and* pushed a new
  failure elsewhere. Useful breadcrumbs name one small fact (a neighbour, an
  index); wholesale restatements of the state usually are not.
- **Chasing a member you haven't measured.** Slow *predicates* and small pure
  functions are frequently the real culprits behind a slow method, because their
  cost is paid at every unfold or call site.
- **Adding assertions to "help" the solver.** When a step fails on a timeout
  rather than on a missing fact, every intermediate assertion you add is one
  more query against the same budget. Capturing a loop invariant in a ghost
  variable before the induction variable moves — the textbook fix for "the
  invariant is there but not in this form" — cost 36s on its own in one member
  and pushed the run from 31m to a 50m timeout. Decomposition helps when the
  solver lacks a fact; it hurts when the solver lacks *budget*, and
  `gobra-debug-perf` tells you which.
- **`reveal`ing an opaque function inside a hot loop.** Making a function
  `opaque` and then revealing it at a call site in the loop body puts the
  expensive definition straight back into the context that needed protecting —
  in one case worse than never making it opaque (24m + an out-of-memory kill of
  Z3, against 24m and a clean failure). Introduce the fact with a ghost lemma
  instead, so the unfolding happens in the lemma's own small context and the
  caller receives only its `ensures`.

## Reporting

Close with a short table: member, baseline time, change applied, new time,
kept/reverted. Then state the whole-package time before and after, confirm the
package still verifies with zero errors, and list any member that now depends on
a completeness-affecting option (`exhaleMode(0)`, `moreJoins(all)`) so it is
obvious where to look if a spurious error appears later.
