---
name: gobra-locate-failure
description: Find the cause of a Gobra verification failure by applying proof actions — small, verifier-checked rewrites of the failing proof that narrow "this member does not verify" down to one obligation, one statement, and one missing fact. Use whenever Gobra reports an error whose cause is not obvious: "Assert might fail", "Postcondition might not hold", "Precondition of call ... might not hold", "Loop invariant might not be established" or "... might not be preserved", "Permission to ... might not suffice", "Fold might fail", "Unfold might fail", "Assertion ... might not hold", overflow errors, termination errors. Also use when someone asks "why doesn't this verify", "which conjunct is failing", "where did my permission go", "is this a real bug or a missing hint", or when a quantified fact is in scope but does not fire.
---

# Locating the cause of a Gobra verification failure

Gobra tells you *that* an obligation failed and *what* the obligation was. It
never tells you *why*: which facts were in context, which quantifier did not
fire, where a permission went — none of that is observable from the output.
Guessing at extra annotations is the default response, and it is why proof
debugging eats days.

The method that works treats the verifier as the instrument. A **proof action**
is a small, mechanical rewrite of the *source-level* proof — an assertion, a
contract clause, a lemma — chosen so that the verifier's answer to the
*rewritten* program tells you something the original answer did not. Apply one,
re-run, read the change. This is the idea of **ProofPlumber** (Cho, Zhou,
Bosamiya, Parno; *A Framework for Debugging Automated Program Verification
Proofs via Proof Actions*, CAV 2024), which implements 17 such actions for
Verus. This skill is that catalogue transposed to Gobra, plus the actions Gobra
needs and Verus does not: permissions, folding, and triggers.

Two rules make the rest work.

- **A proof action is a probe, not a fix.** It exists to produce information.
  Probes come back out of the source before you commit, and the member is
  re-verified without them (§6).
- **One action per run, against a recorded baseline.** "It still fails" is not
  an observation. "It fails at the same position with the same reason" is.

## Action index

| # | Action | ProofPlumber counterpart | Use when |
|---|---|---|---|
| 3.1 | Decompose the obligation | *Decompose Failing Assertion* | Any failing assertion or clause with `&&` |
| 3.2 | Materialize the obligation | *Insert Failing Postcondition* / *Precondition* | The error is on a contract, not an `assert` |
| 3.3 | Walk the fact up | *Weakest Precondition Step* | You know *what* fails, not *where* |
| 3.4 | Snapshot and compare | — (Gobra-specific) | The fact is heap-dependent |
| 3.5 | Introduce the hypothesis | *Convert Implication to If* | The goal is `A ==> B` |
| 3.6 | Introduce the bound variable | *Introduce Forall-Implies* | The goal is quantified |
| 3.7 | Instantiate at a witness | — (Gobra-specific) | Quantified goal, suspect triggers |
| 3.8 | Reveal the definition | *Reveal Opaque* | Goal mentions `opaque` or a predicate |
| 3.9 | Case-split | *Split Inequality* | `<=`, `!=`, disjunction, `nil` checks |
| 3.10 | Bounds and reslicing facts | *Sequence Index In-Bounds* | Goal mentions `q[i]` or `x[a:b]` |
| 3.11 | Localize the permission | — (Gobra-specific) | `Permission to ... might not suffice` |
| 3.12 | Scope the region | *Insert Assert-By Block* | Long body, or the member diverges |
| 3.13 | Weaken the contract | *Split Implication in Ensures* | Diagnosing a postcondition, temporarily |

## 1. Read the error before touching anything

Gobra prints each verification error as `<file:line:column>` followed by the
**error** — which obligation failed — and, on the next line, the **reason** —
why the backend could not discharge it:

```
<src/internal/bytealg/bytealg.go:191:6> Assert might fail.
Assertion forall k int :: 0 <= k && k < n ==> &s[lo:i][k] == &s[lo+k] might not hold.
```

The two lines carry different information and you need both. The error names the
*kind* of obligation, which picks the action; the reason names the *goal*, which
is what you decompose.

```bash
python3 .claude/skills/gobra-locate-failure/scripts/triage_errors.py gobra-run.log
```

The script parses a run's output into one row per error — position, error class,
reason class, and the first action to try — and deduplicates repeats. Collect
the log with `--noStreamErrors` so errors arrive grouped per package instead of
interleaved with progress output.

**What the error tells you:**

| Error | Obligation | First action |
|---|---|---|
| `Assert might fail` | An `assert` you wrote | §3.1, then §3.3 |
| `Postcondition might not hold` | An `ensures` clause at a return | §3.2 |
| `Precondition of call ... might not hold` | A callee's `requires` at a call site | §3.2 |
| `Loop invariant might not be established` | Invariant at the loop head, on entry | §3.2 (assert before the loop, init value substituted) |
| `Loop invariant might not be preserved` | Invariant at the loop head, after the post statement | §3.2 (assert at the end of the body, post statement substituted) |
| `Fold might fail` / `Unfold might fail` | The predicate body / the instance | §3.11 |
| `Assignment might fail` | Permission to the assigned location | §3.11 |
| `Expression may cause integer overflow` | Bounds of a subexpression | §3.1 on the arithmetic |
| `Function might not terminate` / measure errors | `decreases` | §3.4 on the measure |
| `The pure function is not well-formed` | Preconditions of the body's own calls | §3.2 with `asserting … in` |
| `Method contract is not well-formed` | Self-framing of the contract | The contract reads state it does not own |
| `Generated implementation proof ... failed` | Interface method contract vs. implementation | Compare the two contracts before probing |

**What the reason tells you:**

| Reason | Meaning |
|---|---|
| `Assertion <e> might not hold.` | A logical fact is missing (or unprovable) |
| `Permission to <e> might not suffice.` | A *resource* is missing — a different problem entirely (§3.11) |
| `Index <i> into <e> might exceed sequence length.` / `might be negative.` | Well-definedness, not the property (§3.10) |
| `Expression <e> might cause integer overflow.` | Bounds; consider `integer` (see `gobra-review-code` §5) |
| `Quantified resource <e> might not be injective.` | A quantified permission whose receiver expression is not visibly injective |
| `Divisor <e> might be zero.` | Well-definedness |
| `Termination measure might not decrease.` | The measure, not the property |
| `Assertion <e> definitely holds.` | You ran a `refute`: the state is unreachable, or the assertion always holds (§5) |

Two facts about the error *list* that mislead people constantly:

- **Silicon stops a member at its first failing obligation.** The list is a
  lower bound: fixing one error routinely reveals three more, and that is not a
  regression. You do not have to peel them off one run at a time — dump the
  Viper program and raise the limit (§2 Q1):
  `silicon --numberOfErrorsToReport 0 pkg/b.go.chopped0.vpr`.
- **A reason mentioning permission is never a missing-fact problem.** Do not
  reach for lemmas and asserts; go to §3.11.

## 2. Triage: three questions, before any probing

Every action below assumes the failure is a genuine proof gap. Three cheap
checks decide whether it is. Answer them in this order; each is one run.

### Q1. Is the failure on a path that can actually happen?

Silicon forks on `if`, on impure implications and conditionals, and inside
`unfolding`. An obligation is reported if it fails on *any* path, so the first
question is which one — a goal that is unprovable only on a branch you believed
was impossible needs the branch ruled out, not the goal proved.

```bash
gobra -i pkg/b.go@412 --printVpr
silicon --numberOfParallelVerifiers 1 --enableBranchconditionReporting \
        --numberOfErrorsToReport 0 pkg/b.go.chopped0.vpr
```

`--enableBranchconditionReporting` attaches the branch conditions to each error.
`--numberOfErrorsToReport 0` lifts Silicon's default of stopping a member at its
first failure, so you see the whole set at once instead of peeling them off one
run at a time — worth doing before you invest in any single one.

**What this question is not.** It is tempting to probe the failing position with
`assert false` to check the context is not inconsistent. That check is worth
running, but never here: an inconsistent state proves *everything*, so an
obligation that fails has already demonstrated that its own state is consistent.
`assert false` at a failing position cannot succeed, and a "passing" vacuity
check there means you moved the probe, not that you learned something.

The vacuity check belongs in the two places where it can actually fire: before
believing a probe that **passed** (§5), and on the member once it **verifies**
(§6). The mechanics are there.

### Q2. Is it a proof gap or a budget problem?

With an `assert_timeout` set (this repo: 30s for `internal/bytealg`), a query
that runs out of budget is reported *exactly* like a refuted one. Re-run the
isolated member with a much larger timeout:

```bash
gobra -i pkg/b.go@412 --assertTimeout 300000
```

If it now passes, stop. This is not a missing fact and nothing in §3 applies —
hand over to `gobra-debug-perf`. Worse, probing makes it *harder*: every assert
you insert is another query against the same budget, so a decomposition can
"fix" a timeout without telling you anything true.

Tells that you are looking at a timeout: the step is trivial (linear arithmetic,
or congruence from the line above), or it is the last obligation in a long
member where the context is largest.

### Q3. Is the property actually true?

Before proving harder, try to refute. Gobra's assign-such-that statement asks
the solver for a witness, so it is a genuine refutation probe:

```go
//@ var k int :| 0 <= k && k < n && !P(k)     // verifies => your `forall` is false here
```

If that verifies, Gobra proved a counterexample index exists in this context and
your quantified goal cannot be proved because it is *wrong* — provided the
context is consistent, since an inconsistent one produces a "witness" for
anything. Check that with `refute false` at the same position (§5) before
acting on a successful refutation. If the probe fails instead ("Witness for
assertion ... not found"), the result is inconclusive: a context that cannot
prove `P(k)` usually cannot prove `!P(k)` either. Carry on with §3.

If the false property is a postcondition of the code as written, you have found
a bug, not a proof gap. Say so loudly and separately: that is the outcome
`gobra-specify-verify` cares about most.

## 3. The action catalogue

Every entry has the same shape: what it applies to, the rewrite, and — the part
that matters — **how to read the outcome**. Apply one at a time. Before you
start, get the fast reproduce loop from `gobra-debug-perf`:

```bash
# pass every file of the package; attach @line only to the member you target
gobra -i pkg/a.go pkg/b.go@412
```

You will spend 5–20 runs here. At package speed you will stop measuring and
start guessing.

One property of Gobra's `assert` makes this whole approach viable on resources:
**`assert` checks without consuming.** Unlike `exhale`, it leaves the permission
state untouched, so `assert acc(&x.f)` is a read-only measurement and can be
inserted anywhere without disturbing the proof around it. `assume`, `inhale`,
`exhale`, `fold` and `unfold` are *not* probes in this sense — they change the
state, and everything downstream of them is a different program.

### 3.1 Decompose the obligation

*The highest-yield action, and the one to try first on anything logical.* A
failing conjunction tells you nothing; a failing conjunct tells you everything.

```go
//@ assert 0 <= i && i <= len(s) && h == RKHashRange(seq(s), 0, i)
```
becomes
```go
//@ assert 0 <= i
//@ assert i <= len(s)
//@ assert h == RKHashRange(seq(s), 0, i)
```

The same applies to contract clauses, and there it is free and always safe:
several `requires`/`ensures`/`invariant` clauses mean exactly their conjunction,
so splitting one clause into several changes nothing except that Gobra now
reports the position of the failing part.

**Splitting one `assert` into several is not always meaning-preserving.**
Between *impure* assertions — anything mentioning `acc`, a predicate instance,
or a quantified permission — Viper's `&&` is a **separating** conjunction: the
permissions add up. So

```go
//@ assert acc(&x.f, 1/2) && acc(&x.f, 1/2)     // needs the whole permission
//@ assert acc(&x.f, 1/2)                       // each passes while holding only 1/2
//@ assert acc(&x.f, 1/2)
```

are different checks, and the split turns a genuine failure into a pair of
spurious passes — the vacuous-pass failure mode of §5, manufactured by the
action meant to diagnose it. Decomposition is safe when the conjuncts are pure,
and when they are impure but mention disjoint resources (`acc(s, p) && acc(sep,
p)` for distinct slices). It is unsafe as soon as one location can be covered
twice, which includes quantified permissions over ranges that may overlap and
two predicate instances over the same object. When in doubt, decompose the pure
conjuncts and leave the resource ones joined.

**Split only at the top level, and only when the top-level operator is `&&`.**
`==>` binds *weaker* than `&&`, so `A ==> B && C` is `A ==> (B && C)` and
splitting its `&&` produces two assertions that are not implied by the original.
Same trap with `||`, with the ternary `? :`, and with a leading quantifier,
whose body extends as far right as possible. Let the script decide:

```bash
python3 .claude/skills/gobra-locate-failure/scripts/split_conjuncts.py \
    "forall i int :: {t(i)} 0 <= i && i < n ==> P(i) && Q(i)"
# -> top-level operator is a quantifier; not splittable. Use action 3.6.
```

**Reading it.** The first conjunct that fails is your real goal; carry it, and
only it, into §3.3. If *no* conjunct fails individually, that is a real result:
the parts are provable and the conjunction is not, which means budget (§2 Q2) or
a state-dependent interaction, not a missing fact.

### 3.2 Materialize the obligation as an assertion

Contract errors are reported at the contract, which is the wrong place to
debug: you cannot decompose or walk something that is not a statement. Turn it
into one.

**Postcondition** (*Insert Failing Postcondition*) — copy the failing clause to
an `assert` at each return, **in the state the postcondition is actually checked
in**. That qualification is the whole difficulty. `return -1` assigns the result
parameter *as part of* the `return`, so an `assert` placed textually above it
runs while `res` still holds whatever it held before the return — its zero
value, unless the body assigned it earlier. The probe then tests a claim nobody
asked about, and for a clause shaped `res == -1 ==> …` it passes *vacuously*
whenever that stale value is not `-1`. A probe that
reports success while testing nothing is the worst outcome available.

Split the return so the assignment happens first:

```go
//@ ensures res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
func IndexRabinKarpBytes(s, sep []byte /*@ , ghost p perm @*/) (res int) {
    ...
    res = -1
    //@ assert res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
    return
}
```

Name the results first if they are unnamed — naming return parameters is one of
the sanctioned code edits in `gobra-specify-verify`, and the `return e` →
`res = e; return` rewrite is a probe like any other, so §6 takes it back out. A
naked `return` needs no rewrite: the results already hold their values.

Two more traps at a return. With several results, assign them all
(`r1, r2 = a, b`) before the assert, since a postcondition normally relates
them. And if the function `defer`s anything that writes a named result, the
postcondition is checked *after* the deferred call runs, so no point in the body
is the right one — work from the deferred function's contract instead.

`old(e)` keeps its meaning inside the body — it is the function's pre-state — so
postconditions containing `old` transfer unchanged.

**Precondition of a call** (*Insert Failing Precondition*) — copy the *callee's*
`requires`, substituting actuals for formals, immediately before the call:

```go
//@ assert 0 <= j && 0 <= k && k <= len(pat) && j+k <= len(q)   // lemma's requires
//@ lemmaMatchesAtRangeFromPointwise(q, pat, j, k)
```

This is the action that converts a useless "precondition of call might not hold"
into a pinpointed conjunct — decompose it (§3.1) and you are done in two runs.

**Loop invariant** — the error tells you which end to probe, but in a 3-clause
`for` the init and post statements sit *between* the body and the invariant
check, so a literal copy of the clause tests the wrong state — the same trap as
at a `return`. The invariant is checked at the loop head, i.e. after the init on
entry and after the post statement on every later iteration. (This repo's own
contracts show it: `for i := 0; i < len(sep); i++` carries
`invariant 0 <= i && i <= len(sep)`, and `i == len(sep)` is only reachable after
the final `i++`.)

- *not established* → assert the clause **before** the loop, substituting the
  init statement's value for the loop variable, which is not in scope yet: for
  `for i := 0; …`, probe the clause with `0` for `i`. That substitution is the
  weakest-precondition step of §3.3.
- *not preserved* → assert the clause at the **end of the body**, substituting
  the post statement's effect: `i+1` for `i` when the post is `i++`. Better,
  move the post statement into the body — `for i := n; i < len(s); {` with `i++`
  inline, exactly as `bytealg.go:181` does — which makes the end of the body and
  the invariant check the same state and removes the substitution entirely.

Asserting the invariant anywhere earlier in the body tests nothing: it is
assumed at the top.

**Pure function** (`The pure function is not well-formed`) — a pure function has
no statements, so the only probe available is the expression-level form:

```go
pure func f(q seq[byte], j int) uint32 {
    return asserting 0 <= j && j < len(q) in
        RKHashRange(q, j, len(q))
}
```

### 3.3 Walk the fact up (weakest-precondition step)

*The core localization action.* You have one failing fact `G`. Find the last
point at which it still holds. That statement — the **flip point** — is the
cause.

Copy `assert G` to a position earlier in the body and re-run. Binary search
rather than stepping: on a 60-line body, midpoint-first finds the flip point in
six runs instead of thirty.

Restate `G` when you move it past a statement that assigns something it mentions
— this is the weakest-precondition part, and it is what makes the answer
meaningful rather than trivially "the assignment":

| Moving up past | Restate `G` as |
|---|---|
| `x := e` with `e` **pure** | `G[e/x]` — substitute the initializer for the variable |
| `x := foo(…)` with `foo` impure | no substitution available: assertions may not contain impure calls. Keep `G` below the call and probe the call's `ensures` instead |
| `x.f = e`, `s[i] = e` | keep `G`; if it mentions the assigned location, snapshot instead (§3.4) |
| `if c { … } else { … }` | copy `G` into **both** branches; a fact can die on one path only |
| a call `foo(a)` | keep `G` before the call. Holding before and failing after has two causes — see below |
| `fold P(x)` | the fields are gone; `G` must be restated as a property of `P(x)` (§3.8) |
| a loop | `G` after the loop must follow from *invariant ∧ ¬guard*; assert it inside the body too, to see whether it ever held |

A call that kills `G` is ambiguous in a way no other statement is, because
Gobra havocs what the callee may have written. Either **the postcondition is too
weak** to re-establish `G`, or **the caller gave away all its permission** to the
locations `G` mentions and so cannot frame their values across the call even
though nothing wrote them. §3.11's wildcard probe separates the two: if
`assert acc(e, _)` fails after the call, it is framing, and the fix is
`preserves acc(e, R)` on the callee rather than a stronger `ensures`.

**Reading the flip point** — this table is the payoff of the whole skill:

| Statement at the flip point | What it means | Where the fix goes |
|---|---|---|
| A call | Postcondition too weak, or the call took permission it did not return | The callee's `ensures` / `preserves` |
| An assignment to a location `G` depends on | `G` was true of the old value | Snapshot it (§3.4), or restate `G` |
| `fold` | The fact is now inside the predicate | Give the predicate a pure-function view, or state the fact over `unfolding` |
| A loop | The invariant does not carry `G` | Add the clause; establishment and preservation are separate obligations |
| A reslice `x[a:b]` | Element correspondence was never established | The bridge assertion (§3.10) |
| `G` holds everywhere individually but not in place | Not a flip point at all | Triggers (§3.7) or budget (§2 Q2) |

### 3.4 Snapshot and compare

For heap-dependent facts — abstraction functions, `seq(s)`, predicate views —
"where did it change?" is more useful than "where did it stop being provable?",
and Gobra will not answer the first question for you. Name the value in ghost
state and compare:

```go
//@ ghost v0 := l.View()
... suspect region ...
//@ assert l.View() == v0
```

The snapshot only freezes anything if `v0` is a **mathematical value** — `seq`,
`set`, `mset`, `dict`, `integer`, an ADT, a `bool`. Those are copied, so `v0`
keeps the old contents whatever happens to the heap afterwards. Snapshotting a
pointer, a slice, or a struct containing one saves a reference, and `v0` then
changes along with the object: the comparison becomes a tautology and passes for
the wrong reason. Snapshot the abstraction, never the thing it abstracts.

Walk the `assert` up as in §3.3. The flip point is the statement that changed
the abstraction — which is a *much* stronger result than a failing assertion,
because it survives into the fix: the same snapshot is usually what the loop
invariant or the `outline` contract needed.

This is also the probe for termination errors: snapshot the measure, then assert
that it decreased.

### 3.5 Introduce the hypothesis

`assert A ==> B` failing is ambiguous — you cannot tell whether `B` is
unprovable, or `A` was never available. Turn the implication into a branch, so
`A` enters the path condition and the error lands on `B`:

```go
//@ ghost if A { assert B }
```

**Reading it.** If `B` now verifies, the original failure was about the
implication's shape, not the goal: something in the surrounding context could
not see `A`. If `B` still fails, you have a strictly smaller goal — carry `B`
into §3.3 with `A` as a known hypothesis.

### 3.6 Introduce the bound variable

Verus offers `assert forall |i| … implies … by { … }`, which puts the bound
variable in scope and assumes the antecedent. Gobra has no statement form of
this. The Gobra spelling is a **ghost lemma whose parameters are the bound
variables and whose `requires` is the antecedent** — which is exactly what this
repo's `lemmas.gobra` is made of:

```go
// goal: forall m int :: {pat[m]} 0 <= m && m < k ==> q[j+m] == pat[m]
ghost
requires  0 <= j && 0 <= k && k <= len(pat) && j+k <= len(q)
requires  /* the antecedent, and whatever else you need */
ensures   forall m int :: {pat[m]} 0 <= m && m < k ==> q[j+m] == pat[m]
decreases k
func lemmaGoal(q, pat seq[byte], j, k int) { … }
```

Inside the lemma the variable is in scope, the antecedent is assumed, and the
proof runs in a *small* context — which alone fixes a surprising share of
failures, because the ambient context was the problem (see `gobra-improve-perf`
§2). Induction over the bound is then available via `decreases` and a recursive
call, which is the only way to prove most quantified facts about recursive spec
functions.

The cheaper, non-inductive variant: a ghost `for` loop whose invariant is the
quantified goal with `k` in place of the bound, building the fact one index at a
time.

### 3.7 Instantiate at a witness

*This action has no ProofPlumber counterpart and is the one you will use most
in Gobra*, because it separates the two failure modes of a quantified goal that
look identical in the output.

```go
//@ ghost k := <a concrete index: 0, i, len(s)-1, whatever is in scope>
//@ assert 0 <= k && k < n        // the antecedent
//@ assert P(k)                   // the body at that index
```

**Reading it:**

| Instance | Quantified goal | Diagnosis |
|---|---|---|
| fails | fails | The property is missing at that index — a real gap. Carry `P(k)` into §3.3 |
| verifies | fails | **Triggering.** The fact is in context and will not instantiate |

A concrete index is weak evidence: it can succeed at `0` and `n-1` while the
property genuinely fails in the middle, so "verifies at the indices I tried"
does not establish the quantified goal. The version that does discriminate uses
an *arbitrary* index — one constrained only by the antecedent — and Gobra has no
statement that introduces one. That is exactly the lemma of §3.6: a ghost
function with `k` as a parameter and the antecedent as its `requires`. If the
body verifies there and the quantified form still fails at the call site, the
gap is triggering or context, not the property. Use the concrete probe to form
the hypothesis cheaply and the lemma to settle it.

A trigger diagnosis sends you to `gobra-debug-perf`'s trigger section: Gobra
does not run Viper's consistency check, so a quantifier can carry a pattern
Silicon rejects with no diagnostic anywhere in the output. Confirm with
`--printVpr` plus a direct Silicon run, and fix with the renaming idiom in
`gobra-improve-perf` §5b. The same probe run *inside* the quantifier's scope
distinguishes "no trigger fires" from "the fact was never established".

### 3.8 Reveal the definition

When the goal mentions an `opaque` pure function or a predicate, the definition
is deliberately not in context. Put it there, once, at the failing point:

```go
//@ assert reveal MatchesAt(q, pat, j)            // opaque pure function
//@ assert unfolding acc(l.Mem(), R) in l.n > 0   // predicate, non-destructively
```

Use the **`unfolding … in` expression form**, not an `unfold` statement, when
you are only probing. `unfold` permanently replaces the predicate instance with
its body: everything after it is a different program, later `fold`s may stop
matching, and you have changed the thing you were trying to measure. `unfolding`
opens the predicate for the evaluation of one expression and leaves the state
alone, which is what a probe should do (§3 preamble).

**Reading it.** If the goal now verifies, the missing fact was the definition —
but `reveal` at that point is usually the *wrong fix*. Revealing inside a hot
region puts the expensive definition back into the context you were protecting;
`gobra-improve-perf` records a case where that was worse than never marking the
function opaque. Introduce a lemma whose `ensures` states the consequence you
need, so the unfolding happens in the lemma's small context and the caller
receives only the conclusion.

When the fix does need a real `unfold`, keep the unfolded region short: an
unfolded predicate costs the same as no predicate (`gobra-improve-perf` §2).

### 3.9 Case-split

Some goals have two proofs and the solver commits to neither. Split explicitly:

```go
//@ assert a <= b                        // failing
//@ assert a < b || a == b               // same goal, two proofs offered
//@ ghost if a != b { assert a < b }     // the case that actually needs work
```

Worth trying for `<=` (the *Split Inequality* action), `!=`, disjunctive goals,
and `nil`/non-`nil` receivers. **Reading it:** the branch that still fails is a
strictly smaller goal with a stronger hypothesis. If both branches verify, the
case analysis itself was the missing step and a `ghost if` is a legitimate
permanent fix.

### 3.10 Bounds and reslicing facts

A goal mentioning `q[i]` carries a *well-definedness* obligation that is
reported separately (`Index ... might exceed sequence length`). Assert the
bounds first; a bounds failure is a different bug from the property failing.

The reslicing case is worth checking by reflex, because it accounts for a large
share of real failures on slice-heavy Go and looks like anything but what it is.
After `x[a:b]`, Gobra cannot relate the new slice's elements to the original
without quantifier reasoning that often does not fire on its own:

```go
//@ assert forall i int :: {&x[a:b][i]} 0 <= i && i < len(x[a:b]) ==> &x[a:b][i] == &x[a+i]
```

If a failure sits at or after a line containing a subslice expression, insert
that assertion before concluding anything else. It is both the probe and the
fix. Keep arithmetic out of the trigger — `{&s[i-n:i][k]}` is rejected by Viper,
`{&s[lo:i][k]}` with `ghost lo := i - n` is not; `bytealg.go:190` does exactly
this.

### 3.11 Localize the permission

`Permission to <e> might not suffice` is a **resource** failure, not a logical
one. Nothing in §3.1–§3.10 applies: no lemma, assert or reveal will produce a
permission you do not hold. Two probes, in order.

**Do you hold any of it?** The wildcard removes the amount from the question:

```go
//@ assert acc(&x.f, _)      // or: assert acc(P(x), _)
```

| `acc(e, _)` | `acc(e, write)` | Diagnosis |
|---|---|---|
| fails | fails | You hold **none**. Find where it went — walk it up |
| verifies | fails | You hold **a fraction**. Someone kept a share, or the contract asked for `R` where the code needs `write` |

**Where did it go?** Walk `assert acc(&x.f, _)` up the body exactly as in §3.3.
The flip point is almost always one of four things:

| Flip point | Cause |
|---|---|
| A call | The callee's contract takes `write` and returns less — see `gobra-review-code` §4.3, and prefer `preserves acc(x, R)` |
| `fold P(x)` | The permission is inside the predicate now; assert `acc(P(x), _)` instead |
| A loop | The invariant does not carry the permission, so it was havocked |
| A call with `acc(e, _)` in its contract | The wildcard hands back *some* positive amount, not the one you gave — a caller can never reassemble `write` |

A `Fold might fail` is the same problem stated at the predicate: decompose the
predicate body (§3.1) into one `assert` per conjunct just before the `fold`, and
the missing chunk names itself.

### 3.12 Scope the region

When the body is long, the context is large, or the member **diverges** and
gives you no error at all to work with, cut it down. Gobra's `outline` verifies
a block against its own contract and hides it from the enclosing member:

```go
//@ requires Bytes(s)
//@ ensures  Bytes(s)
//@ ensures  /* the fact you believe the block establishes */
//@ outline (
        ... suspect region ...
//@ )
```

This is the Gobra stand-in for Verus's *Insert Assert-By Block*, and it does
four things at once: the precondition prunes context, facts established inside
do not leak out, branching inside is hidden, and **errors get localized to the
region instead of the verifier spinning forever**. A member that hangs with no
output often terminates with a precise error once the suspect region is
outlined. Many outlines are worth introducing while debugging and deleting
afterwards.

Restrictions: no `return` inside, no `break`/`continue` targeting an outer loop,
and use `before(x)` rather than `old(x)` for the block's pre-state.

Note that Gobra's grammar admits `assert P by { … }` and `assert P by contra
{ … }`, but the plain proof form is currently rejected by the type checker (see
`gobra-improve-perf` §5). `by contra` works and is the direct spelling of a
proof by contradiction; the idiom this repo uses instead is an explicit
refutation branch:

```go
if reveal MatchesAt(q, pat, j) {
    …
    assert false
}
```

### 3.13 Weaken the contract (diagnostic only)

For a failing `ensures A ==> B`, move `A` into `requires` and leave `ensures B`.
If `B` then verifies, the difficulty is in establishing `A` at the return, not
in `B`. **This is a probe, not a fix** — it moves the obligation onto every
caller. Revert it unless the stronger precondition is genuinely what the API
means, in which case it is a spec change and belongs in the report as one.

The same caution covers every "make it verify by weakening" move: deleting a
postcondition, adding `trusted`, or inserting `assume`. Those are holes in the
proof, not localizations. If you use `assume` as a probe — and it is a good
probe, since `assume G` before the failure tells you whether `G` is the *only*
missing fact — delete it in the same session.

## 4. The loop

Chain the actions; do not shop among them. The procedure terminates.

1. **Triage** (§2). Which path does it fail on? Not a timeout? Property
   actually true?
2. **Materialize** (§3.2) until the failure is on an `assert` statement.
3. **Decompose** (§3.1) until the failing goal is a single conjunct that no
   longer splits.
4. **Introduce** (§3.5–§3.7) until the goal is quantifier- and
   implication-free — a fact about concrete terms.
5. **Walk it up** (§3.3, §3.4) until you have the flip point.
6. **Read the flip point** against the table in §3.3.
7. **Name the missing fact** in one sentence: *"at `file:line`, `<fact>` holds
   before and not after, because `<statement>` `<did what>`."*

If step 5 finds no flip point — the fact fails at every position, including the
first statement of the body — the fact was never true in this context. Go back
to step 4 with the *precondition* as the goal, or to §2 Q3.

## 5. Ways to fool yourself

- **Every probe you insert is a fact the solver can then use.** An `assert` that
  succeeds is added to the context for everything after it, so decomposing an
  assertion can make a *later* obligation pass that used to fail. Nothing is
  established until the member verifies with the probes removed.
- **Put the probe where the state is, not where the statement is.** An `assert`
  reads the state at the point it sits, and that is not always the point the
  obligation is checked: at `return e` the result parameter still holds its
  pre-return value, at the end of a 3-clause `for` body the post statement has not run yet,
  and after a `fold` the fields are inside the predicate. A probe in the wrong
  state usually *passes* — vacuously — and a vacuous pass reads exactly like a
  real one. Before believing a probe that succeeded, check that it could have
  failed: negate it, or place it somewhere you know it must fail.
- **A probe that passed may be sitting in an inconsistent context**, where
  everything is provable. This is the one place the vacuity check fires, since a
  *failing* obligation already proves its own state consistent (§2 Q1). At the
  probe's position:

  ```go
  //@ assert false      // SUCCEEDS (nothing reported) => context is inconsistent
  //@ refute false      // FAILS ("...unreachable or it always holds") => same, normal sign
  ```

  `refute` is the better form in a batch run: it reports an error in the bad
  case instead of asking you to notice a missing one. Usual causes, in the order
  they occur: a `requires false` stub left from `gobra-specify-verify` step 1; an
  `assume` stronger than intended; a contradictory (not merely wrong) loop
  invariant; an unfolded predicate whose body is unsatisfiable. The refutation
  probe of §2 Q3 needs this check for the same reason — in an inconsistent
  context it "finds" a witness for anything.
- **An error that "disappears" may have moved.** Silicon stops a member at its
  first failing obligation, so a probe inserted before the real failure can hide
  it. Check that the member now *verifies*, not merely that the message changed.
- **A passing probe proves derivability at that point, nothing more.** It does
  not prove the fact is what the proof needs, and it does not prove the proof is
  complete.
- **Decomposition changes the budget, not only the logic.** Under
  `assert_timeout`, `assert P; assert Q` is two smaller queries where
  `assert P && Q` was one big one. A decomposition that "fixes" the failure may
  have re-budgeted it (§2 Q2), and adding intermediate assertions to a
  budget-starved member makes it strictly worse.
- **Contract edits are not local.** §3.13 and any `requires` you strengthen move
  work to callers, which may be in other packages.
- **`assume` left behind is a silent unsoundness.** If one has to survive, it
  goes in `assumptions.gobra`, named and justified (`gobra-review-code` §8).
- **A member that verifies is not necessarily proving anything.** A vacuous
  proof is worse than a failing one, because it is silent. Put `refute false` at
  the end of the body — and inside each branch that matters — once the member is
  green, especially if you strengthened a `requires` along the way.

## 6. Clean up before reporting

Probes come out. Concretely, before you call this done:

1. Delete every `assert`, `ghost` variable, `outline`, `assume`, `refute` and
   split-out clause that existed only to localize.
2. Re-verify the member, then the package (`gobra -p ./pkg`). Probes suppress
   later errors; the package run is what tells you the fix is real.
3. **Check the proof is not vacuous.** A member that verifies because its
   context is inconsistent verifies silently. Put `refute false` at the end of
   the body and inside any branch you care about, confirm each one is *not*
   reported, and take them out again. Do this whenever you strengthened a
   `requires`, added an `assume`, or changed an invariant while debugging.
4. Keep only what earns its place: an assertion that is *load-bearing* (removing
   it breaks the proof), a lemma extracted in §3.6, a bridge assertion from
   §3.10, or a snapshot that the invariant now needs. Test each one by deleting
   it and re-running.
5. Run `gofmt -l` over any `.go` file you touched, and put new ghost members in
   the right file — `spec.gobra`, `lemmas.gobra`, `assumptions.gobra`
   (`gobra-review-code` §8).

## 7. Report

- **The failing obligation**: `file:line`, error and reason quoted verbatim.
- **Triage verdict**: proof gap / timeout / vacuous context / bug in the code.
  If it is the last one, that is the headline, not a footnote.
- **The minimal failing goal** after decomposition.
- **The flip point**: `file:line` and the statement, plus the one-sentence
  statement of the missing fact from §4 step 7.
- **The probes you ran**, as a short list of action → outcome. The ones that
  came back negative are as informative as the one that landed, and they stop
  the next person repeating them.
- **The fix**, and whether it is local (an assertion or lemma), a contract
  change (callers affected), or a specification change (hand to
  `gobra-specify-verify`).
- **Confirmation** that the package verifies with the probes removed.

If the diagnosis is a timeout or a trigger blow-up, stop here and hand over to
`gobra-debug-perf` — it starts from exactly this information.
