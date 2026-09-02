# Gobra verification status of container/ring

This file is the honest inventory of what is actually proven. A member counts
as **verified** only when it carries a real contract, has no `trusted`
annotation, no `requires false`, and no `assume` anywhere on its path.

**The package is not fully verified.** Two of its nine members, `Link` and
`Unlink`, are stubbed out; see "Not verified" below.

## Members of the package

| Member | State | Notes |
| --- | --- | --- |
| `(*Ring).init` | verified | private; lazy initialization of the zero value |
| `(*Ring).Next` | verified | |
| `(*Ring).Prev` | verified | |
| `(*Ring).Move` | verified | doc-faithful `Wrap(i+n, len(rs))`, via `stepIsWrap` |
| `New` | verified | ghost results carry the ring it built |
| `(*Ring).Len` | verified | |
| `(*Ring).Do` | verified | closure specification `VisitSpec` / `Visitor` |
| `(*Ring).Link` | **stub** | `trusted` + `requires false` |
| `(*Ring).Unlink` | **stub** | `trusted` + `requires false` (calls `Link`) |

## Ghost members

| Member | File | State |
| --- | --- | --- |
| `Mem` | spec.gobra | predicate |
| `IsInit`, `Size`, `Wrap`, `step` | spec.gobra | verified |
| `Visitor`, `VisitSpec` | spec.gobra | verified |
| `wrapShift`, `stepIsWrap` | lemmas.gobra | verified |

`Mem`, `IsInit`, `Size`, `Wrap`, `Visitor` and `VisitSpec` are exported because
they appear in exported contracts; `step`, `wrapShift` and `stepIsWrap` are
package-internal scaffolding for `Move`'s proof and are not.

`wrapShift` has an empty body: its postcondition `Wrap(k+m, m) == Wrap(k, m)`
is discharged by Z3's axioms for `%` alone. That is a proof, not an
assumption — the body is empty because nothing further is needed.

`VisitSpec` has no body at all. That is the closure-specification idiom, not an
assumption: it is never called, it only states the contract that
`proof cl implements VisitSpec{...}` has to discharge. Gobra's own regression
suite writes closure specs the same way.

The `trusted` on the two stubs is **not** decoration. It suppresses
type-checking of their bodies, which call `Next`, `Prev` and `Move` without
their ghost arguments; dropping it while keeping `requires false` produces five
Gobra type errors. Anyone reviving `Link` has to thread the ghost arguments
through first.

## Tests

`ring_test.gobra` reproduces `verify`, `makeN`, `sumN`, `TestNew` and
`TestMoveEmptyRing` as verified clients, with every `t.Errorf` turned into an
`assert` proved unreachable. `TestCornerCases`, `TestLink1`, `TestLink2`,
`TestLink3`, `TestLinkUnlink` and `TestUnlink` are **not** translated: all of
them call `Link` or `Unlink`, which no client can call while those two carry
`requires false`.

## Assumptions

**None.** There is no `assume` in the package, and no member other than the two
stubs is `trusted`.

## Not verified: Link and Unlink

`Link` is stubbed with `requires false` rather than left with a `trusted`
contract, so nothing in the package or its tests rests on an unproved
property: a `requires false` member cannot be called at all.

A full contract for `Link` was written and its proof taken a long way before
being abandoned; what stopped it is a property of the encoding, measured rather
than guessed:

- `Mem(rs, vs)` owns the ring's elements with a quantified permission indexed
  by position, `forall i :: acc(rs[i])`.
- The **different-ring** case of `Link` merges two such footprints into one.
  That direction works: a standalone reproduction of exactly that step — two
  full `Mem`-shaped predicates, the four pointer writes, and the fold of the
  merged ring — verifies in **86 s**.
- The **same-ring** case has to do the opposite: split one footprint into the
  ring `r` keeps and the subring that is unlinked. That direction did not
  become tractable. A standalone reproduction of just the split, in a lemma
  whose context holds nothing but `Mem`'s own body, **fails after 4 m 54 s** on
  the quantified permission it is asked to hand out.

So `Link`'s missing proof is not one stubborn assertion; it is that this
encoding of ownership does not support splitting a footprint by index range.

### The pointer-quantified encoding: tried, and how far it got

Quantifying ownership over the *pointer* rather than the position — `forall x
*Ring :: {x elem xs} x elem xs ==> acc(x)`, whose receiver is the bound
variable and so trivially injective — was tried. It **does** remove the
blocker above, and it is cheaper to adopt than expected, but it does not on its
own finish `Link`. Measured, on the same machine as the numbers above:

| Step | Result |
| --- | --- |
| Split, merge, and three-way split of a pointer-quantified footprint | verifies, 17 s (the index-quantified split fails after 4 m 54 s) |
| One, two and four field writes through such a footprint | verifies, 6 s |
| Carve four elements out, write through them, weld back | verifies, 7 s |
| `toSet` / `fromSet`: hand the footprint between `Mem` and the pointer form | verifies, 8 s |
| Sequence distinctness to pointwise set disjointness | verifies, once given the index mapping |
| Two rings held at once are disjoint | verifies, if derived while both are unfolded |

Two things follow. First, the split really is the part the pointer form fixes.
Second — and this was not obvious beforehand — `Mem` would **not** have to
change: `toSet` and `fromSet` convert between the two forms cheaply, so `Link`
can do its surgery in the set world while the other seven members keep the
index form untouched. The earlier estimate in this file, that adopting the
pointer form means re-doing `Mem` and re-verifying seven members, was wrong.

What stops it is a second obstacle that the first one was hiding:

- **A field write splits the chunk of a quantified permission.** A fragmented
  chunk can still be `fold`ed into a predicate — which is why the
  different-ring case, a merge, works — but it can no longer be handed over as
  a bare quantified permission. Converting the footprint after the surgery
  fails with "Permission to rs[i] might not suffice", and so does welding two
  fragments back together.
- **Splitting before the surgery avoids that, but then the split has to frame
  what the elements hold.** Exhaling and re-inhaling a quantified permission
  hands back a fresh snapshot, so the splitting lemma needs `old(...)` clauses
  for `Value`, `next` and `prev`, reachable through the index mapping. That is
  where the attempt stalls: at `assert_timeout` 5000 the call fails on
  "Permission to ars[i].next might not suffice", and at 30000 Silicon throws
  instead of answering.

So the ordering constraint is the live problem: the writes want the footprint
whole, the cut wants it split, and whichever comes second pays. A next attempt
should start there — for instance by carving the four written elements out as
individual `acc`s rather than as a quantified permission, so that no chunk is
ever fragmented — rather than by re-litigating the encoding, which the table
above settles.

Things that were tried and did not help, each measured: raising
`assert_timeout` to 20 s and 60 s (verification stopped terminating rather
than succeeding); splitting the mapping assertions into per-range pieces
(diverged); adding backward-triggered readings of the concatenations (moved
the failure from one obligation to the next, at 2.5x the run time); and
describing the results as slices of `rs` rather than as concatenations of
ghost sequences (diverged outright — `Seq_take`/`Seq_drop` terms, exactly the
hazard `gobra-improve-perf` warns about).

## Proof stability in New

A style review reported that `New`'s loop invariant fails intermittently with
"Quantified resource rs[k] might not be injective", 2 runs in 6. **I could not
reproduce that**: six consecutive runs of the same tree all passed. The most
likely explanation for the difference is machine load — with
`assert_timeout: 5000`, a query close to the budget is reported as a failure
rather than as a timeout, so a loaded machine can turn a slow check into an
error.

The invariant was hardened anyway, because the fragility it points at is real
and the fix is free. Silicon consumes loop-invariant conjuncts left to right,
so the quantified permission was being re-inhaled *before* the distinctness
fact its injectivity check needs. Distinctness is now a separate conjunct
listed first, where it needs no permission of its own; the linkage half stays
after the permission, which it does need. The package verifies about 25%
faster as a result (58 s to 43 s), which is consistent with the check no longer
depending on the solver rediscovering the fact.

## Known limitation: Do is callable only from rs[0]

`Next`, `Prev`, `Move` and `Len` take a free ghost index `i` with `rs[i] == r`,
so any handle on the ring can call them. `Do` alone requires `rs[0] == r`,
because it reports the values in the order it visits them — and the package
ships no lemma to re-root `Mem(rs, vs)` at another element. A client that
walked away from `rs[0]` therefore cannot call `Do` at all.

That is a real gap in the design's own claim that "every element is an equal
handle", and it is the same wall `Link` hit: a re-rooting lemma has to rotate
the sequence, which is a split followed by a merge of the quantified-permission
footprint, and the split is what this encoding does not support. Generalizing
`Do` to `rs[i] == r` with `ensures vis.Seen(vs[i:] ++ vs[:i])` is the other
option; it was not attempted, and the slicing in that postcondition is itself a
known performance hazard.

## Scope

- Termination is in scope: every member and every loop carries a `decreases`.
- Overflow checking is **not** enabled (`--overflow` is not set in
  `src/gobra-mod.json`), so Gobra models Go's `int` as a mathematical integer.
  Nothing here is proved about `int` wraparound.
