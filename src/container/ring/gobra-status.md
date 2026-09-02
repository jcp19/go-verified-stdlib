# Gobra verification status of container/ring

This file is the honest inventory of what is actually proven. A member counts
as **verified** only when it carries a real contract, has no `trusted`
annotation, no `requires false`, and no `assume` anywhere on its path.

**The package is not fully verified.** `Unlink` is stubbed out, and `Link`
carries a contract that covers two of its three documented cases and excludes
the third by precondition; see "Link: what is and is not covered" and "Not
verified: the same-ring cut" below.

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
| `(*Ring).Link` | verified, **restricted** | full contract for `s == nil` and for `s` on a different ring; the same-ring case is excluded by the precondition |
| `(*Ring).Unlink` | **stub** | `trusted` + `requires false`; it is the same-ring case of `Link` |

## Ghost members

| Member | File | State |
| --- | --- | --- |
| `Mem` | spec.gobra | predicate |
| `IsInit`, `Size`, `Wrap`, `step` | spec.gobra | verified |
| `Visitor`, `VisitSpec` | spec.gobra | verified |
| `wrapShift`, `stepIsWrap` | lemmas.gobra | verified |
| `memDisjoint`, `spliceRead`, `spliceReadV` | lemmas.gobra | verified |

`Mem`, `IsInit`, `Size`, `Wrap`, `Visitor` and `VisitSpec` are exported because
they appear in exported contracts; `step`, `wrapShift` and `stepIsWrap` are
package-internal scaffolding for `Move`'s proof, and `memDisjoint`,
`spliceRead` and `spliceReadV` for `Link`'s, and are not.

`wrapShift` has an empty body: its postcondition `Wrap(k+m, m) == Wrap(k, m)`
is discharged by Z3's axioms for `%` alone. That is a proof, not an
assumption — the body is empty because nothing further is needed.

`VisitSpec` has no body at all. That is the closure-specification idiom, not an
assumption: it is never called, it only states the contract that
`proof cl implements VisitSpec{...}` has to discharge. Gobra's own regression
suite writes closure specs the same way.

The `trusted` on `Unlink` is **not** decoration. It suppresses type-checking of
its body, which calls `Move` and `Link` without their ghost arguments; dropping
it while keeping `requires false` produces Gobra type errors. Anyone reviving
`Unlink` has to thread the ghost arguments through first -- and to prove the
same-ring cut, which is what `Unlink` is.

## Tests

`ring_test.gobra` reproduces `verify`, `makeN`, `sumN`, `TestNew`,
`TestMoveEmptyRing` and `TestLink2` as verified clients, with every `t.Errorf`
turned into an `assert` proved unreachable. `TestLink2` is the original's
different-ring test in full -- two one-element rings, a ring of ten, and the
twelve-element ring the last splice produces -- and it is what shows `Link`'s
contract is usable rather than vacuously true.

Four tests are **not** translated:

- `TestCornerCases`, `TestUnlink` and `TestLinkUnlink` call `Unlink`.
- `TestLink1` links a ring to itself, which `Link`'s contract does not cover.
- `TestLink3` calls `verify` on the *result* of `Link`, which is the element
  after the splice and not the one `Mem` is rooted at. Translating it needs the
  re-rooting lemma the package does not ship; see "Known limitation" below.

## Assumptions

**None.** There is no `assume` in the package, and `Unlink` is the only
`trusted` member. `Link` is neither `trusted` nor `requires false`: its
restriction is a precondition a client has to meet, not an unproved claim.
Every member and every test function was rechecked for vacuity by placing
`assert false` in its body and confirming that Gobra reports an error.

## Link: what is and is not covered

`Link`'s doc comment describes three cases: `s == nil`, `s` on a different ring,
and `s` on the same ring as `r`. The contract covers the first two:

```go
// @ requires  Mem(rs, vs) && 0 < len(rs) && rs[0] == r
// @ requires  rs == seq[*Ring]{r} ++ ts && vs == seq[any]{v0} ++ tvs
// @ requires  s != nil ==> Mem(ss, ws) && 0 < len(ss) && ss[0] == s
// @ ensures   ret == (len(ts) > 0 ? ts[0] : r) && ret != nil
// @ ensures   s == nil ==> Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   s != nil ==> Mem(seq[*Ring]{r} ++ ss ++ ts, seq[any]{v0} ++ ws ++ tvs)
```

The third case is excluded by `requires s != nil ==> Mem(ss, ws)`: no client
can produce a second `Mem` for elements it already owns through `Mem(rs, vs)`,
so the precondition is exactly "s is on a ring of its own". That is a
restriction on what may be called, not a claim taken on trust -- `Link` has no
`trusted`, no `requires false` and no `assume`, and `TestLink2` calls it four
times. What it costs is `Unlink`, which is nothing but the same-ring case, and
the three tests that use it.

## Not verified: the same-ring cut

`Unlink` is stubbed with `requires false` rather than left with a `trusted`
contract, so nothing in the package or its tests rests on an unproved
property: a `requires false` member cannot be called at all.

A contract for the same-ring case was written and its proof taken a long way
before being abandoned; what stopped it is a property of the encoding, measured
rather than guessed:

- `Mem(rs, vs)` owns the ring's elements with a quantified permission indexed
  by position, `forall i :: acc(rs[i])`.
- The **different-ring** case of `Link` merges two such footprints into one.
  That direction works, and is what the shipped contract proves.
- The **same-ring** case has to do the opposite: split one footprint into the
  ring `r` keeps and the subring that is unlinked. That direction did not
  become tractable. A standalone reproduction of just the split, in a lemma
  whose context holds nothing but `Mem`'s own body, **fails after 4 m 54 s** on
  the quantified permission it is asked to hand out.

So the missing proof is not one stubborn assertion. The two sections
below take that split apart far enough to say what actually costs what; the
conclusion above — that the encoding cannot split a footprint by index range —
turns out to be two separable problems and one capacity limit, and only the
last of them is still open.

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

### Two more walls, and where the third one actually is

Pushing further took the cut apart into pieces small enough to measure one at
a time. Each piece below **verifies**, standalone, in the time given; the
reproductions are minimal files with nothing in them but a `Ring`-shaped
struct and the lemma under test.

**1. `old(...)` in a splitting lemma's contract cannot be discharged by the
caller.** A lemma that hands out half a footprint has to say what the elements
still hold, because exhaling and re-inhaling a quantified permission returns a
fresh snapshot. Writing that as `us[i].Value === old(us[i].Value)` makes the
*caller* resolve a pre-state heap read of `us[i]` through an index mapping into
`rs`, and it fails there ("Permission to `us[i].Value` might not suffice") even
though every fact it needs is provable at the call site — each of the five
assertions preceding the call passes. The fix is to transport the facts rather
than frame them: state them as preconditions on `rs` and as postconditions on
the two pieces, re-indexed, and keep `old` inside the body where the pre-state
permission is genuinely held. With that change the same lemma gets past this
point.

**2. `acc(p)` on a struct with an interface-typed field is what breaks the
cut.** This is the sharpest finding, and it is a one-line change:

| Same lemma, same contract, same body | Result |
| --- | --- |
| footprint as `forall i :: acc(rs[i])`, `Value int` | verifies, 24 s |
| footprint as `forall i :: acc(rs[i])`, `Value any` | **fails, 5 m 25 s** — "Permission to `ars[a].next` might not suffice" |
| footprint as `acc(&rs[i].next)`, `acc(&rs[i].prev)`, `acc(&rs[i].Value)`, `Value any` | verifies, 19 s |

Only the field's type and the shape of the permission differ. `Ring.Value` is
`any`, so the package is in the failing row, and whole-struct quantified
ownership over it defeats Silicon's handling of the footprint. Removing the
value clauses from the contract entirely does **not** help (still fails, 3 m
0 s), so it is the field's presence in `acc(p)` and not the `===` transport
that costs. Every `acc(p)` in a quantifier in this package's proof should be
one `acc(&p.f)` per field.

**3. What is left is a solver-capacity limit, not a missing lemma.** With
those two fixed, every ingredient of `Link`'s same-ring case verifies on its
own:

| Ingredient | Result |
| --- | --- |
| Cut before the surgery, field-wise, transporting values and linkage | verifies, 19 s |
| The same lemma called from a whole-struct *and* a field-wise caller | verifies, 17 s |
| Cut *after* the surgery, handing both halves back as `Mem` predicates | verifies, 63 s |
| `Link`'s four writes, in its own order and aliasing pattern | verifies, 9 s |
| Closing a half with two writes and folding `Mem` | verifies, 10 s |

Assembled into `Link`, none of it holds. The failure does not stay in one
place: it moves to whichever obligation is touched last, it moves when
assertions that are themselves provable are added, and adding an unrelated
file to the same verification run turned two green lemmas red. In the last
configuration tried — everything inline, field-wise, no boundary crossed after
the surgery — the failing obligation was `r.next = s`, the first of the four
writes, which verifies in 9 s by itself.

That is the signature of quantifier-instantiation blowup rather than a gap in
the proof. At the point of the surgery `Link` has about fifteen live
quantifiers over the same four or five sequences — its own eleven ghost
parameters, `Mem`'s unfolded body, and the index mappings — and Silicon has to
compute residual permission for a footprint that four field writes have
fragmented. A next attempt should therefore go at the *context*, not the
encoding: fewer ghost parameters, a `Mem` that is not indexed by a sequence of
pointers, or a formulation of `Link` that never needs the whole ring's
footprint at once. Permuting the cut further is not it — the tables above
settle the encoding question.

Things that were tried and did not help, each measured: raising
`assert_timeout` to 20 s, 30 s and 60 s (verification stopped terminating
rather than succeeding); splitting the mapping assertions into per-range
pieces (diverged); adding backward-triggered readings of the concatenations
(moved the failure from one obligation to the next, at 2.5x the run time);
naming each written element's index before the writes (fixed the writes, moved
the failure into the reads that follow); asserting the pointer disequalities
Silicon needs for residual permission (moved the failure back onto a write
that had been passing); and describing the results as slices of `rs` rather
than as concatenations of ghost sequences (diverged outright —
`Seq_take`/`Seq_drop` terms, exactly the hazard `gobra-improve-perf` warns
about).

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
footprint. It should now be cheaper than it was — a rotation crosses no
post-surgery heap read, so obstacles 1 and 3 above do not apply, and obstacle 2
says to write the permission one field at a time. It was not attempted.
Generalizing `Do` to `rs[i] == r` with `ensures vis.Seen(vs[i:] ++ vs[:i])` is
the other option; it was not attempted either, and the slicing in that
postcondition is itself a known performance hazard.

This limitation is also what keeps `TestLink3` out of `ring_test.gobra`: that
test calls `verify` on the element `Link` returns, which is not the one `Mem`
is rooted at.

## Scope

- Termination is in scope: every member and every loop carries a `decreases`.
- Overflow checking is **not** enabled (`--overflow` is not set in
  `src/gobra-mod.json`), so Gobra models Go's `int` as a mathematical integer.
  Nothing here is proved about `int` wraparound.
