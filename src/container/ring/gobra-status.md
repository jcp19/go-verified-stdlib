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
| `(*Ring).Move` | verified | doc-faithful `Wrap(i+n, len(rs))`, via `StepIsWrap` |
| `New` | verified | ghost results carry the ring it built |
| `(*Ring).Len` | verified | |
| `(*Ring).Do` | verified | closure specification `VisitSpec` / `Visitor` |
| `(*Ring).Link` | **stub** | `trusted` + `requires false` |
| `(*Ring).Unlink` | **stub** | `trusted` + `requires false` (calls `Link`) |

## Ghost members

| Member | File | State |
| --- | --- | --- |
| `Mem` | spec.gobra | predicate |
| `IsInit`, `Wrap`, `Step` | spec.gobra | verified |
| `Visitor`, `VisitSpec` | spec.gobra | verified |
| `WrapShift`, `StepIsWrap` | lemmas.gobra | verified |

`WrapShift` has an empty body: its postcondition `Wrap(k+m, m) == Wrap(k, m)`
is discharged by Z3's axioms for `%` alone. That is a proof, not an
assumption — the body is empty because nothing further is needed.

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
The likely fix is to quantify ownership over the *pointer* (`forall x *Ring ::
x in xs ==> acc(x)`, whose receiver is trivially injective) instead of over the
position, which would make the split set reasoning rather than index
re-mapping — at the cost of re-doing `Mem` and re-verifying the seven members
that currently depend on it.

Things that were tried and did not help, each measured: raising
`assert_timeout` to 20 s and 60 s (verification stopped terminating rather
than succeeding); splitting the mapping assertions into per-range pieces
(diverged); adding backward-triggered readings of the concatenations (moved
the failure from one obligation to the next, at 2.5x the run time); and
describing the results as slices of `rs` rather than as concatenations of
ghost sequences (diverged outright — `Seq_take`/`Seq_drop` terms, exactly the
hazard `gobra-improve-perf` warns about).

## Scope

- Termination is in scope: every member and every loop carries a `decreases`.
- Overflow checking is **not** enabled (`--overflow` is not set in
  `src/gobra-mod.json`), so Gobra models Go's `int` as a mathematical integer.
  Nothing here is proved about `int` wraparound.
