# Gobra verification status of container/ring

This file is the honest inventory of what is actually proven. A member counts
as **verified** only when it carries a real contract, has no `trusted`
annotation, no `requires false`, and no `assume` anywhere on its path.

**Every member of the package is verified**, including all three documented
cases of `Link` and, through it, `Unlink`. There is no `trusted` member and no
`assume` anywhere in the package or its tests.

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
| `(*Ring).Link` | verified | all three cases: `s == nil`, `s` on another ring, `s` on the same ring |
| `(*Ring).Unlink` | verified | the same-ring case of `Link`, with `s` n+1 elements ahead |

## Ghost members

| Member | File | State |
| --- | --- | --- |
| `Mem`, `ElemSet` | spec.gobra | predicate; opaque pure function |
| `IsInit`, `Size`, `Wrap`, `step` | spec.gobra | verified |
| `Visitor`, `VisitSpec` | spec.gobra | verified |
| `wrapShift`, `wrapNeg`, `wrapSucc`, `stepIsWrap` | lemmas.gobra | verified |
| `mulStep`, `mulSucc`, `linContra`, `divUnique`, `divIdentity`, `modUnique`, `modShift`, `modPred`, `modSucc` | lemmas.gobra | verified |
| `LemmaElemSetConcat`, `LemmaElemSetSingle`, `LemmaElemSetCard`, `LemmaDistinct`, `LemmaNotElem`, `LemmaDistinctCard`, `LemmaElemSetOnly`, `idxEq`, `cardSplit`, `cardJoin` | lemmas.gobra | verified |
| `memDisjoint`, `spliceSets`, `spliceRead`, `spliceReadV` | lemmas.gobra | verified |
| `cutRead`, `cutReadV`, `cutSets` | lemmas.gobra | verified |
| `LemmaRotate`, `rotSets`, `rotRead`, `rotReadV` | lemmas.gobra | verified |

`Mem`, `ElemSet`, `IsInit`, `Size`, `Wrap`, `Visitor`, `VisitSpec` and the
`Lemma*` functions are exported because they appear in exported contracts or
are meant for clients (`LemmaRotate` re-roots a ring; `LemmaElemSetSingle` and
`LemmaDistinct` are what a client needs to fold or open `Mem` for itself). The
lower-case lemmas are package-internal scaffolding for `Move`, `Link` and
`Unlink`.

Two of them deserve a word, because an empty body or an unsatisfiable
precondition is exactly what this file exists to flag:

- `VisitSpec` has no body. That is the closure-specification idiom, not an
  assumption: it is never called, it only states the contract that
  `proof cl implements VisitSpec{...}` has to discharge. Gobra's own regression
  suite writes closure specs the same way.
- `linContra`'s precondition is unsatisfiable by design. It closes branches
  that cannot happen (see the periodicity notes below) and is the one member
  the vacuity sweep is expected to pass.

Several lemmas (`mulStep`, `mulSucc`, `divIdentity`, `idxEq`, `rotRead`,
`cutRead`, ...) have an empty body `{}`. That is not an assumption either: an
empty-bodied ghost method is verified like any other, its postcondition proved
from its precondition by the solver alone. They exist to move a fact to the
call site as a postcondition, because Silicon's `assert` checks a fact without
assuming it.

## The encoding: ownership keyed by the element set

`Mem(rs, vs)` owns the elements `rs` of one ring, in forward order, storing the
values `vs`. Ownership is keyed by the *set* of elements, one quantified
permission per field, as `container/list` does:

```gobra
(forall p *Ring :: {p.next}  p elem ElemSet(rs) ==> acc(&p.next)) &&
(forall p *Ring :: {p.prev}  p elem ElemSet(rs) ==> acc(&p.prev)) &&
(forall p *Ring :: {p.Value} p elem ElemSet(rs) ==> acc(&p.Value)) &&
```

Distinctness is the cardinality `len(ElemSet(rs)) == len(rs)`, which has no
quantifier at all; `LemmaDistinct` unpacks it into the pairwise form where a
proof needs it. Linkage is one quantifier per direction, triggered on the field
read (`{rs[i].next}`), so naming a neighbour does not re-trigger the body.

This encoding replaced an index-keyed one, `forall i :: acc(rs[i])`, and is
what made the same-ring case of `Link` provable at all. The measurements that
led to it, from the abandoned attempt on the old encoding:

- **The index-keyed footprint could merge but not split.** The different-ring
  case of `Link` merges two footprints, and verified; the same-ring case splits
  one, and a standalone reproduction of just the split failed after 4 m 54 s.
  Keyed by pointer instead, split, merge and three-way split verified in 17 s.
- **`acc(p)` on a struct with an interface-typed field breaks the cut.** The
  same splitting lemma verified in 24 s with `Value int` and failed after
  5 m 25 s with `Value any` under whole-struct `acc(rs[i])`; one `acc(&p.f)` per
  field with `Value any` verified in 19 s. `Ring.Value` is `any`, hence the
  per-field quantifiers.
- **`old(...)` in a splitting lemma's contract cannot be discharged by the
  caller.** The facts a split hands out are transported as pre- and
  postconditions on the pieces, never framed with `old`.

Keyed by the set, a split or merge of the footprint is set algebra
(`spliceSets`, `cutSets`), proved once in pure lemmas instead of inside every
fold.

## Link and Unlink

`Link` takes, as ghost arguments, the decomposition of `r`'s ring that its
results are phrased in: `rs == {r} ++ ts`. When `s` is on another ring, `ss` is
that ring; when `s` is on `r`'s own ring, `ss` is empty and `ts` splits as
`us ++ ks` — the elements `Link` unlinks, then the ones `r` keeps, which start
at `s` (or `s == r` when `ks` is empty):

```go
// @ ensures   ret == (len(ts) > 0 ? ts[0] : r) && ret != nil
// @ ensures   s == nil ==> Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   s != nil && len(ss) > 0 ==> Mem(seq[*Ring]{r} ++ ss ++ ts, seq[any]{v0} ++ ws ++ tvs)
// @ ensures   s != nil && len(ss) == 0 ==> Mem(seq[*Ring]{r} ++ ks, seq[any]{v0} ++ kvs)
// @ ensures   s != nil && len(ss) == 0 && len(us) > 0 ==> Mem(us, uvs) && IsInit(us, uvs)
```

The four pointer writes run inside an `outline` block. An outline is verified
against its own contract in a clean context, so the surgery does not see the
state `Next` and `Prev` leave behind on the way there. Assembled inline, the
same proof took 1245 s and failed; with the outline it verifies, and the
outline is where the time goes (see Performance). Gobra encodes an outline as a
Viper method of its own, which matters when isolating it: `-i ring.go@<line>`
on `Link`'s signature verifies `Link` *without* its outline, and the outline
has to be targeted by a line inside it.

`Unlink(n)` is `Link` with `s = r.Move(n+1)`. Its contract counts in
`u = Wrap(n, len(rs))`, the `n % r.Len()` of its doc comment: `rs[1:1+u]` is
the removed subring and `r` keeps the rest. `wrapSucc` relates the position
`Move(n+1)` reaches to `u`. The body gains only an intermediate local for
`Move`'s result.

`Unlink` asks for `rs[0] == r` and `Link` for `rs == {r} ++ ts`. A client
holding another element re-roots first with `LemmaRotate`.

## Re-rooting: LemmaRotate

```gobra
requires  0 <= i && i < len(rs)
requires  Mem(rs, vs) && IsInit(rs, vs)
ensures   Mem(rs[i:] ++ rs[:i], vs[i:] ++ vs[:i])
ensures   IsInit(rs[i:] ++ rs[:i], vs[i:] ++ vs[:i])
func LemmaRotate(rs seq[*Ring], vs seq[any], i int)
```

lists the same ring from `rs[i]`. Under the set-keyed encoding a rotation
leaves the element set unchanged (`rotSets`), so the footprint is not split at
all and the lemma is cheap. It closes the gap the previous version of this
file recorded: `Do`, `Link` and `Unlink` still ask for the handle to be first,
but a client can now always make it so. `TestLink1`, `TestUnlink` and
`TestLink3` use it.

## Tests

`ring_test.gobra` reproduces every test of `ring_test.go` — `TestCornerCases`,
`TestNew`, `TestLink1`, `TestLink2`, `TestLink3`, `TestUnlink`,
`TestLinkUnlink`, `TestMoveEmptyRing` — together with the helpers `verify`,
`makeN` and `sumN`, with every `t.Errorf` turned into an `assert` proved
unreachable. Only `dump` is not translated: it is a debugging aid that
exercises `fmt`, not the ring. One test is added, `testMoveIsNotDegenerate`,
which pins down the element `Move` returns.

## Periodicity of `%` on Z3 4.14 and later

`wrapShift` used to have an empty body, its postcondition
`Wrap(k+m, m) == Wrap(k, m)` left to Z3's axioms for `%`. That stopped working
on Z3 4.14 and later — the version the CI image ships, 4.16.0, reports it as
failing — because the solver can no longer relate `(k+m) % m` to `k % m` for a
symbolic `m`. It now has a real proof, via uniqueness of the quotient-remainder
decomposition (`divUnique`), and the arithmetic is shaped by three things
measured on Z3 4.16:

- **Only non-negative dividends.** Z3 still proves the division identity and
  the small-value facts for `%` on non-negative dividends, and proves neither
  on negative ones. `Wrap` is therefore written
  `k >= 0 ? k % m : (m-1) - ((-k-1) % m)`, the same function as the previous
  `((k % m) + m) % m` but with `%` applied only where the solver can follow it.
- **Non-linear steps are lemmas, not asserts.** `mulStep` and `mulSucc` carry
  the two product facts uniqueness needs, and their callers get them as
  postconditions.
- **Products are kept out of the final contradiction.** Even with those facts in
  hand, the contradiction in `divUnique` — linear in the atoms `q1*m` and
  `q2*m` — is not found while those terms are in the query. `linContra` takes
  them as plain parameters, so the solver sees only a linear problem.

`modPred`/`wrapNeg` (for the test's backward moves) and `modSucc`/`wrapSucc`
(for `Unlink`) are built the same way.

## Assumptions

**None.** There is no `assume` and no `trusted` in the package or its tests.
Every member with a body and every test function was rechecked for vacuity by
placing `assert false` first in its body and confirming that Gobra reports an
error; the only expected exception is `linContra`, whose precondition is false
on purpose. The same was done for each of the five branches inside `Link`'s
outline (the different-ring case and the four shapes of the cut), targeting
the outline itself: every branch is reachable.

## Performance

The package and its tests verify in about 6 minutes on 4 local cores with
Z3 4.16.0; the CI runner takes about 2 minutes for the step. `Link` is almost
all of it — 332 s of the 371 s summed over members in the last local run —
and almost all of `Link` is the outline's same-ring branch with both `us` and
`ks` non-empty. Measured with Silicon alone, one verifier, on the whole
package's Viper program:

| What | Time |
| --- | --- |
| `Link` without its outline | 14 s |
| The outline, all cases | 96 s |
| The outline, different-ring case only | 15 s |
| The outline, without the general same-ring case | 23 s |

So the outline's cost is concentrated in one branch, and the time measured
for it moves with its surroundings — the package run's 332 s for `Link`, on 4
cores verifying members in parallel, is three times the 110 s Silicon alone
needs for the same two Viper methods. That is the signature of solver search
order and load rather than of a missing fact, and it means the general cut case runs well
inside the 5 s `assert_timeout` on a quiet machine but nearer it on a loaded
one. It is also not perfectly repeatable: while checking the outline's
branches for reachability, two runs of an unchanged input hung for minutes
where a rerun finished in 27 s. If it ever reports a spurious failure, that branch is where to look
first: its preparation (`cutSets`, `LemmaDistinct` and the five `idxEq`
calls) could move into a lemma with an explicit contract, the way `cutSets`
already took the set algebra out.

## Proof stability in New

A style review reported that `New`'s loop invariant fails intermittently with
"Quantified resource rs[k] might not be injective", 2 runs in 6. That was not
reproducible here, and the most likely explanation is machine load: with
`assert_timeout: 5000`, a query close to the budget is reported as a failure
rather than as a timeout. The invariant was hardened anyway: Silicon consumes
loop-invariant conjuncts left to right, so distinctness — which the injectivity
check needs — is listed before the quantified permission rather than after it.

## Scope

- Termination is in scope: every member and every loop carries a `decreases`.
- Overflow checking is **not** enabled (`--overflow` is not set in
  `src/gobra-mod.json`), so Gobra models Go's `int` as a mathematical integer.
  Nothing here is proved about `int` wraparound — in particular `Unlink`'s
  `n + 1` for `n` the largest `int`.
