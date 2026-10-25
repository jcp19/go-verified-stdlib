# Gobra verification of container/ring

All nine members of this package are verified with
[Gobra](https://github.com/viperproject/gobra): memory safety, absence of
panics, termination and functional correctness against their doc comments,
with **no assumptions** and no `trusted` member. That includes all three
documented cases of `Link` — `s == nil`, `s` on a different ring, and `s` on
the same ring, which cuts the ring in two — and `Unlink`, which is that last
case. Every test of the package's `ring_test.go` has a verified counterpart.
`gobra-status.md` is the per-member inventory, with the measurements behind
the design choices below.

## Abstraction

A ring is a circular doubly-linked list *without a header*: the package's own
doc comment says that "a pointer to any ring element serves as reference to
the entire ring". There is no distinguished node to hang ghost fields on, so
unlike `container/list` this package does not carry its abstraction in the
receiver. It passes it explicitly:

```gobra
pred Mem(rs seq[*Ring], vs seq[any])
```

owns the elements `rs` of one ring, in forward order, and states that `vs` are
the values they store. A method says which element it was called on with a
ghost index `i` satisfying `rs[i] == r`:

```go
// @ preserves Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   IsInit(rs, vs)
// @ ensures   ret == rs[i > 0 ? i-1 : len(rs)-1] && ret != nil
func (r *Ring) Prev( /*@ ghost rs seq[*Ring], ghost vs seq[any], ghost i int @*/ ) (ret *Ring)
```

### Why not ghost fields

`gobra-specify-verify` recommends ghost fields plus pure getters, and
`container/list` in this repository follows that advice. Deviating here is
deliberate, and it is the shape of `ring`'s API that forces it:

- **Every element is an equal handle.** With the abstraction in a ghost field
  of one node, handing a caller `r.Next()` would leave them holding a pointer
  they have no predicate for, and re-rooting the predicate at another element
  would need a lemma call at every step.
- **Aliases into one ring are normal.** `TestUnlink` keeps `r10` and
  `s10 := r10.Move(6)` alive at the same time and calls `verify` on both. With
  a parameterized predicate, `Mem(rs, vs)` is one resource and the two handles
  differ only in their ghost index for `Next`, `Prev`, `Move` and `Len`; only
  the members that need the handle first (`Do`, `Link`, `Unlink`) need a
  rotation. With ghost fields every switch between handles is a re-rooting
  lemma.
- **Repeated queries on one handle are the common case.** `verify` calls
  `r.Move` four times per loop iteration. Each is `preserves Mem(rs, vs)`,
  because `rs` and `vs` are pinned in the predicate's own arguments.

That last point is also why no read-only method here carries a "nothing
changed" postcondition, and why none of them needs a read fraction: the
abstraction cannot drift when it is a parameter.

`Do`, `Link` and `Unlink` ask for the handle to be the first element,
`rs[0] == r`: `Do` reports the values in the order it visits them, and the
results of `Link` and `Unlink` are phrased as cuts of the sequence starting at
`r`. A client holding another element re-roots first with

```gobra
requires  0 <= i && i < len(rs)
requires  Mem(rs, vs) && IsInit(rs, vs)
ensures   Mem(rs[i:] ++ rs[:i], vs[i:] ++ vs[:i])
ensures   IsInit(rs[i:] ++ rs[:i], vs[i:] ++ vs[:i])
func LemmaRotate(rs seq[*Ring], vs seq[any], i int)
```

which is cheap because ownership is keyed by the element set (below), and a
rotation leaves the set unchanged. The translated `TestUnlink` does exactly
this to call `verify` on `s10`.

### The zero value

`Ring`'s doc comment declares the zero value to be "a one-element ring with a
nil Value", and every exported method lazily initializes such an element on
first use (the `r.next == nil` branches). `Mem` therefore admits two shapes for
a one-element ring — linked to itself, or still holding the zero value's nil
`next` and `prev`:

```gobra
(rs[0].next == nil ==> len(rs) == 1 && rs[0].prev == nil) &&
(rs[0].next != nil ==> rs[len(rs)-1].next == rs[0] && rs[0].prev == rs[len(rs)-1])
```

Demanding an initialized ring instead would have been a stronger precondition
than the documentation supports, and `TestMoveEmptyRing` — which is translated
here — would not have verified. `IsInit` makes the distinction observable,
which the tests need because they read `r.next` and `r.prev` directly; no
client-visible behaviour depends on it.

## Notable proof engineering

- **Ownership is keyed by the element set, one quantifier per field.**

  ```gobra
  (forall p *Ring :: {p.next}  p elem ElemSet(rs) ==> acc(&p.next)) &&
  (forall p *Ring :: {p.prev}  p elem ElemSet(rs) ==> acc(&p.prev)) &&
  (forall p *Ring :: {p.Value} p elem ElemSet(rs) ==> acc(&p.Value))
  ```

  rather than by position (`forall i :: acc(rs[i])`). A position-keyed
  footprint can be merged, which is all the different-ring case of `Link`
  needs, but splitting one — the same-ring case — did not terminate; keyed by
  the set, the split is set algebra proved once in pure lemmas (`cutSets`,
  `spliceSets`). Per field rather than `acc(p)`, because `Ring.Value` is `any`,
  and whole-struct quantified ownership over a struct with an interface-typed
  field is what defeated the cut in measurements (`gobra-status.md`).
  `ElemSet` is opaque, so `Mem`'s body does not unroll it at every unfold.
- **Distinctness is a cardinality**, `len(ElemSet(rs)) == len(rs)`, with no
  quantifier at all; `LemmaDistinct` unpacks it into the pairwise form where a
  proof needs it. It has to be stated, not just implied by the permissions:
  `Len` and `Do` stop when the walk returns to `r`, and concluding "then I have
  taken exactly `len(rs)` steps" is precisely the step that needs it.
- **Linkage is one quantifier per direction, triggered on the field read**,
  `{rs[i].next}` and `{rs[i].prev}`: naming the neighbour `rs[i+1]` in the body
  does not create the term `rs[i+1].next`, so the quantifier cannot chain
  instantiations around the ring.
- **`Move` is proved with one description of the walk and specified with
  another.** The loop invariant uses `step`, which counts single steps exactly
  as the code does; the contract uses `Wrap(i+n, len(rs))`, which is the
  `% r.Len()` of the doc comment. `stepIsWrap` bridges them by induction on
  `n`. Stating the invariant directly in `Wrap` would have put symbolic modular
  arithmetic in every iteration.
- **`%` is only applied to non-negative dividends, and its periodicity is
  proved rather than left to the solver.** Z3 4.14 and later cannot relate
  `(k+m) % m` to `k % m` for a symbolic `m` on its own, so `wrapShift` goes
  through uniqueness of the quotient-remainder decomposition, with each
  non-linear step in a lemma of its own and the final contradiction stated
  over the product terms as plain values (`linContra`). `gobra-status.md`
  has the measurements.
- **A neighbour is derived where it is needed, not stored.** `Next`, `Prev` and
  `Move` each name the neighbour they are about to read in an `assert` before
  reading it, which brings the term into scope and lets the linkage
  quantifier fire. Adding the neighbour relation to `Mem` instead would have
  made every fold in the package pay for it.
- **`Len` and `Do` keep `Mem` folded across their loops** and read `p.next`
  through `unfolding Mem(rs, vs) in p.next` in the loop's post statement. The
  fact about what that expression *is* is established at the end of the body,
  where an `unfold`/`fold` pair can bracket an assertion.
- **The position in `Len` and `Do` is a function of the counter, not a second
  ghost variable.** `p == rs[i+n < m ? i+n : i+n-m]` holds at the loop head
  with the counter the body already maintains, which sidesteps the awkwardness
  of updating a ghost index from a `for` post statement.
- **`New` builds its ring under raw quantified permissions** rather than an
  auxiliary predicate: the ring is not closed until the last two assignments,
  so there is nothing to fold until then. Its invariants list **distinctness
  first, before the quantified permission**: Silicon consumes invariant
  conjuncts left to right, and re-inhaling that permission for the extended
  sequence is what needs the injectivity of `k |-> rs[k]`. Leaving the fact to
  be rediscovered from the combined quantifier that used to follow made the
  check depend on the solver's search order, and cost about 25% of the
  package's runtime.
- **`Link` takes the decomposition of the ring as ghost arguments** and tells
  its three cases apart by them: `rs == {r} ++ ts`; when `s` is on another
  ring `ss` is that ring, and when `s` is on `r`'s own ring `ss` is empty and
  `ts == us ++ ks` — the elements `Link` unlinks, then the ones `r` keeps. The
  different-ring case is a merge, the same-ring case a cut, and each folds its
  result straight back as `Mem`. Small lemmas carry the bookkeeping:
  `memDisjoint` reads two rings' disjointness off the fact that both are held
  at once (an element of both would carry `acc` twice); `spliceRead` and
  `cutRead` say what the merged or cut sequences are, by position;
  `spliceSets` and `cutSets` do the set algebra.
- **`Link`'s four pointer writes run inside an `outline` block.** An outline
  is verified against its own contract in a clean context, so the surgery does
  not see what `Next` and `Prev` left behind on the way there. Assembled
  inline, the same proof took 1245 s and failed; with the outline it verifies,
  in about 110 s of solver time, nearly all of it the same-ring case. Inside it, the same-ring branch is split
  by the shape of the cut (`us` or `ks` empty or not), and each branch does its
  own `unfold`: Silicon rejoins branches that only call pure lemmas, and a
  rejoined branch loses the shape it was split on.
- **`Unlink` is `Link` with `s` n+1 elements ahead.** Its contract counts in
  `u = Wrap(n, len(rs))`, the `n % r.Len()` of its doc comment: `rs[1:1+u]` is
  the removed subring and `r` keeps the rest. `wrapSucc` relates the position
  `Move(n+1)` reaches to `u`.
- **`Size` exports what `Mem` seals.** `0 < len(rs)` and `len(rs) == len(vs)`
  are invisible outside the predicate, which makes *any* contract mentioning
  `rs` and `vs` together ill-formed for a client. The getter is what keeps the
  abstraction usable from another package.
- **`Do` uses a closure specification.** `Visitor` is a ghost interface with a
  predicate `Seen(calls)` — the client's invariant after `f` has been applied
  to exactly `calls` — and a pure `Accepts(v)`. `Accepts` is what lets a
  *partial* closure be passed: the summing closure in `ring_test.go` asserts
  `p.(int)`, so it cannot run on arbitrary values, and `Do` requires
  `vis.Accepts(vs[t])` for every value in the ring. Without it only total
  closures would qualify, which is a stronger demand on clients than `Do`
  actually makes.

## Changes to the original Go code

The implementation logic is unchanged. Stripping every annotation from
`ring.go` and diffing against the upstream file leaves only permitted
transformations: return parameters are named; three `return r.init()` become
`res := r.init(); return res` so a `fold` can sit between the call and the
return (likewise `res := r.next`); `Unlink`'s `return r.Link(r.Move(n + 1))`
stores `Move`'s result in a local `s` first; ghost parameters and results are added
inside `/*@ … @*/`; and doc comments are extended. `f func(any)` becomes
`f func( /*@ ghost seq[any], @*/ any)`, which Go still reads as `func(any)`.
`go build`, `go vet` and `go test` pass on the transformed package, and
`gofmt` reports the same single deviation it reports for the upstream file
(a trailing `//` line that predates this work).

Two Gobra limitations forced a workaround rather than a code change:

- A bare `nil` inside a `seq[any]` literal cannot be typed, so `New` reads the
  nil value out of the freshly allocated element (`seq[any]{r.Value}`).
- Updating a `seq[any]` with an untyped `int` crashes Silicon with an internal
  `AssertionError`; `makeN` in the test file boxes the value into an `any`
  local first.

## Tests (ring_test.gobra)

Every test of `ring_test.go` — `TestCornerCases`, `TestNew`, `TestLink1`,
`TestLink2`, `TestLink3`, `TestUnlink`, `TestLinkUnlink` and
`TestMoveEmptyRing` — is reproduced as a verified client, together with the
helpers `verify`, `makeN` and `sumN`; every `t.Errorf` becomes an `assert` proved
unreachable, so the tests hold for the specifications statically. `verify` is split into three
functions, one per block of the original, and `TestNew`'s two loops are
unrolled into one call per length — both to keep each proof small. Results of
impure calls are stored in locals before being compared, because Gobra does not
allow a call inside an assertion.

The tests are also what show the contracts are usable rather than vacuously
true: `TestLink2` exercises the different-ring case of `Link` up to the
twelve-element ring its last splice produces, `TestLink1` the same-ring case
in both of its shapes, and `TestUnlink` and `TestLinkUnlink` `Unlink`, the
latter linking every removed subring back and checking that the ring is
restored element for element. Where the original calls `verify` on a handle
that is not the first element of its ring (`s10` in `TestUnlink`, `Link`'s
result in `TestLink1` and `TestLink3`), the ring is re-rooted with
`LemmaRotate` first. Only `dump` is not translated: it is a debugging aid that
exercises `fmt`, not the ring.

One test is *added*, `testMoveIsNotDegenerate`. The original checks Move only
by comparing `Move(n)` with `Move(n % Len())`, which a contract saying "Move
returns the receiver" would satisfy just as well; the added test pins the
returned element down on a three-element ring.

Every member with a body and every test function was checked for vacuity by
placing `assert false` first in its body and confirming that Gobra reports an
error; the one expected exception is `linContra`, whose precondition is false
on purpose (it closes impossible branches of the `%` proofs). There is no
`assume` and no `trusted` anywhere in the package.

## Running the verification

```sh
java -jar gobra.jar --config <repo>/src/container/ring
```

(Requires Z3 on `Z3_EXE`.) The package and its tests verify in about 6 minutes
on 4 local cores with Z3 4.16.0, the version the CI image ships, with
`assert_timeout` at 5 s; the CI runner takes about 2 minutes. Nearly all of it
is `Link`'s same-ring case, and `gobra-status.md` records where in it the time
goes. See `../../gobra/TOOLCHAIN.md` for why the Z3 version matters here.
