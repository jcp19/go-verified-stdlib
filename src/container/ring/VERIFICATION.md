# Gobra verification of container/ring

Seven of the nine members of this package are verified with
[Gobra](https://github.com/viperproject/gobra): memory safety, absence of
panics, termination and functional correctness against their doc comments,
with **no assumptions and no trusted members**. The two that are not —
`Link` and `Unlink` — carry `requires false`, so no client can call them and
nothing else in the package rests on an unproved property. `gobra-status.md`
is the per-member inventory and records, with measurements, why those two
were not finished.

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
// @ requires  Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   ret == rs[i > 0 ? i-1 : len(rs)-1]
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
  a parameterized predicate that costs nothing: `Mem(rs, vs)` is one resource
  and the two handles differ only in their ghost index. With ghost fields each
  switch between them is a re-rooting lemma.
- **Repeated queries on one handle are the common case.** `verify` calls
  `r.Move` four times per loop iteration. Each is `preserves Mem(rs, vs)`,
  because `rs` and `vs` are pinned in the predicate's own arguments.

That last point is also why no read-only method here carries a "nothing
changed" postcondition, and why none of them needs a read fraction: the
abstraction cannot drift when it is a parameter.

`Do` is the one member that asks for `rs[0] == r`. It reports the values in
the order it visits them, so the sequence has to start where the walk does.

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

- **Distinctness and linkage share one two-variable quantifier.** Its body
  introduces no new sequence-index term, so Z3 cannot chain instantiations
  around the ring:

  ```gobra
  (forall i, k int :: {rs[i], rs[k]} 0 <= i && i < len(rs) && 0 <= k && k < len(rs) ==>
      (rs[i] == rs[k] ==> i == k) &&
      (k == i+1 ==> rs[i].next == rs[k] && rs[k].prev == rs[i]))
  ```

  Distinctness has to be stated, not just implied by the permissions: `Len` and
  `Do` stop when the walk returns to `r`, and concluding "then I have taken
  exactly `len(rs)` steps" is precisely the step that needs it.
- **`Move` is proved with one description of the walk and specified with
  another.** The loop invariant uses `Step`, which counts single steps exactly
  as the code does; the contract uses `Wrap(i+n, len(rs))`, which is the
  `% r.Len()` of the doc comment. `StepIsWrap` bridges them by induction on
  `n`. Stating the invariant directly in `Wrap` would have put symbolic modular
  arithmetic in every iteration.
- **A neighbour is derived where it is needed, not stored.** `Next`, `Prev` and
  `Move` each name the neighbour they are about to read in an `assert` before
  reading it, which brings the term into scope and lets the two-variable
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
  so there is nothing to fold until then.
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
return (likewise `res := r.next`); ghost parameters and results are added
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

`verify`, `makeN`, `sumN`, `TestNew` and `TestMoveEmptyRing` are reproduced as
verified clients; every `t.Errorf` becomes an `assert` proved unreachable, so
the tests hold for the specifications statically. `verify` is split into three
functions, one per block of the original, and `TestNew`'s two loops are
unrolled into one call per length — both to keep each proof small. Results of
impure calls are stored in locals before being compared, because Gobra does not
allow a call inside an assertion.

The six tests that call `Link` or `Unlink` are not translated: those members
carry `requires false`, so no client can call them.

One test is *added*, `testMoveIsNotDegenerate`. The original checks Move only
by comparing `Move(n)` with `Move(n % Len())`, which a contract saying "Move
returns the receiver" would satisfy just as well; the added test pins the
returned element down on a three-element ring.

Every member of the package and every test function was checked for vacuity by
placing `assert false` in its body and confirming that Gobra reports an error —
7 for the package, 6 for the tests. There is no `assume` anywhere in the
package, and the only `trusted` members are the two stubs.

## Running the verification

```sh
java -jar gobra.jar --config <repo>/src/container/ring
```

(Requires Z3 on `Z3_EXE`.) The package and its tests verify in about one minute
on 4 cores, with `assert_timeout` at 5 s.
