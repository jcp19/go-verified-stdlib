# Gobra verification of container/list

This package is fully verified with [Gobra](https://github.com/viperproject/gobra):
memory safety, absence of panics, termination, and functional correctness of
every method, with **no assumptions and no trusted members**. The unit tests of
the package are reproduced as verified clients in `list_test.gobra`.

## Abstraction

A `List` carries its own abstraction in three ghost fields, read through pure
getters defined in `spec.gobra`:

- `Es() seq[*Element]` — the elements of the list, in list order,
- `Vs() seq[any]` — the stored values (`Vs()[i]` is the value of `Es()[i]`),
- `Ini() bool` — whether the sentinel ring has been initialized (`Init`/
  `lazyInit`). The zero `List` value gives empty sequences and `Ini() == false`,
  which is exactly the state `lazyInit` recognizes, so clients may use a zero
  `List` directly.

The predicate `l.Mem()` owns the list header and all elements and pins the
doubly-linked sentinel ring to `Es()`. Because the abstraction lives in the
receiver rather than in predicate parameters, contracts are mostly
`preserves l.Mem()` plus sequence algebra over the getters, and call sites
carry no ghost sequences at all:

```go
// @ preserves l.Mem()
// @ ensures   l.Es() == old(l.Es()) ++ seq[*Element]{ret}
// @ ensures   l.Vs() == old(l.Vs()) ++ seq[any]{v}
func (l *List) PushBack(v any) (ret *Element)
```

so a test reads `l.PushBack(3)` rather than
`l.PushBack(3, seq[*Element]{e1, e2}, seq[any]{1, 2}, true)`.

Because Go's `container/list` is an intrusive structure whose elements are
shared with clients, methods taking an element or mark still take two ghost
parameters: the list that currently owns it and its index there. They support
the three placements a caller can be in — the element belongs to `l`, belongs
to another list (whose `Mem()` is passed along), or is detached and owned by
the caller (`acc(e)`, `e.list == nil`, as after `Remove`). The no-op paths of
the original code ("if e is not an element of l, the list is not modified")
are covered by the latter two modes; `lemmas.gobra` provides `DistinctLists`
for clients that need to tell two lists apart.

## Notable proof engineering

- The linkage of consecutive elements is phrased as a two-variable
  quantifier `forall i, k :: {l.es[i], l.es[k]} k == i+1 ==> ...` whose body
  introduces **no new sequence-index terms**. An earlier formulation
  (`es[i].next == es[i+1]` under trigger `{es[i]}`) let Z3 chain
  instantiations along the sequence and made verification diverge.
- A heap-dependent getter may be mentioned in a loop invariant, but the
  predicate has to be listed **first**: `invariant l.Mem()` before any
  `invariant ... l.Es() ...`. Silicon consumes invariant conjuncts left to
  right, so a getter placed ahead of its own predicate cannot be framed.
- Read-only methods must state `l.Es() == old(l.Es()) && ...` explicitly.
  With predicate parameters this was implicit in `preserves l.Mem(es, vs, ini)`;
  with ghost fields the predicate no longer pins the values, so "nothing
  changed" is now a proof obligation the author writes down. This is the main
  cost of the ghost-field design.
- `Vs()` exports `len(res) == len(l.Es())` as a postcondition. The relation is
  otherwise sealed inside the folded predicate, and without it every contract
  that indexes into `Vs()` fails its well-formedness check.
- Folds after pointer surgery are preceded by "breadcrumb" assertions that
  name the neighbors of the affected elements and give the element-wise
  mapping between old and new sequences.
- `PushFrontList` prepends, so the index of the element being read shifts by
  one during each iteration; the ghost index handed to `Prev` in the loop
  post-statement accounts for that. `PushBackList` appends and needs no shift.

## Changes to the original Go code

The implementation logic is unchanged. The only transformations, all
permitted ones, are: the private field `len` is renamed to `length` (`len`
is a Gobra keyword); three ghost fields are added to `List` inside a
`/*@ … @*/` block, which the Go toolchain does not see; some intermediate
results are stored in fresh local variables (e.g. `res := l.root.next;
return res`) so proof annotations can be placed between the read and the use;
return parameters are named; and `New` introduces a variable for `new(List)`.
`go build`, `go vet` and `go test` still pass on the transformed code.

## Tests (list_test.gobra)

Every function of `list_test.go` is translated; `t.Errorf` calls become
`assert` statements that are proven unreachable, so the tests hold for the
specifications statically. Deviations, all semantics-preserving:

- `TestList`, `TestExtending` and `TestMove` are split into sequential
  continuation functions (`testListMoves`, `testExtendingBack`, …) because a
  single long straight-line member is too expensive for the verifier.
- Values later inspected with type assertions are written `int(1)` /
  `string("banana")`: Gobra does not apply Go's default-type rule when an
  untyped constant is boxed into `any`, so the dynamic type of a bare `1`
  is unknown to the verifier. The Go meaning is identical.
- Parallel swap assignments use explicit temporaries, and `checkList`
  compares values with `===` instead of the `.(int)` type assertion.

`example_test.go` is not translated (it exercises `fmt`, not the list).

## Formatting

`list.go` is `gofmt`-clean: gofmt rewrites `//@` into `// @`, and Gobra
accepts that spelling, so the file passes both tools.

## Running the verification

```sh
java -jar gobra.jar --config <repo>/src/container/list
```

(Requires Z3 on `Z3_EXE`.) The most expensive members are the two
`Push*List` loops and `move`, whose proofs cross-case over element positions.
