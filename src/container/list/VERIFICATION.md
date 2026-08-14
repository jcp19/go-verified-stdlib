# Gobra verification of container/list

This package is fully verified with [Gobra](https://github.com/viperproject/gobra):
memory safety, absence of panics, termination, and functional correctness of
every method, with **no assumptions and no trusted members**. The unit tests of
the package are reproduced as verified clients in `list_test.gobra`.

## Abstraction

A list `l` is abstracted by two mathematical sequences and a flag:

- `es seq[*Element]` — the elements of the list, in list order,
- `vs seq[any]` — the stored values (`vs[i]` is the value of `es[i]`),
- `ini bool` — whether the sentinel ring has been initialized (`Init`/
  `lazyInit`); the zero `List` value is covered by `ini == false` with empty
  sequences, so clients may use a zero `List` directly.

The predicate `l.Mem(es, vs, ini)` (in `spec.gobra`) owns the list header and
all elements and pins the doubly-linked sentinel ring to `es`. Method
contracts are then plain sequence algebra, e.g. `PushBack` appends
`(ret, v)`, `Remove` deletes index `i`, `move` is described by the pure
functions `moveSeq`/`moveSeqV`, and `PushBackList`/`PushFrontList` return the
freshly allocated copies as a ghost sequence `nes` so their postconditions
can name them (`l` becomes `es ++ nes` resp. `nes ++ es`).

Because Go's `container/list` is an intrusive structure whose elements are
shared with clients, methods taking an element/mark argument support the
three placements a caller can be in, selected by ghost arguments: the
element belongs to `l`, belongs to another list (whose `Mem` is passed
along), or is detached and owned directly by the caller (`acc(e)`,
`e.list == nil`, as after `Remove`). The no-op paths of the original code
("if e is not an element of l, the list is not modified") are covered by the
latter two modes; `lemmas.gobra` provides `DistinctLists` for clients that
need to tell two lists apart.

## Notable proof engineering

- The linkage of consecutive elements is phrased as a two-variable
  quantifier `forall i, k :: {es[i], es[k]} k == i+1 ==> ...` whose body
  introduces **no new sequence-index terms**. An earlier formulation
  (`es[i].next == es[i+1]` under trigger `{es[i]}`) let Z3 chain
  instantiations along the sequence and made verification diverge.
- `ini` is a predicate parameter rather than a heap-dependent pure function:
  a pure function reading the predicate cannot be used in loop invariants
  (its `Mem` argument is consumed earlier in the same exhale).
- Folds after pointer surgery are preceded by "breadcrumb" assertions that
  name the neighbors of the affected elements and give the element-wise
  mapping between old and new sequences.

## Changes to the original Go code

The implementation logic is unchanged. The only transformations, all
permitted ones, are: the private field `len` is renamed to `length` (`len`
is a Gobra keyword); some intermediate results are stored in fresh local
variables (e.g. `res := l.root.next; return res`) so proof annotations can
be placed between the read and the use; return parameters are named; and
`New` introduces a variable for `new(List)`. `go build`, `go vet` and
`go test` still pass on the transformed code.

## Tests (list_test.gobra)

Every function of `list_test.go` is translated; `t.Errorf` calls become
`assert` statements that are proven unreachable, so the tests hold for the
specifications statically. Deviations, all semantics-preserving:

- `TestList` and `TestExtending` are split into sequential continuation
  functions (`testListMoves`, `testExtendingBack`, ...) because a single
  600-line straight-line member is too expensive for the verifier.
- Values later inspected with type assertions are written `int(1)` /
  `string("banana")`: Gobra does not apply Go's default-type rule when an
  untyped constant is boxed into `any`, so the dynamic type of a bare `1`
  is unknown to the verifier. The Go meaning is identical.
- Discarded results of `InsertBefore`/`PushBack`/... are bound to names so
  ghost arguments can refer to the created elements; parallel swap
  assignments use explicit temporaries; `checkList` compares values with
  `===` instead of the `.(int)` type assertion.

`example_test.go` is not translated (it exercises `fmt`, not the list).

## Running the verification

```sh
java -jar gobra.jar --config <repo>/src/container/list
```

(Requires Z3 on `Z3_EXE`.) The whole package verifies in roughly 5–10
minutes on 4 cores; the most expensive members are `TestMove` and the
internal `move`, whose proofs cross-case over element positions.
