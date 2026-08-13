---
name: gobra-review-code
description: Review Gobra code — .gobra files, or .go files carrying //@ and /*@ @*/ annotations — for idiomatic style and specification conventions, covering annotation order, Go naming, .go/.gobra file separation, purity and permission discipline, `integer` arithmetic, `old` expressions, and interface specifications. Use whenever the user asks to review, critique, clean up, or sanity-check Gobra code, specs, contracts, predicates, lemmas or ghost code; when a diff or PR touches .gobra files or Gobra annotations; when the user pastes Gobra code and asks "does this look right?"; and when they ask about Gobra style, conventions, or naming. Use it before submitting Gobra code for human review, even if the user only asked "is this good?".
---

# Reviewing Gobra code

Gobra code is judged on two axes at once: does it verify, and does it read like something
another verification engineer can maintain. This skill covers the second axis — the
conventions that repeatedly come up in review and that a verifier will never complain about.

## How to run a review

1. **Find the Gobra surface.** `.gobra` files, and `.go` files with `//@` or `/*@ … @*/`
   annotations. Read whole files, not diffs alone: a contract only makes sense next to its
   declaration, and a naming problem is only visible next to the package boundary.
2. **Work through the checks below**, in order. They are roughly sorted by how much damage
   they do.
3. **Report only real findings.** An empty review is a fine outcome. Do not pad with
   generic verification advice.
4. **Propose minimal diffs.** Proofs are brittle; unrelated churn costs the author a
   re-verification cycle and often a proof-stability debugging session. If a rewrite is
   large, say why it is worth it.

Report findings grouped into **Correctness / soundness** (wrong, unsound, or won't verify)
and **Style** (verifies fine, reads badly), each as `file:line — what — why — fix`:

```
### Style

- `router/dataplane.gobra:88` — `pure` sits above the spec clauses. Everyone reads
  `pure func` as one token. → move it to `pure func absPkt(...)`.
```

## 1. Declaration shape

### `pure` goes immediately before `func`

The grammar accepts the modifiers in any order, so a misplaced `pure` parses fine. It still
reads badly: everyone scans for `pure func` as a single token, and a `pure` floating above
the preconditions is easy to miss entirely.

```go
// ✗
pure
requires acc(x)
decreases
func (x *node) Value() int { … }

// ✓
requires acc(x)
decreases
pure func (x *node) Value() int { … }
```

The canonical order is: `trusted`, then `ghost` alone on the first line, then `requires` / `ensures`, then
`decreases`, then any remaining modifiers (`opaque`), then `pure func`.

### Abstract functions carry `trusted`

A function with a specification and no body is an assumption: Gobra takes the contract on
faith. Written as a bare bodyless declaration it looks like an unfinished stub. `trusted`
names the assumption, so `grep -rn trusted` gives an honest inventory of the trusted base.

```go
// ✗ — silently assumed
requires acc(b.Mem(), _)
ensures  res == b.Len()
func size(b *Buffer) (res int)

// ✓
trusted
requires acc(b.Mem(), _)
ensures  res == b.Len()
func size(b *Buffer) (res int)
```

The exception is a `.gobra` file acting as a *header* for a package that is not verified —
there the whole file is the assumption, and marking each declaration adds nothing.

## 2. Naming and package boundaries

Gobra names follow Go's rules, including for ghost declarations: exported names start with
an upper-case letter, everything else is package-private; `CamelCase`, never `snake_case`.

Beyond that: **every symbol appearing in the contract of an exported declaration must
itself be exported.** A contract is part of the API. A client in another package has to
state it, establish it, and reason about it — which it cannot do if the predicate or pure
function naming the relevant state is invisible.

```go
// ✗ — clients can see Process but cannot mention mem
pred mem(x *T) { … }

requires mem(x)
func Process(x *T)

// ✓
pred Mem(x *T) { … }

requires Mem(x)
func Process(x *T)
```

This covers predicates, pure and ghost functions, ghost types and fields, and constants.

## 3. `.go` and `.gobra` files carry different things

In a project that has both kinds of files, the split is:

- **`.go` files: non-ghost definitions only.** Executable code, with its specifications in
  `//@` / `/*@ @*/` annotations.
- **`.gobra` files: ghost definitions only.** Predicates, lemmas, ghost functions and
  types, implementation proofs.

The point is that the `.go` files stay compilable, `go build`-able Go, and the proof
infrastructure stays in files the Go toolchain never sees.

The one exception is again the header case: a `.gobra` file may hold specifications for a
package whose `.go` files are not (yet) verified.

## 4. Purity and permissions

### 4.1 Keep pure ghost functions free of resources

A pure ghost function whose arguments are already mathematical values (`seq`, `set`,
`mset`, `dict`, `integer`, ADTs) should not require permissions. Resourceful preconditions
force every caller — including other specifications and lemma statements — to hold and
thread those resources.

There are exceptions: **abstraction functions** that maps heap state into the mathematical
domain in the first place. That one is *supposed* to require access to the state it
abstracts; it is the boundary. Other exceptions are getters, non-ghost functions, or functions
that define properties on the representation.

Consider the following example, where we have the specification of a parsing function
that parses a pair of 32-bit integers fields from a `[]byte`:

```gobra
// ✗ we need to carry permissions along to the functions called from this one.
ghost
requires 8 <= len(b)
requires forall i int :: 0 <= i && i < len(b) ==> acc(&b)
decreases
pure func ParsePairSpec(b []byte) Pair {
  return Pair {
    Fst : ParseInt32Spec(b[0:4]),
    Snd : ParseInt32Spec(b[4:8]),
  }
}
```
This is annoying to work with, as we need to somehow prove that we have the ownership of all ghost
locations for both sublices when we call ParseInt32Spec (which itself requires ownership of its input slice).
A much better solution is to introduce an abstraction function to reduce the permission reasoning to a minimum:
```gobra
// ✓ abstraction function — resources carried at the boundary of the specs
ghost
requires 8 <= len(b)
requires forall i int :: 0 <= i && i < len(b) ==> acc(&b)
decreases
pure func ToSeq(b []byte) seq[byte] {
  // impl ommitted
}

ghost
requires 8 <= len(b)
decreases
pure func ParsePairSpec(b seq[byte]) Pair {
  return Pair {
    Fst : ParseInt32Spec(b[0:4]),
    Snd : ParseInt32Spec(b[4:8]),
  }
}
```
With this spec (and the analogous changes applied to ParseInt32Spec too), we can completely remove permission reasoning in a good part of our functional specs.


### 4.2 No permission amounts inside pure functions

In current Gobra, the permission amount in a pure function's precondition no longer carries
meaning: a pure function performs no heap modification, and it implicitly returns
everything it received, so any positive amount behaves identically. Writing a specific
fraction states a constraint that is not enforced and misleads readers into thinking the
callers' permission bookkeeping matters here. (The legacy behaviour survives only behind
`--respectFunctionPrePermAmounts`, which new projects should not use.)

So `acc(e, X)` with `X` a fraction, `write`, or `_` does not belong in the contract or body
of a pure function. Plain `acc(e)` is right. The same applies to `unfolding` expressions
occurring anywhere in a pure function — including inside implementation proofs of pure
interface methods, where `unfolding acc(x.Mem(), 1/2) in …` is a common leftover.

```go
// ✗
requires acc(c.Mem(), 1/2)
decreases
pure func (c *counter) HasNext() bool {
	return unfolding acc(c.Mem(), 1/2) in c.f < c.max
}

// ✓
requires c.Mem()
decreases
pure func (c *counter) HasNext() bool {
	return unfolding c.Mem() in c.f < c.max
}
```

Non-pure functions are unaffected — there, asking for the smallest amount you actually need
is exactly right, and a read-only method requiring `write` is its own review finding.

## 5. Prefer `integer` in specifications

Go's sized integer types drag their bounds into every arithmetic assertion. Under
`--overflow`, a postcondition like `res == 2 * x` on `int32` obliges you to constrain the
input, even though the property you meant to state is about mathematics, not about
`int32`. Casting to `integer`, Gobra's unbounded ghost integer type, states the intended
property directly and needs no bounds annotation.

```go
// ✗ — forces a precondition like `requires -(1 << 30) <= x && x < 1 << 30`
ensures res == 2 * x
func double(x int32) (res int32)

// ✓
ensures integer(res) == 2 * integer(x)
func double(x int32) (res int32)
```

Flag arithmetic-heavy specs written over sized types, and flag bounds preconditions that
exist only to keep such a spec well-defined — they usually disappear under `integer`.

Two things to get right when suggesting the rewrite:

- **Convert the operands, not the expression.** `integer(a + b)` still evaluates `a + b` at
  the sized type and can overflow there; `integer(a) + integer(b)` cannot.
- **The body may legitimately still need bounds** to pass its own overflow checks. The claim
  is only that the *contract* should not be the reason those bounds exist — so check whether
  a precondition is still doing work before proposing its removal.

## 6. `old` applies to heap-dependent expressions only

`old(e)` evaluates `e` in the pre-state. That only changes anything if `e` depends on the
heap or on a resource such as a predicate instance. Applied to anything else — a parameter,
a local, a ghost value, a slice's length, arithmetic over these — `old` is inert, and its
presence signals that the author believed something was changing when it was not. Treat it
as an error, not a stylistic wart.

```go
// ✗ — n, len(s) and the arithmetic are all heap-independent
ensures res == old(n) + 1
ensures len(s) == old(len(s))

// ✓ — the field and the abstraction function read the heap
ensures x.left == old(x.left) + n
ensures l.Abs() == old(l.Abs()) ++ seq[int]{v}
```

Watch for the near-miss `old(f(x))` where `f` is pure but heap-independent: it is just
`f(x)`.

Rule of thumb: the argument of `old` has to *reach through* something — a field selection, a
dereference, an index, an `unfolding`, or a pure function that requires permissions.

## 7. Interfaces: a pure ghost method per non-ghost method

*Suggested, not required.* For an interface with non-ghost, non-pure methods, give each one
a pure ghost method that acts as its specification, and write the method's contract in
terms of it. Implementations then say what they compute by defining one pure function,
rather than by restating a bespoke postcondition, and clients reason against a stable
mathematical description instead of an implementation-shaped one.

```go
type Buffer interface {
	pred Mem()

	// Abs is the specification of the interface's state.
	ghost
	requires Mem()
	decreases
	pure Abs() seq[byte]

	// Write's contract is stated entirely through Abs.
	requires Mem()
	ensures  Mem()
	ensures  Abs() == old(Abs()) ++ seq[byte]{b}
	Write(b byte)
}
```

Raise this when an interface's postconditions are visibly leaking implementation detail, or
when two implementations were given incompatible-looking contracts for the same method. Do
not raise it on a one-method interface with an already-crisp contract.

## 8. Recurring findings worth a second look

These come up often enough in review to be worth scanning for, but they are judgement calls
— report them with the reasoning, not as violations.

- **`assume` and `trusted` creep.** Every `assume` in non-test code is a hole in the proof.
  Ask whether it can be discharged, and if not, whether it is documented as a standing
  assumption. A PR that adds one deserves an explicit note.
- **Postconditions restating a pure function's body.** Gobra reasons about pure functions
  through their bodies, so `ensures res == <the body>` is redundant. It also pins the body
  into the contract, which makes later refactoring a breaking change.
- **Permissions stronger than needed.** A non-pure function that only reads should ask for a
  fraction, not `write` — otherwise callers cannot run it concurrently or keep their
  own read access across the call.
- **`preserves P` instead of `requires P` + `ensures P`.** Shorter, and makes the intent —
  this resource is borrowed, not consumed — visible at a glance.
- **Missing or over-clever termination measures.** `decreases` is mandatory on pure and
  ghost functions, so its absence is a verification error rather than a review finding; but
  a measure that is a large arithmetic expression where a predicate instance would do is
  worth a comment.

## 9. What not to flag

Review noise is expensive here: a Gobra author is usually mid-way through a proof, and every
false finding costs a context switch away from it.

- **Proof structure** — `assert` steps, `fold`/`unfold` placement, lemma calls — unless it is
  provably dead. Whether a proof step is needed is something only the verifier settles, and
  guessing wrong sends the author into a re-verification cycle for nothing.
