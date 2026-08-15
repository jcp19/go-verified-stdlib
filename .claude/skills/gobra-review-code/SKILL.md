---
name: gobra-review-code
description: Review Gobra code — .gobra files, or .go files carrying //@ and /*@ @*/ annotations — for idiomatic style and specification conventions, covering annotation order, Go naming, .go/.gobra file separation, purity, permission strength (read fractions vs. `write`), `integer` arithmetic, `old` expressions, and interface specifications. Use whenever the user asks to review, critique, clean up, or sanity-check Gobra code, specs, contracts, predicates, lemmas or ghost code; when a diff or PR touches .gobra files or Gobra annotations; when the user pastes Gobra code and asks "does this look right?"; when they ask whether a contract demands too much permission; and when they ask about Gobra style, conventions, or naming. Use it before submitting Gobra code for human review, even if the user only asked "is this good?".
---

# Reviewing Gobra code

Gobra code is judged on two axes at once: does it verify, and does it read like something
another verification engineer can maintain. This skill covers the second axis — the
conventions that repeatedly come up in review and that a verifier will never complain about.

## How to run a review

1. **Find the Gobra surface.** `.gobra` files, and `.go` files with `//@` or `/*@ … @*/`
   annotations. Read whole files, not diffs alone: a contract only makes sense next to its
   declaration, and a naming problem is only visible next to the package boundary.
2. **Run `gofmt -l` / `gofmt -d` over the `.go` files** (§3). It is the one check a tool
   answers for you, and it catches the `//@` vs `// @` prefix drift for free.
3. **Work through the checks below**, in order. They are roughly sorted by how much damage
   they do.
4. **Report only real findings.** An empty review is a fine outcome. Do not pad with
   generic verification advice.
5. **Propose minimal diffs.** Proofs are brittle; unrelated churn costs the author a
   re-verification cycle and often a proof-stability debugging session. If a rewrite is
   large, say why it is worth it.

Report findings grouped into **Correctness / soundness** (wrong, unsound, or won't verify)
and **Style** (verifies fine, but reads badly or over-constrains clients), each as
`file:line — what — why — fix`:

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

### Contract conditions start in the same column

Pad the clause keywords so that the conditions themselves line up. A contract is read as a
list of assertions; ragged left edges make the reader re-find the start of each one, and
they hide the shape of the contract (which clauses are long, which are repeated).

```go
// ✗
//@ requires p > 0
//@ preserves acc(sep, p)
//@ ensures rhash == RKHash(seq(sep))
//@ decreases

// ✓
//@ requires  p > 0
//@ preserves acc(sep, p)
//@ ensures   rhash == RKHash(seq(sep))
//@ decreases
```

`preserves` and `invariant` are the longest keywords at nine characters, so padding every
keyword to nine puts the conditions in one column across a whole file — loop invariants
included, not just the function contract. Apply it to `.gobra` files too, where the
clauses have no `//@` prefix.

This is cosmetic, so raise it once per file rather than once per clause, and skip it
entirely if the author is mid-proof: re-verifying to land a whitespace change is a bad
trade.

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

### Run `gofmt` over the `.go` files

Annotations are comments, so nothing in the verifier notices when a `.go` file drifts out
of gofmt shape — but the Go toolchain, CI and every other reader do. Run it as part of the
review:

```bash
gofmt -l ./path/to/pkg      # lists files that need formatting
gofmt -d ./path/to/pkg      # shows what it wants
```

Careful with the exit status: `gofmt -l` exits 0 whether or not it lists anything, so
`gofmt -l pkg && echo clean` reports "clean" for a dirty tree. Check the *output*, not the
status.

The most common finding is the annotation prefix. gofmt rewrites a top-level `//@` to
`// @`, and `// @` is the better form to standardize on for exactly that reason: it is
what the formatter produces, so a file written that way stays clean. Gobra accepts both
spellings.

gofmt only rewrites comments at the top level, so a formatted file legitimately ends up
with both forms — `// @` on the clauses attached to declarations, `//@` on the ones
indented inside function bodies. That mixture is gofmt's doing, not an inconsistency to
flag.

Re-verify after formatting. It should be a no-op for the proof, and confirming that costs
one run.

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
is exactly right, and a read-only method requiring `write` is its own review finding (§4.3).

### 4.3 A read-only function should ask for read permission

`acc(x)`, `acc(x, write)`, and a bare predicate instance `x.Mem()` all mean *all* of the
permission. A non-pure function that never writes should not be asking for that. This is the
most common over-specification in Gobra contracts, and unlike a naming problem it is a real
API defect: the author pays nothing, and every caller pays forever.

Three things a `write` precondition takes away from callers:

- **A caller holding only a fraction cannot call the function at all.** Any client that
  itself received read access has nothing to hand over, so the read-only function is
  unreachable from exactly the contexts it was meant for.
- **Callers lose framing.** A caller that keeps a positive share across the call knows *for
  free* that nothing under that share changed. A caller that surrendered everything knows
  only what the postcondition spells out — which is why over-permissioned contracts grow
  postconditions whose only job is to say "and nothing else moved".
- **No two readers at once.** Two goroutines cannot both hold `write`, so the contract rules
  out concurrent reads for a function that could not race in the first place.

#### How to spot it

Flag a non-pure function when both of these hold:

- the contract takes `write` (`acc(x)`, `acc(x, write)`, `acc(x, 1)`, or a bare `x.Mem()`),
- the body assigns to nothing reachable through that parameter — no `*p = …`, no `p.f = …`,
  no `s[i] = …`, no `append`/`copy` into it — and calls nothing that demands write.

Getters, `Len`, `Peek`, `Contains`, `String`, `Equals`, `Validate` and marshalling routines
are the usual suspects.

#### The fix: a read-permission constant per package

The fix is *not* to sprinkle `1/2` and `1/4` across contracts, unless in contracts of private
functions when need be. Ad-hoc fractions do not compose: as soon as one read-only function
calls another, the amounts have to be split and lined up by hand. Give the package one
constant instead, and let every public contract that means "read" use it — read-only
functions then pass the amount straight through to each other, with no permission arithmetic
in sight.

```gobra
// mypkg/spec.gobra — ghost definitions of the package live here (§8)

// Enables Gobra in the current file.
// +gobra

package mypkg

// R is the permission amount this package's public contracts use to stand for
// read-only access. It has to be positive, small enough that any realistic holder
// can spare it, and larger than the R of the packages this one calls into.
ghost const R perm = 1/1000
```

`perm` is Gobra's type of permission amounts, and a package-level `perm` constant is
ordinary Gobra — `const p perm = 1/4` appears in Gobra's own regression suite, and the bare
`const` form is equally accepted here since `perm` is already a ghost type. Being an
exported constant, `R` is nameable by clients, as §2 requires of anything appearing in a
public contract. Two mechanical points:

- **Do not name the package `perm`.** The import would shadow Gobra's predeclared `perm`
  type in every file that uses it. `perms` is fine.
- **Keep the value a single literal fraction.** Nested arithmetic falls back to integer
  semantics — `perm((1/2)/1)` is `0`, not `1/2` — and a constant that is silently `noPerm`
  produces a baffling "permission might not suffice" on the *body*, not on the constant.

#### One constant per package, not one per project

A caller that hands away *everything* it holds for a location cannot frame that location
across the call: it holds nothing while the callee runs, so on return the value is unknown
unless the callee's postcondition pins it down. A single project-wide amount walks straight
into this, because caller and callee then ask for exactly the same fraction:

```go
import "pkg"

type T struct {
	name pkg.Name
	// … other fields
}

// requires acc(t, R)
func (t *T) GetName() (res string) {
	return t.name.ToString()   // also requires acc(&t.name, R) — takes the whole share
}
```

`GetName` holds exactly `R` of `&t.name`, gives all of it away, and can no longer prove that
`t.name` did not change. It costs nothing in a one-line body like this one, but it bites as
soon as the function reads state around the call.

So each package declares its own `R` and picks a value **larger than the `R` of every package
it calls into** — the deeper a package sits, the smaller its fraction. Callers then always
retain a positive remainder and frame for free. The same trap exists between two read-only
functions *within* a package: the usual way out is to make the inner one `pure`, since a pure
function never takes permission away (§4.2), and the fallback is the `ghost p perm` parameter
below.

At the use site:

```go
// ✗ — Len only reads, but takes the whole structure
requires l.Mem()
ensures  l.Mem()
ensures  res == len(l.View())
ensures  l.View() == old(l.View())   // only needed because the caller gave up everything
func (l *List) Len() (res int)

// ✓ — the caller keeps a share, so "nothing moved" needs no stating
preserves acc(l.Mem(), R)
ensures   res == len(l.View())
func (l *List) Len() (res int)
```

A client in another package writes `acc(l.Mem(), list.R)`. If it names that package only from
annotations, the import goes in an annotation too — `//@ import "…/list"` — so the `.go` file
stays compilable Go (§3).

**Be honest about what the rewrite costs.** The amount multiplies through the predicate
body, so every `fold`, `unfold` and `unfolding` in the function has to carry it —
`unfold acc(l.Mem(), R)` yields `acc(&l.head, R)`, not `acc(&l.head)`, and the
proof below it may need the same treatment. That is a real diff, so propose it when the
function is genuinely read-only and part of an API, and skip it for a package-private helper
with one caller.

#### Why not `acc(x, _)`

The wildcard is the tempting shortcut, and it breaks callers in a way a constant does not:
the amount handed back is *some* positive amount, not the one that was handed over, so a
caller can never reassemble what it started with.

```go
preserves acc(p, _)
func (p *pair) sum() (s int)

func client() {
	p := &pair{3, 5}
	res := p.sum()
	p.left = res  // ERROR: Permission to p.left might not suffice.
}
```

With a named constant this works: a caller holding `write` gives away `R`, gets `R` back, and
holds `write` again.

#### When the constant is not enough

A `ghost p perm` parameter with `requires p > 0` is strictly more versatile, and the price is
an extra argument at every call site plus a `p` threaded through every intermediate contract.
Keep it for the cases the constant genuinely cannot express:

```go
requires  p > 0
preserves acc(l.Mem(), p)
func (l *List) Get(i int, ghost p perm) (res int)
```

- **Splitting a read share further** — a function that holds `acc(x, R)` and fans out to
  goroutines that each need their own share. Each would need `R/2`, which no fixed constant
  names.
- **Amount-polymorphic APIs** — a wrapper or callback that must return exactly the caller's
  amount, when that amount is chosen elsewhere and is not `R`.

Everything else — the ordinary sequential read-only method — is served by the constant, and
that is the version worth suggesting in review.

Finally, this check does not reopen §4.2: in a **pure** function the amount is meaningless,
so plain `acc(x)` stays correct there, and `R` does not belong in its contract.

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

## 8. File organization
Definitions of ghost types of the package under verification, predicate definitions, and ghost functions
that are not lemmas should be defined in the `spec.gobra` file. Lemmas should be defined in a separate file
(`lemmas.gobra`). Any trusted ghost member or member that, for some reason is not fully verified, should be
in `assumptions.gobra`. This is a super strict check!!!!

## 8b. Ghost state on a struct

When a type carries its abstraction in ghost fields, the fields themselves stay
private (like any other field) but the **getters are part of the API** and must
be exported, along with every pure function a contract mentions:

```go
type List struct { /*@ ghost es seq[*Element] @*/ }  // private field: fine

ghost requires l.Mem() decreases
pure func (l *List) Es() seq[*Element] { … }         // must be exported: contracts use it
```

Two things to check on such a package:

- **Read-only methods that forget "nothing changed".** `preserves l.Mem()` no
  longer pins the abstraction, so a getter-based contract needs an explicit
  `ensures l.Es() == old(l.Es()) && …`. Its absence is a real spec gap: a
  client calling `Front()` loses everything it knew about the list.
- **Relations sealed inside the predicate.** If contracts index into a derived
  sequence, the getter should export what makes that well-formed —
  `ensures len(res) == len(l.Es())` — rather than each caller re-proving it.

## 9. Recurring findings worth a second look

These come up often enough in review to be worth scanning for, but they are judgement calls
— report them with the reasoning, not as violations.

- **`assume` and `trusted` creep.** Every `assume` in non-test code is a hole in the proof.
  Ask whether it can be discharged, and if not, whether it is documented as a standing
  assumption. A PR that adds one deserves an explicit note.
- **Postconditions restating a pure function's body.** Gobra reasons about pure functions
  through their bodies, so `ensures res == <the body>` is redundant. It also pins the body
  into the contract, which makes later refactoring a breaking change.
- **`preserves P` instead of `requires P` + `ensures P`.** Shorter, and makes the intent —
  this resource is borrowed, not consumed — visible at a glance.
- **Missing or over-clever termination measures.** `decreases` is mandatory on pure and
  ghost functions, so its absence is a verification error rather than a review finding; but
  a measure that is a large arithmetic expression where a predicate instance would do is
  worth a comment.

## 10. What not to flag

Review noise is expensive here: a Gobra author is usually mid-way through a proof, and every
false finding costs a context switch away from it.

- **Proof structure** — `assert` steps, `fold`/`unfold` placement, lemma calls — unless it is
  provably dead. Whether a proof step is needed is something only the verifier settles, and
  guessing wrong sends the author into a re-verification cycle for nothing.
- **A precondition that looks like it belongs in the body.** The natural review note on a
  clause like `requires forall k :: {&s[lo:hi][k]} &s[lo:hi][k] == &s[lo+k]` is "assert this
  at the top of the body instead of cluttering the contract". Check the neighbouring clauses
  first: if any of them reads the reslice — `seq(s[lo:hi])`, `s[lo:hi][k]` — then that
  correspondence is what gives the clause its permission, and a contract is checked
  independently of the body, so an assert inside is too late. The failure is not subtle when
  it happens (`Permission to seq(s[lo:hi]) might not suffice`, reported *on the requires
  line*), but it costs the author a round trip. The same reasoning applies to any
  precondition whose job is to make a later clause well-defined rather than to constrain the
  caller.
