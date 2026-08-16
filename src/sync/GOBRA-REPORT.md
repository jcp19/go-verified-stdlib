# Specifying and verifying `sync.Mutex` with Gobra

**Status: `sync.Mutex` verifies.** `Lock`, `lockSlow`, `TryLock`, `Unlock` and
`unlockSlow` are all verified against the contracts below. Both `throw` sites are
proved *unreachable*: the mutex never reports an inconsistent state. Gobra
reports 0 errors on `src/sync` in about 95 s.

The trusted base is one file, `assumptions.gobra`, plus one `assume` statement in
`mutex.go` (§A3). Nothing else in the package is trusted.

### Files

| file | what |
| --- | --- |
| `mutex.go` | the Go implementation, with its proof in `//@` annotations |
| `spec.gobra` | ghost state, the invariant, and the client-visible ghost interface |
| `lemmas.gobra` | the two *proved* lemmas about the state word's bit layout |
| `assumptions.gobra` | the bit-layout axiom and the runtime primitives — the whole trusted base |
| `mutex_client_test.gobra` | verified clients, checking the specs are usable from outside |
| `gobra.json` | package configuration (see §F8 for `more_joins`) |

## What is being verified, and against which specification

The client-visible contracts are taken from Gobra's own model of the package,
[`src/main/resources/stubs/sync/mutex.gobra`](https://github.com/viperproject/gobra/blob/master/src/main/resources/stubs/sync/mutex.gobra),
so that code verified against the stub keeps verifying against the real
implementation:

```gobra
pred (m *Mutex) LockP()
pred (m *Mutex) UnlockP()

ghost requires acc(m.LockP(), _) decreases _
pure func (m *Mutex) LockInv() pred()

ghost requires inv() && acc(m) && *m == Mutex{}
      ensures m.LockP() && m.LockInv() == inv decreases
func (m *Mutex) SetInv(ghost inv pred())

requires acc(m.LockP(), _)
ensures  m.LockP() && m.UnlockP() && m.LockInv()()
func (m *Mutex) Lock()

requires acc(m.LockP(), _) && m.UnlockP() && m.LockInv()()
ensures  m.LockP()
decreases
func (m *Mutex) Unlock()
```

The stub's `requires lowContext()` on `Lock`/`Unlock` is a secure-information-flow
side condition and is out of scope here, as agreed. It is also not expressible on
an implemented method: with hyper mode off Gobra rejects `lowContext()` in the
contract of any member that has a body, and with hyper mode on the mutex cannot
discharge the resulting noninterference obligations, because its control flow
genuinely depends on shared, non-low state. Dropping a *precondition* only
weakens what the implementation demands of its callers, so every client verified
against the stub still satisfies the contract proved here.

`TryLock` is not in the stub; it is given the analogous contract.

## The protocol

`m.state` packs four fields into one word:

| bits | meaning |
| --- | --- |
| 0 | `mutexLocked` |
| 1 | `mutexWoken` |
| 2 | `mutexStarving` |
| 3.. | waiter count |

The mutex is *logically free* — the protected resource `LockInv()()` sits inside
the invariant — exactly when `mutexLocked` and `mutexStarving` are both clear.
`mutexStarving` counts as held because in starvation mode ownership is handed
from the unlocking goroutine straight to a waiter through the runtime semaphore,
and while it is in flight neither of them has `mutexLocked` set.

Ownership is tracked by ghost tokens, each a half-permission to a ghost field so
that holding one is exclusive and its holder can read the corresponding bit off
the invariant:

* `gl` — held by the lock holder. `UnlockP()` *is* this token. Out ⟺ `mutexLocked` set.
* `gw` — the right to clear `mutexWoken`; this is what `lockSlow`'s local `awoke` stands for. Out ⟺ `mutexWoken` set.
* `ghc` — a handoff a waiter has claimed but not yet installed. It also records
  the waiter count seen at claim time; since only the claimer ever decrements
  that count, and does so once, this is a lower bound that stays valid and is
  what justifies subtracting a waiter in the `delta` update.

and invariant-owned flags record resources parked *inside* the invariant on
behalf of a semaphore ticket: `gh` (a parked ownership handoff) and `gws` (a
parked `gw` token).

### Why the semaphore payload is a bare ticket

`runtime_Semrelease` is called from two places with opposite intentions:
`unlockSlow`'s normal path merely wakes a sleeper, its starving path hands over
ownership. A goroutine returning from `runtime_SemacquireMutex` cannot tell which
one woke it, so the payload can be neither "ownership" nor a disjunction (Viper
has no disjunction of resources).

The payload is therefore a bare ticket `semTicket(m) = acc(&m.gt, 1/4)`, and the
resource it entitles the bearer to stays parked in the invariant, tagged `gws` or
`gh`. The bearer disambiguates at *redemption* time, inside the critical region
that reads the state word:

* `mutexStarving` clear ⟹ `gh` is false (a parked handoff forces starvation
  mode) ⟹ the ticket is the parked `gw` token; the goroutine becomes `awoke`.
* `mutexStarving` set ⟹ `mutexWoken` is clear (the two are mutually exclusive)
  ⟹ `gw` is not out at all ⟹ `gws` is false ⟹ the ticket is the parked
  handoff; the goroutine owns the mutex.

The counting is done with permissions: the invariant keeps `acc(&m.gt, 1/2)` plus
a quarter for each of `gws`/`gh` that is *false*, so a ticket holder that opens
the invariant would hold 5/4 of `&m.gt` if both were false — more than write
permission, a contradiction. This is also what rules out two goroutines
simultaneously believing they were handed ownership, the step that would
otherwise let both add `mutexLocked` to the state word.

## Assumptions

Every assumption is listed here. A1 and A2 make up `assumptions.gobra`, the only
`trusted` declarations in the package; A3 is the only `assume` statement; A4-A8
are modelling decisions rather than declarations.

**A1. The bit layout (`bitsLemma` in `assumptions.gobra`).**
Gobra encodes `&`, `|`, `&^` and `>>` on non-constant operands as *uninterpreted*
functions — it cannot even prove that `&` is commutative — so nothing about
`mutex.go`'s bit twiddling reaches the solver. `bitsLemma` is a single bodiless
(hence assumed) lemma relating four abstract decoding functions both to the
arithmetic decomposition `s == locked + 2*woken + 4*starving + 8*waiters` and to
every bit expression `mutex.go` evaluates. Each clause is a concrete arithmetic
identity checkable by inspection. It also states `1 << mutexWaiterShift == 8`,
because Gobra folds constant `&`/`|` but not `<<`. Everything else about bits
(`decompUnique`, `bitsOf`) is *proved* from it.

**A2. The runtime semaphore (`assumptions.gobra`).**
`runtime_SemacquireMutex` / `runtime_Semrelease` are implemented in package
`runtime`; they are specified as a resource-transferring semaphore. Resources are
conserved: acquirers never obtain more payloads than releasers deposited. Not
modelled: blocking/liveness (`runtime_SemacquireMutex` deliberately has no
termination measure), queue discipline (`lifo`, `handoff`) and fairness.

**A3. The waiter count never overflows.**
`newv += 1 << mutexWaiterShift` in `lockSlow` is unguarded in the Go source: with
2²⁸−1 waiters already queued it overflows into the sign bit and corrupts the
state word. The proof carries `numWaiters(m.state) <= maxWaiters` and needs
`assume nn < maxWaiters` at that one increment. This is a real (if unreachable in
practice — each waiting goroutine costs at least a stack) gap in the
implementation.

**A4. `m.state` is read atomically.**
`mutex.go` reads `m.state` with plain, non-atomic loads (`oldv := m.state`) while
other goroutines CAS it. Under the Go memory model those are data races. They are
modelled as `atomic.LoadInt32`, the standard "benign race" reading, which is what
the code means and what every supported architecture actually executes.

**A5. `sync/atomic` (`src/gobra/sync/atomic/atomic.gobra`).**
The operations are architecture-specific assembly, so their contracts are
assumed. They are modelled as sequentially consistent. `Add*` does *not* model
wrap-around: the contracts require the caller to rule out overflow, because
assuming exact arithmetic without that precondition would be unsound (Gobra
assumes a sized integer is always in range, so an overflowing addition with an
exact postcondition proves `false`).

**A6. `internal/race` models the non-race build.**
`race.Enabled` is the constant `false`, as in `norace.go`, which makes every
`if race.Enabled { … }` block statically dead. The operations carry
`requires false`, so calling one outside such a block is reported.

**A7. `unsafe.Pointer` is modelled as the empty interface.**
Only enough to make `unsafe.Pointer(m)` type-check inside those dead
`race.Enabled` blocks. Code that actually dereferences an unsafe pointer is
rejected, not mis-verified.

**A8. The CAS-retry loop in `unlockSlow` terminates** (`decreases _`). Gobra's
stub gives `Unlock` a termination measure; the retry loop is lock-free but not
wait-free, so its termination needs a fairness assumption Gobra cannot express.
`lockSlow` needs no such assumption: `Lock` has no termination measure, matching
the stub, because `runtime_SemacquireMutex` blocks.

Not an assumption, but worth recording: `throw` carries `requires false`, the
contract Gobra's builtin package gives `panic`. Both call sites are therefore
*proved* unreachable rather than assumed away.

## Changes to the Go source

The implementation is unchanged except for these behaviour-preserving edits, each
forced by a Gobra limitation:

1. `old`/`new` are Gobra keywords: locals renamed to `oldv`/`newv`.
2. `atomic` is a Gobra keyword: the import is aliased, `atomics "sync/atomic"`.
3. `starvationThresholdNs = 1e6` → `1000000`: Gobra rejects float literals.
4. Atomic calls inside a `critical` region must be a statement whose arguments are
   variables or literals, so `&m.state`, `-mutexLocked` and `oldv|mutexLocked`
   are hoisted into locals, and results are assigned to a pre-declared variable
   rather than declared with `:=`.
5. `TryLock`'s result is named (`res`) so the contract can mention it.
6. In `lockSlow`, the spin-path CAS is lifted out of the `&&` chain it sat in, for
   the same reason as (4): an atomic operation has to be a statement of its own
   inside a critical region. The short-circuit behaviour is unchanged — the CAS
   was the last conjunct, so it ran exactly when the preceding conditions held.

## Are the specifications any good?

An internal proof can be perfectly sound and still specify the wrong thing, so
the specification is exercised from the outside in two files.

`mutex_test.gobra` ports `TestMutex` and `HammerMutex` from `mutex_test.go` under
the usual transformation — drop the `testing.T` parameter, turn each call into
the testing framework into an `assert`. Nothing else about them changes: the
ported `TestMutex` still starts ten goroutines running `HammerMutex`, each doing
a thousand `Lock`/`Unlock`/`TryLock` rounds, and still joins them over a channel.
All of that verifies. **One assertion does not, and it is a genuine gap in the
specification rather than in the proof — see F10.** The tests that are not
ported, and why, are listed at the bottom of that file: `TestMutexMisuse` forks a
subprocess, `TestMutexFairness` measures wall-clock latency, `TestSemaphore`
needs a semaphore that starts with a token outstanding, and the benchmarks drive
`testing.B`.

`mutex_client_test.gobra` adds clients written from scratch, checking the
properties the tests exist to establish:

* a client sets a mutex up with `SetInv` over a counter predicate, and `Lock`
  really does hand the counter over — the client can mutate it without holding
  any permission of its own;
* the same mutex is passed to two client functions, each holding only
  `acc(m.LockP(), _)`. Sharing the right to *use* a mutex works;
* `TryLock` yields the resource only when it succeeded;
* a value written under the lock is still there when read under the same lock.

Two negative checks were run (not committed, since Gobra has no
expect-failure annotation for user projects):

* unlocking twice is rejected — *"Permission to `m.UnlockP()` might not suffice"*.
  The right to unlock is not shareable;
* `assert false` at three points in the proof is rejected, so the verified paths
  are genuinely reachable and the result is not vacuous.

## Findings

### F1. Go: the waiter count can overflow
See A3. `lockSlow` increments the waiter field with no bound check.

### F2. Go: `m.state` is read non-atomically
See A4. `lockSlow` and `unlockSlow` read `m.state` with plain loads concurrently
with CAS updates by other goroutines.

### F3. Gobra: `atomic` is a hard keyword, so `sync/atomic` cannot be used
`ATOMIC : 'atomic'` is a lexer keyword, so `package atomic` fails to parse and so
does every qualified use `atomic.CompareAndSwapInt32(...)`. **No Go file that
imports `sync/atomic` under its default name can be verified by Gobra today.**
Making it a contextual keyword (as `pure`/`trusted` effectively are) would fix it.

### F4. Gobra: `<<` is not constant-folded, but `&`/`|` are
`assert 1<<3 == 8` fails while `assert mutexLocked|mutexStarving == 5` succeeds.
Shifts go through the uninterpreted `intShiftLeft` even when both operands are
constants. This is why A1 has to state `1 << mutexWaiterShift == 8`.

### F5. Gobra: `pred()`-typed struct fields are not addressable
`acc(&m.inv, _)` on a `ghost inv pred()` field crashes Gobra with
`requirement failed: expected shared location`. This is the same limitation that
made Gobra's own `spinlock.gobra` test pass its lock by value. Worked around by
storing the invariant as `option[pred()]`.

### F6. Gobra: critical regions reject safe argument forms
`validArgAtomicFuncCall` accepts only literals, exclusive named operands and
certain selections, so `atomic.CompareAndSwapInt32(&m.state, oldv, oldv|mutexLocked)`
is rejected even though `&m.state` and `oldv|mutexLocked` cannot change
concurrently. Address-of a field of an exclusive variable, and pure expressions
over locals, would be safe to allow.

### F7. Gobra: `lowContext()` cannot appear on an implemented method
With hyper mode off, `removeLow` raises a consistency error for any member with a
body, so Gobra's own `sync.Mutex` stub carries a contract that no implementation
can be verified against. (Secure information flow is out of scope for this work,
so this only matters as a note on the stub.)

### F8. Performance: the invariant's conditional permissions cause path explosion
`mutexInv` carries several impure implications (`!m.gl ==> acc(&m.gl, 1/2)` and
friends), and Silicon forks on each of them at *every* unfold. `lockSlow` opens
the invariant six times, so with the default `more_joins` setting the package
went from ~95 s to over 20 minutes without finishing. Setting

```json
"more_joins": "impure"
```

in `src/sync/gobra.json` — join at impure branch points — brings it back to
~95 s. This is worth knowing for anyone writing invariants in this style: the
half-permission token idiom is naturally full of conditional permissions, and it
is the number of them *per predicate*, not the size of the method, that sets the
cost.

### F10. The specification cannot say that a mutex is unshared
`TestMutex` checks two things about `TryLock`, and only one of them is provable.

That `TryLock` *fails* while the caller holds the lock does verify, with a hint:
if it had succeeded the caller would hold the lock invariant twice, and a lock
invariant worth having is not duplicable. (Note the dependency — for a mutex
protecting `PredTrue{}` the assertion is unprovable, because two copies of
nothing are still nothing.)

That `TryLock` *succeeds* on an uncontended mutex does not verify, and no proof
hint helps. The gap is structural. `Lock`'s contract goes from
`acc(m.LockP(), _)` to `m.LockP()`: a full `LockP` is recoverable from any
wildcard fraction, which forces `LockP` to be duplicable — as it is here, since
its body is `Invariant(...)` plus wildcards and pure facts. So a client can never
hold evidence that nobody else can reach the mutex, not even immediately after
creating it. From the specification's point of view some other goroutine may
always be holding the lock, and `TryLock` is entitled to fail.

This is a property of the interface, not of this implementation, and it is worth
raising against the stub: expressing it would need a second, exclusive flavour of
`LockP` that a client holds before it shares the mutex and gives up on sharing —
which is exactly what `SetInv` could return instead of the duplicable one.

### F9. Gobra: the documented modifier order does not parse
`trusted` before `ghost` is rejected (*"Unexpected reserved word ghost"*); it has
to be `ghost` then `trusted`. Minor, but it contradicts the order the house style
guide gives.

## Comparison with the previous project

**Caveat about sources.** Neither the earlier report nor its code could be read
from this environment: `ethz.ch` is blocked by the network egress policy, and
`github.com/AxelMontini/gobra-semester-project` returns 404. What follows is
therefore a comparison of *approaches* — what changed in Gobra, and what a
pre-invariant treatment of atomics must look like — not a review of that code.
The specific claims below are about this development and about Gobra, and are
checkable here.

**What changed.** Before viperproject/gobra#983 Gobra had no invariants and no
notion of a physically atomic operation, so there was no sound way to let two
goroutines share a location that either of them writes. The available options
were all variants of *attaching the shared state to something else*: a predicate
handed around explicitly, a specification that pretends the atomic operation is
sequential, or a mutex-shaped wrapper — which is circular when the thing being
verified *is* the mutex. Today the shared word lives in one `Invariant`, opened
only by a `critical` region around a single `atomic` operation, and that is what
this development uses.

**Where a pre-invariant model is at risk of being unsound**, and how each risk is
discharged here:

1. *Plain reads of shared state.* `lockSlow` and `unlockSlow` read `m.state`
   non-atomically. Any model that gives a goroutine standing read permission to
   that word contradicts the write permission the CAS needs, and if it does not,
   the reads cannot be justified at all. Here they are modelled as atomic loads
   and the permission comes from the invariant, for the duration of one step
   (§A4, §F2).
2. *Ownership handed through the semaphore.* If `runtime_Semrelease` /
   `runtime_SemacquireMutex` are specified as no-ops, the starvation-mode handoff
   is invisible and the proof will "work" while permitting two goroutines to own
   the mutex at once. This is the subtlest part of `sync.Mutex` and needs the
   ticket discipline described above.
3. *Bit twiddling.* Gobra's `&`, `|`, `&^`, `>>` are uninterpreted (§F4), so any
   proof about `sync.Mutex` must supply the bit facts as axioms. It matters a
   great deal *which* axioms: a plausible-looking set can easily be inconsistent,
   which makes everything downstream provable. Here they are confined to one
   lemma whose every clause is a concrete arithmetic identity, and the rest is
   derived (§A1).
4. *Wrap-around.* An `AddInt32` contract with exact arithmetic and no overflow
   precondition is unsound in Gobra, because a sized integer is assumed to be in
   range — an overflowing addition then proves `false` (§A5). The stubs here
   require the caller to rule overflow out, which is what forced §A3 into the
   open.
