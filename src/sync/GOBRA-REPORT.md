# Specifying and verifying `sync.Mutex` with Gobra

**Status: work in progress.** `Lock` (fast path), `TryLock`, `Unlock` and
`unlockSlow` are verified. `lockSlow` carries the contract it has to satisfy but
is still marked `trusted`; discharging it is the remaining work.

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
* `ghc` — a handoff that a waiter has claimed but not yet installed.

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

Every assumption is listed here. There are no `assume` statements other than the
one noted in §A3, and no `trusted` members other than `lockSlow` while it is WIP.

**A1. The bit layout (`bitsLemma` in `mutex.gobra`).**
Gobra encodes `&`, `|`, `&^` and `>>` on non-constant operands as *uninterpreted*
functions — it cannot even prove that `&` is commutative — so nothing about
`mutex.go`'s bit twiddling reaches the solver. `bitsLemma` is a single bodiless
(hence assumed) lemma relating four abstract decoding functions both to the
arithmetic decomposition `s == locked + 2*woken + 4*starving + 8*waiters` and to
every bit expression `mutex.go` evaluates. Each clause is a concrete arithmetic
identity checkable by inspection. It also states `1 << mutexWaiterShift == 8`,
because Gobra folds constant `&`/`|` but not `<<`. Everything else about bits
(`decompUnique`, `bitsOf`) is *proved* from it.

**A2. The runtime semaphore (`runtime.gobra`).**
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
can be verified against.

## Comparison with the previous project

*To be written: the earlier project (A. Montini, ETH Zürich) predates Gobra's
invariants and modelled atomics differently.*
