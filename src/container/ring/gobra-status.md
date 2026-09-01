# Gobra verification status of container/ring

This file is the honest inventory of what is actually proven. A member counts
as **verified** only when it carries a real contract, has no `trusted`
annotation, no `requires false`, and no `assume` anywhere on its path.

Legend for *State*:

- `verified` — real contract, proved by Gobra, no assumptions.
- `stub` — `trusted` and/or `requires false`; the contract is taken on faith.
- `wip` — real contract, not yet passing.

## Members of the package

| Member | Contract | State | Notes |
| --- | --- | --- | --- |
| `(*Ring).init` | memory + functional | wip | private; lazy initialization of the zero value |
| `(*Ring).Next` | memory + functional | wip | |
| `(*Ring).Prev` | memory + functional | wip | |
| `(*Ring).Move` | memory + functional | wip | needs `StepIsWrap` |
| `New` | memory + functional | wip | ghost results carry the built ring |
| `(*Ring).Link` | none | **stub** | `trusted` + `requires false` |
| `(*Ring).Unlink` | none | **stub** | `trusted` + `requires false` |
| `(*Ring).Len` | memory + functional | wip | |
| `(*Ring).Do` | none | **stub** | `trusted` + `requires false`; needs a closure spec |

## Ghost members (spec.gobra, lemmas.gobra)

| Member | State | Notes |
| --- | --- | --- |
| `Mem` | n/a | predicate |
| `IsInit` | wip | |
| `Wrap`, `Step`, `Rot`, `RotV` | wip | pure ghost functions |
| `Visitor`, `VisitSpec` | wip | closure specification for `Do` |
| `WrapShift` | wip | body empty; relies on Z3's `%` axioms |
| `StepIsWrap` | wip | proof by induction on `n` |
| `Rotate` | not written | needed to re-root `Mem` at another element |

## Assumptions

None so far. Any `assume` introduced later must be listed here with a
justification.

## Scope

- Termination is in scope: every member and every loop carries a `decreases`.
- Overflow checking is **not** enabled (`--overflow` is not set in
  `src/gobra-mod.json`), so Gobra models Go's `int` as a mathematical integer.
  In particular `Unlink`'s `r.Move(n + 1)` is not proved free of the wraparound
  a real `n == math.MaxInt` would cause.
