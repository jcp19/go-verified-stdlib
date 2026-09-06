# gobra

This directory holds Gobra-only sources for verifying the standard library:

- specifications and stubs for dependencies that are not verified themselves,
- verified utility packages containing ghost code shared across packages.

It is listed in the `includes` field of `../gobra-mod.json`, so imports are
resolved against this directory in addition to the module root (`../`).

Current contents:

| Package | Holds |
|---|---|
| `arith` | lemmas about non-linear integer arithmetic |

`arith` exists so that a package which needs a non-linear fact can ask for it
by name instead of leaving the solver to find it. Non-linear arithmetic is
where Z3 wanders, and a package that keeps it out of its own proofs can be
verified with `--disableNL`, which makes the solver leave products of
non-constants alone. `internal/bytealg` is verified that way; see
`../internal/bytealg/GOBRA.md`.

Nothing here is compiled by the Go toolchain; `.gobra` files are only read by
Gobra.

`TOOLCHAIN.md` records which Gobra and Z3 versions the verified packages need,
and how to reproduce a verification run locally.
