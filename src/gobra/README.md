# gobra

This directory holds Gobra-only sources for verifying the standard library:

- specifications and stubs for dependencies that are not verified themselves,
- verified utility packages containing ghost code shared across packages.

It is listed in the `includes` field of `../gobra-mod.json`, so imports are
resolved against this directory in addition to the module root (`../`).

Nothing here is compiled by the Go toolchain; `.gobra` files are only read by
Gobra.

`TOOLCHAIN.md` records which Gobra and Z3 versions the verified packages need,
and how to reproduce a verification run locally.
