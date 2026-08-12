# gobra

This directory is on Gobra's include path (see `../gobra-mod.json`). It holds
code that supports the verification of the standard library but that is not
part of it:

- specifications and stubs for packages that are not verified themselves, and
- verified utility packages containing ghost code shared across packages.

Files here are not part of the Go standard library and are ignored by the Go
toolchain.
