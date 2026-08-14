# Gobra verification of `internal/bytealg` — `bytealg.go`

This package is partially verified with [Gobra](https://github.com/viperproject/gobra).
The scope of this report is the file `bytealg.go`; the remaining files of the
package (per-architecture assembly and their Go declarations) are outside the
verified scope and are stubbed where needed.

## What is verified

All six functions of `bytealg.go` are verified for **memory safety** (all slice
and string accesses in bounds, no permission violations) and **termination**,
and carry **functional specifications** proved against mathematical
abstractions defined in `spec.gobra`:

| Function | Functional guarantee |
|---|---|
| `HashStrBytes` | `hash == RKHash(seq(sep))` and `pow == PowRK(PrimeRK, len(sep))` |
| `HashStr` | `hash == RKHashStr(sep, 0, len(sep))` and `pow == PowRK(PrimeRK, len(sep))` |
| `HashStrRevBytes` | `hash == RKHashRev(seq(sep))` and `pow == PowRK(PrimeRK, len(sep))` |
| `HashStrRev` | `hash == RKHashStrRev(sep, 0, len(sep))` and `pow == PowRK(PrimeRK, len(sep))` |
| `IndexRabinKarpBytes` | first-occurrence contract in terms of `MatchesAt` (see below) |
| `IndexRabinKarp` | first-occurrence contract in terms of `StrMatchesAt` (see below) |

The abstractions (`spec.gobra`) are: `RKHashRange`/`RKHash` (Rabin-Karp hash of
a byte-sequence range), `RKHashRevRange`/`RKHashRev` (hash of the reversed
range), `RKHashStr`/`RKHashStrRev` (the analogues over string ranges), `PowRK`
(exponentiation), and the match predicates `MatchesAt`/`StrMatchesAt`.

Notably, the contracts capture:

- the exact Rabin-Karp hash equations for all four hash functions, including
  correctness of the exponentiation-by-squaring loop
  (`pow == PrimeRK^len(sep)`);
- for `IndexRabinKarpBytes`: if the result is `-1`, no window of `s` equals
  `sep` (as byte sequences); otherwise `sep` occurs in `s` at the returned
  index, and the values of `s` and `sep` are preserved. (That the returned
  index is the *first* occurrence is not proved for this function; see
  Limitations.)
- for `IndexRabinKarp` (strings): the full first-occurrence contract, stated
  with `StrMatchesAt`, which is the strongest property expressible in Gobra's
  abstract string model (see Limitations).

## Preconditions added

`IndexRabinKarpBytes` and `IndexRabinKarp` require `len(sep) <= len(s)`
(resp. `len(substr) <= len(s)`): both implementations index `s[i]` for
`i < len(sep)` unconditionally, so they are memory-unsafe without it. All
callers in the standard library (`bytes`, `strings`) guarantee it.

The byte-slice functions additionally take a ghost fractional permission
parameter `p` and preserve `acc(sep, p)` (and `acc(s, p)`), following the
usual Gobra convention for read-only slice arguments.

## Trusted assumptions

An honest inventory of everything assumed rather than proved
(`grep -rn trusted src/internal/bytealg`):

1. **`Equal` (spec.gobra).** Declared in `equal_native.go` and implemented in
   per-architecture assembly, which Gobra cannot verify. Its trusted contract
   states that `Equal(a, b)` returns exactly whether `a` and `b` have the same
   mathematical byte sequence.
2. **`lemmaBitFacts` (spec.gobra).** States `i>>1 == i/2` and `i&1 == i%2` for
   `i >= 0`. These are true facts of Go's semantics, but Gobra encodes the
   bitwise operators as uninterpreted functions without axioms, so they are
   unprovable inside the tool. They are needed for the
   exponentiation-by-squaring loops.
No `assume` statements are used anywhere. (No stub files for `unsafe` or
`internal/cpu` are needed: `offsets.go`, the only user of those packages, is
outside the verified scope.)

## Code changes (all semantics-preserving)

The implementation logic is unchanged. The full list of code-level edits:

1. The `unsafe.Offsetof` constant block and the `internal/cpu`/`unsafe`
   imports were moved, verbatim, from `bytealg.go` to the new file
   `offsets.go`: Gobra cannot parse `unsafe.Offsetof`, and these constants
   exist only as link-time symbols for the assembly files. `go build` output
   is unaffected (same package, same declarations).
2. Result parameters were named (`(rhash, rpow uint32)`, `(res int)`) so that
   postconditions can refer to them.
3. Everything else is comments: `//@`/`/*@ @*/` annotations (contracts, loop
   invariants, ghost lemma calls, proof asserts) and the `// +gobra` header.

## Limitations

- **Gobra's integer model.** Verification runs without `--overflow`; Go's
  fixed-size integers are treated as unbounded mathematical integers, so the
  `uint32` arithmetic in the specs is the exact, non-wrapping counterpart of
  the code's arithmetic. In particular the hash equalities are equalities of
  those unbounded values; wrap-around behaviour is not modelled. (On the flip
  side, this makes the rolling-hash reasoning exact rather than modular.)
- **Gobra's string model.** Strings are abstract identifiers with only length
  axioms: string slicing/indexing are essentially uninterpreted and there is
  no extensionality. A pointwise "the bytes match" property is therefore not
  expressible for `IndexRabinKarp`; `StrMatchesAt` instead captures exactly
  the test the code performs (window hash equal and string comparison
  succeeds). The byte-slice variant has the full pointwise contract.
- **Assembly.** `Equal` and the other assembly-backed functions of the package
  are not verified; `Equal`'s contract is trusted (see above).
- **Minimality for `IndexRabinKarpBytes`.** The "no earlier match"
  postcondition for the found-match case is maintained as a loop invariant and
  holds, but exhaling it at the early `return i - n` requires transporting a
  quantified fact over the heap-dependent `seq(s)`/`seq(sep)` terms into the
  postcondition state, which Silicon/Z3 does not manage within any practical
  assert timeout (the equivalent property for the string version, whose
  hash abstraction is heap-independent, verifies fine). The conjunct is
  therefore omitted from the byte version's contract; the complete
  "`-1` implies no match anywhere" direction and the "result is a match"
  direction are both verified.

## Verification setup

- Config: `src/gobra-mod.json` (module `std`, `only_files_with_header`,
  `require_triggers`, experimental friend clauses) plus the package-local
  `src/internal/bytealg/gobra.json`.
- CI: the `Gobra` workflow verifies the package with
  `viperproject/gobra-action` in config-file mode.
- Local runs: `java -jar gobra.jar --config src/internal/bytealg` with Z3
  4.8.7.
