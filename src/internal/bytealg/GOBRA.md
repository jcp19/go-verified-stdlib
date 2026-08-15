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
| `IndexRabinKarpBytes` | rolling-hash invariant and result bounds; the search-correctness conjuncts are deferred (see Limitations) |
| `IndexRabinKarp` | first-occurrence contract in terms of `StrMatchesAt` (see below) |

The abstractions (`spec.gobra`) are: `RKHashRange`/`RKHash` (Rabin-Karp hash of
a byte-sequence range), `RKHashRevRange`/`RKHashRev` (hash of the reversed
range), `RKHashStr`/`RKHashStrRev` (the analogues over string ranges), `PowRK`
(exponentiation), and the match predicates
`MatchesAtRange`/`MatchesAt`/`NoMatchBefore`/`StrMatchesAt`.

Notably, the contracts capture:

- the exact Rabin-Karp hash equations for all four hash functions, including
  correctness of the exponentiation-by-squaring loop
  (`pow == PrimeRK^len(sep)`);
- for `IndexRabinKarpBytes`: that the rolling hash is exactly
  `RKHashRange(seq(s), i-n, i)` at every iteration — the algorithm's core
  arithmetic, including the roll step that drops the outgoing byte and admits
  the incoming one — and that a non-`-1` result lies within
  `[0, len(s)-len(sep)]`. That the result *is* a match, and that it is the
  *first* one, are specified in `spec.gobra` but not currently discharged;
  see Limitations.
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
  succeeds). Note the irony that the string version, despite the weaker
  model, is the one with a complete first-occurrence contract: its abstraction
  is heap-independent, so its obligations are far cheaper than the byte
  version's `seq(s)`-based ones.
- **Assembly.** `Equal` and the other assembly-backed functions of the package
  are not verified; `Equal`'s contract is trusted (see above).
- **Search correctness for `IndexRabinKarpBytes` (deferred).** The contract
  currently proves the rolling-hash invariant and the result bounds, but not
  the three search-correctness conjuncts:

  ```go
  ensures res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
  ensures res != -1 ==> MatchesAt(seq(s), seq(sep), res)
  ensures res != -1 ==> NoMatchBefore(seq(s), seq(sep), res)
  ```

  All the machinery for them is present and verified in `spec.gobra` —
  `MatchesAtRange`, `MatchesAt`, `NoMatchBefore` and seven lemmas, each of
  which verifies in about 10s in isolation. What does not discharge is their
  use inside `IndexRabinKarpBytes`, which is a *performance* problem rather
  than a proof gap: every step involved is derivable, and the properties
  themselves hold (the assertion that blocked the loop is literally the loop
  invariant modulo linear arithmetic).

  The concrete blocker is the precondition of `lemmaMatchesAtFalseHash` on the
  hash-mismatch path, which maintains the `NoMatchBefore` invariant. It fails
  at both the default 30s and a 120s assert budget, and the budget cannot be
  raised much further: Gobra derives Z3's `rlimit` as
  `assert_timeout * 10000`, which overflows signed 32-bit above roughly 214s
  and aborts the whole package with an opaque Z3 parse error.

  Measured with Silicon's `--recordProofQueries` ([PR #966]), the cost is
  concentrated rather than diffuse: 94% of prover time is
  `FunctionalCorrectness` in a handful of very large queries, while branching
  (`ScopeManagement`, 2458 queries) accounts for 1 second in total and
  quantified permissions for ~5%. So the remaining work is about shrinking a
  few individual queries, not about path explosion or permissions.

  Three encoding changes made while investigating this are kept, because they
  are what would make resuming feasible — together they took the package from
  42m09s to 10m41s with the full spec, and the reduced spec now verifies in
  about 70s:

  1. `MatchesAt` is defined via the recursive `MatchesAtRange` instead of
     `q[j:j+len(pat)] == pat`. Sequence slicing encodes to nested
     `Seq_take`/`Seq_drop` terms, which dominated the profile.
  2. Contracts are stated in a single heap. `preserves acc(s, p)` gives
     callers value stability by framing, so `ensures seq(s) == old(seq(s))`
     was redundant, and cross-heap sequence equalities are expensive.
  3. Quantifier triggers contain no interpreted arithmetic — `ghost lo := i-n`
     makes `{&s[lo:i][k]}` a legal pattern where `{&s[i-n:i][k]}` is not.
     Gobra does not check trigger validity (and `--checkConsistency` conflicts
     with `--config`, which CI uses), so invalid triggers are otherwise
     silently accepted and handed to Z3 effectively untriggered.

  [PR #966]: https://github.com/viperproject/silicon/pull/966

## Verification setup

- Config: `src/gobra-mod.json` (module `std`, `only_files_with_header`,
  `require_triggers`, experimental friend clauses) plus the package-local
  `src/internal/bytealg/gobra.json`.
- CI: the `Gobra` workflow verifies the package with
  `viperproject/gobra-action` in config-file mode.
- Local runs: `java -jar gobra.jar --config <abs-path>/src/internal/bytealg`
  with Z3 4.8.7. The config path must be absolute; a relative one is resolved
  against the module root and fails with `File 'src/src/.' not found`.
  The package currently verifies in about 70s.
