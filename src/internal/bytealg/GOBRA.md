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
| `IndexRabinKarpBytes` | first-occurrence contract in terms of `MatchesAt`/`NoMatchBefore` |
| `IndexRabinKarp` | first-occurrence contract in terms of `StrMatchesAt` (see below) |

The Gobra sources are split by role:

| File | Holds |
|---|---|
| `spec.gobra` | the ghost definitions the contracts are written against |
| `lemmas.gobra` | the lemmas that discharge proofs about those definitions |
| `assumptions.gobra` | the trusted members (see Trusted assumptions) |

The abstractions (`spec.gobra`) are: `RKHashRange`/`RKHash` (Rabin-Karp hash of
a byte-sequence range), `RKHashRevRange`/`RKHashRev` (hash of the reversed
range), `RKHashStr`/`RKHashStrRev` (the analogues over string ranges), `PowRK`
(exponentiation), and the match predicates
`MatchesAtRange`/`MatchesAt`/`NoMatchBefore`/`StrMatchesAt`.

Notably, the contracts capture:

- the exact Rabin-Karp hash equations for all four hash functions, including
  correctness of the exponentiation-by-squaring loop
  (`pow == PrimeRK^len(sep)`);
- for `IndexRabinKarpBytes`: the full first-occurrence contract. The rolling
  hash is exactly `RKHashRange(seq(s), i-n, i)` at every iteration — the
  algorithm's core arithmetic, including the roll step that drops the outgoing
  byte and admits the incoming one — and on top of that:

  ```go
  ensures res != -1 ==> 0 <= res && res <= len(s)-len(sep)
  ensures res != -1 ==> MatchesAt(seq(s), seq(sep), res)
  ensures res != -1 ==> NoMatchBefore(seq(s), seq(sep), res)
  ensures res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
  ```

  so a returned index is an occurrence with none before it, and `-1` means
  there is no occurrence at any of the positions the search could report.
  `LemmaNoMatchBeforePointwise` turns the recursive `NoMatchBefore` into the
  quantified form for clients.
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
(everything in `assumptions.gobra`; `grep -rn trusted src/internal/bytealg`
finds nothing outside it):

1. **`Equal` (assumptions.gobra).** Declared in `equal_native.go` and implemented in
   per-architecture assembly, which Gobra cannot verify. Its trusted contract
   states that `Equal(a, b)` returns exactly whether `a` and `b` have the same
   mathematical byte sequence.
2. **`lemmaBitFacts` (assumptions.gobra).** States `i>>1 == i/2` and `i&1 == i%2` for
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
   Plain comments added for verification are prefixed `(Gobra)` so they stay
   distinguishable from the upstream ones.

## Limitations

- **Gobra's integer model.** Verification runs without `--overflow`; Go's
  fixed-size integers are treated as unbounded mathematical integers, so the
  `uint32` arithmetic in the specs is the exact, non-wrapping counterpart of
  the code's arithmetic. In particular the hash equalities are equalities of
  those unbounded values; wrap-around behaviour is not modelled. (On the flip
  side, this makes the rolling-hash reasoning exact rather than modular.)
- **Gobra's string model.** Strings are abstract identifiers with only length
  axioms: string slicing/indexing are essentially uninterpreted and there is
  no extensionality. Nor can a string be turned into a `seq[byte]` in a *pure*
  context, which is what a specification function needs: the conversion has to
  go through `[]byte(s)`, which allocates, and Gobra rejects it inside a pure
  function with "expected pure expression". (It is accepted in impure ghost
  code, and `s[i]` indexing is fine in pure ghost code — the restriction is
  specifically the allocating conversion under purity.) A pointwise "the bytes
  match" property is therefore not
  expressible for `IndexRabinKarp`; `StrMatchesAt` instead captures exactly
  the test the code performs (window hash equal and string comparison
  succeeds). Both search functions now carry a first-occurrence contract, but
  they are not equally strong: `MatchesAt` says the bytes agree, whereas
  `StrMatchesAt` says the comparison the code performs succeeded. The weaker
  abstraction is also the cheap one — it is heap-independent, which is why
  `IndexRabinKarp` verifies in under a second and `IndexRabinKarpBytes`, whose
  obligations all run through `seq(s)`, takes minutes.
- **Assembly.** `Equal` and the other assembly-backed functions of the package
  are not verified; `Equal`'s contract is trusted (see above).
- **Cost of the `IndexRabinKarpBytes` contract.** The search-correctness
  conjuncts are what the package's verification time is spent on:
  `IndexRabinKarpBytes` alone is ~97% of it, and the package went from 54s
  without them to 6–13 minutes with them, with a large spread between runs of
  the same source. That is comfortable against the CI job's 1h timeout but
  leaves little appetite for adding more to this member.

## What made the search-correctness proof go through

This part of the contract was deferred once, on performance grounds — it hit
both the 30s assert budget and, in some shapes, an out-of-memory kill of Z3.
Six changes account for the difference; the first two were the decisive ones,
and all of them are about *what the loop body has to carry*, not about proof
steps that were missing.

1. **Never slice a sequence in the search loop.** The two window terms look
   interchangeable and are not: `seq(s[lo:i])` is a plain slice-to-seq term
   and is affordable, while `seq(s)[lo:i]` encodes to nested
   `Seq_take`/`Seq_drop`. Bridging the two with one ground
   `assert seq(s[lo:i]) == seq(s)[lo:i]` — which does verify, and looks like
   the cheapest possible bridge — is enough on its own to take the member
   from 32s to a crashed prover, *before* any of the new postconditions are
   added. The affordable bridge is pointwise, and it belongs in a lemma.
2. **A lemma's proof context is exactly its precondition.** The per-iteration
   reasoning is behind `lemmaMatchesAtWindow` and `lemmaNoMatchExtendWindow`,
   which take the window as two indices and hand back a `MatchesAt` fact.
   Inline in the loop, the same steps are attempted against everything the
   body has accumulated and exceed the budget — not for want of a fact, but
   for want of room. An `outline` block with the same contract works too and
   was the first thing that got the member to verify, but the lemma form was
   twice as fast and is reusable at both call sites.
3. **The address correspondence has to be a precondition of those lemmas.**
   `forall k :: {&s[lo:hi][k]} {seq(s)[lo+k]} &s[lo:hi][k] == &s[lo+k]` is
   what makes the permission for the reslice — and hence `seq(s[lo:hi])` —
   available at all. Establishing it inside the body is too late: the
   contract is checked first, and `seq(s[lo:hi])` in a contract without it
   fails with "Permission to `seq(s[lo:hi])` might not suffice".
4. **That quantifier needs the second trigger.** The pointwise reasoning
   mentions `seq(s)[lo+m]` and never `&s[lo:hi][m]`, so with the address
   pattern alone the fact is in the context and never fires. Arithmetic in an
   *index* is a legal pattern; only arithmetic in a slice *bound* is not.
5. **Prove the roll step before the window test, not after it.** With
   `lemmaRKHashRangeRoll` at the end of the body the invariant still holds,
   but the test does not know `h` to be the hash of the window it is
   comparing — which is exactly what refutes a match on the hash-mismatch
   path, the common one. This is what the earlier attempt was missing when it
   stalled on `lemmaMatchesAtFalseHash`'s precondition.
6. **Refute the two failure modes separately.** A hash mismatch is refuted by
   arithmetic over `RKHashRange` alone; only a hash collision has to look at
   the bytes. Handling both at once puts the window sequence into the context
   of every iteration.

Three earlier encoding choices are still load-bearing and were kept:

1. `MatchesAt` is defined via the recursive `MatchesAtRange` instead of
   `q[j:j+len(pat)] == pat`, for the reason in point 1 above.
2. Contracts and loop invariants are stated in a single heap; `old` does
   not appear anywhere in `bytealg.go`. `preserves acc(s, p)` gives callers
   value stability by framing, so `ensures seq(s) == old(seq(s))` was
   redundant. Inside a function the same trick works against loops: a loop
   invariant asking for only `acc(sep, p/2)` leaves the other half held
   outside, which frames the values across the loop. The same rule governs
   the lemma calls: they are passed `p/4` out of the `p/2` the loop holds, so
   the loop keeps a share and the rolling-hash facts survive the call.
3. Quantifier triggers contain no interpreted arithmetic in slice bounds —
   `ghost lo := i-n` makes `{&s[lo:i][k]}` a legal pattern where
   `{&s[i-n:i][k]}` is not. Gobra does not check trigger validity (and
   `--checkConsistency` conflicts with `--config`, which CI uses), so invalid
   triggers are otherwise silently accepted and handed to Z3 effectively
   untriggered.

Things that were measured and did not help: restating the `NoMatchBefore`
invariant against `lo` early in the body, where the context is small, made the
member ~1.8× slower and did not fix the failure it was aimed at;
`#backend[moreJoins(impure)]` on the member changed nothing (756s against
765s) and was reverted.

## Where the time actually goes

Profiled with Silicon's `--recordProofQueries` ([PR #966]) on the dumped Viper
program, restricted to `IndexRabinKarpBytes`, at the package's own 30s assert
budget. 2514 solver interactions, 491s of prover time:

| category | queries | time | share |
|---|---|---|---|
| `FunctionalCorrectness` | 166 | 406.7s | 82.7% |
| `Heap` | 339 | 82.6s | 16.8% |
| `PathInfeasibility` | 56 | 1.0s | 0.2% |
| `ScopeManagement` | 1856 | 0.5s | 0.1% |

The cost is concentrated to a degree worth stating plainly. **One source
position accounts for 321s — 65% of all prover time — in five queries**, the
worst of them 91s and 80s, and those two failed. It is the disjunctive
precondition of `lemmaNoMatchExtendWindow`:

```go
requires hash != RKHashRange(pat, 0, hi-lo) || seq(s[lo:hi]) != pat
```

Proving a disjunction gives Z3 no branch to work on: the call site has to
derive "hash differs or bytes differ" as one goal from the negated test. This
is also what makes the run time bimodal (roughly 330s or 750s for the same
source) — the query sometimes lands inside the budget and sometimes does not.

Note what the table rules out. Branching is not the problem: 1856
`ScopeManagement` queries cost half a second in total, and `PathInfeasibility`
one second. This is a handful of genuinely hard goals, not path explosion.

Underneath, an SMTScope trace of one such query shows why they are hard:
40 seconds of Z3 produced a **2.6 GB** trace, 1.27M instantiations, of which
668k are quantifier instantiations. `smt-scope redundancy` reports that most
are duplicates (79–97% for the hot ones) and flags Silicon's own
`qp.$FVF<Intbyte>-eq-outer` — the quantified-permission field-value-function
axiom — as a *multiplicative* pattern. The QP inverse-function axioms
(`Intbyte-invOfFct`, `-fctOfInv`) are among the most instantiated. In other
words the remaining cost is the standard byte-slice quantified-permission
problem: three footprints (`s`, `sep`, and the reslice `s[lo:i]`) live at
once. The documented cure — wrapping the permissions in a predicate that stays
folded except around the few statements that index the buffer — is a
package-wide change and has not been attempted here.

Two fixes suggested by this profile were tried and **both made things worse**,
so neither is in the tree:

- Splitting the disjunction into two lemmas (one per failure mode) selected by
  a `ghost if` on `h != hashsep`: 1960s and a new failure on the rolling-hash
  invariant.
- Replacing the invalid trigger `{seq(s)[lo+k]}` with the valid `{pat[k]}`:
  578s and a failure on the `NoMatchBefore` invariant. `pat[k]` is a very
  permissive pattern, and adding it appears to cost more than the dead trigger
  did. Interestingly, *deleting* the invalid pattern from the dumped Viper
  program without adding a replacement let standalone Silicon verify the
  member in 7m24s where the unstripped program failed at 8m22s — but
  `require_triggers` means that variant cannot be written in the source.

  [PR #966]: https://github.com/viperproject/silicon/pull/966

## Invalid triggers in this package

Gobra does not run Viper's consistency check, so it accepts triggers that
Silicon rejects and Z3 then ignores. Six of them exist in this package today:
three instances of `{seq(s)[lo+k]}` and three of the `{q[j+k]}` /
`{q[j:j+len(pat)][k]}` family. **Arithmetic inside a sequence index is not a
legal pattern**, not only arithmetic in a slice bound — `Seq_index(q, j+k)` is
rejected exactly like `Seq_take(Seq_drop(q, j), hi-j)`. `{&s[lo:hi][k]}` is
fine, because the `sadd` in the address encoding is not the same thing.

They are left in place because every attempt to change them measured worse
(above), and because each of those quantifiers has a second, valid pattern to
fall back on — except `lemmaRKHashRangeCongruence`'s, which is effectively
untriggered. To re-check after any change:

```bash
gobra <pkg files> --printVpr --noVerify
silicon --numberOfParallelVerifiers 1 --logLevel ERROR \
        --includeMethods 'NoSuchMethod' pkg/file.go.vpr   # trigger errors only, ~5s
```

## Verification setup

- Config: `src/gobra-mod.json` (module `std`, `only_files_with_header`,
  `require_triggers`, experimental friend clauses) plus the package-local
  `src/internal/bytealg/gobra.json`, which sets `assert_timeout` and
  `chop: 5`. Chopping splits the package into at most five Viper programs with
  smaller contexts: measured 331s / 378s / 728s against 738s / 756s / 765s
  without it. Given the spread that is suggestive rather than conclusive, but
  it never measured worse and costs nothing to carry.
- CI: the `Gobra` workflow verifies the package with
  `viperproject/gobra-action` in config-file mode.
- Local runs: `java -jar gobra.jar --config <abs-path>/src/internal/bytealg`
  with Z3 4.8.7. The config path must be absolute; a relative one is resolved
  against the module root and fails with `File 'src/src/.' not found`.
  The package verifies in 6–13 minutes, essentially all of it in
  `IndexRabinKarpBytes`; the spread is run-to-run variance on the same source,
  not a difference in what is checked.
- Isolating that member for a shorter loop is worth the setup:
  `gobra -i <pkg>/bytealg.go@<line> <pkg>/*.gobra -I src/. -m std
  --onlyFilesWithHeader --requireTriggers --experimentalFriendClauses
  --assertTimeout 30000` verifies only the chopper's slice for it. Note the
  slice is a *smaller* proof context than the whole package, so a member can
  verify in isolation and still time out in the package run — that happened
  here, and the fix was to shrink the context (see above), not to raise the
  budget.
