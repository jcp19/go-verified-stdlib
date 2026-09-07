# Toolchain notes

The CI workflow (`.github/workflows/gobra.yml`) runs `viperproject/gobra-action`,
which verifies with the `ghcr.io/viperproject/gobra:latest` image. The image
bakes in both the Gobra build and the Z3 binary, so the packages here are
verified against whatever Z3 that image ships.

**`sort` and `container/list` verify on Z3 4.16.0**, and did not before;
`container/list` had to be re-encoded to get there. **`internal/bytealg` does
not verify reliably**: of four repeat runs on identical source, three passed and
one failed, and its one expensive member, `IndexRabinKarpBytes`, sits on its
assert budget. Its
proofs have been reworked twice (see `../internal/bytealg/GOBRA.md`) and the
member is roughly three times cheaper than it was, but not cheap enough to be
stable. Z3 4.13.0 still verifies everything here unchanged, so the underlying
regression is the one described below, and the durable fix is upstream.

The rest of this file records why these packages are sensitive to the Z3
version at all. Anyone changing their proofs should know which cliffs are
nearby.

## The Z3 4.14 regression

Gobra commit `9279c48` raised Z3 from 4.8.7 to 4.16.0, and `4587196` updated
Viper to 2026.8. After those two commits the verified packages, as they then
stood, no longer verified.

The Viper update is not the cause. Every measurement below uses the *same*
Gobra build — `4587196`, i.e. with Viper 2026.8 and the new quantified-permission
desugaring — and varies only the Z3 binary.

Bisecting `container/list`'s `*List.move`, the most expensive method in the
package:

| Z3 | `*List.move` |
|---|---|
| 4.8.7 | 64 s, 0 errors |
| 4.11.2 | 81 s, 0 errors |
| 4.12.1 | 81 s, 0 errors |
| 4.13.0 | 74 s, 0 errors |
| 4.13.4 | 82 s, 0 errors |
| **4.14.0** | **diverges (>300 s)** |
| 4.14.1 | diverges (>300 s) |
| 4.15.0 | diverges (>300 s) |
| 4.16.0 | diverges (>300 s) |

The break is between Z3 4.13.4 and 4.14.0.

**Z3 4.13.0 verifies everything in this repository**, on the same Gobra build
and with Silicon's shipped options — no proof changes and no configuration
changes needed:

| Package | Z3 4.13.0 | Z3 4.16.0, as this repo stood | Z3 4.16.0, now |
|---|---|---|---|
| `sort` | 0 errors, 8 s | 0 errors, 7 s | **0 errors, 8 s** |
| `container/list` | 0 errors, 326 s | aborted: prover crash | **0 errors, 122-217 s** |
| `internal/bytealg` | 0 errors, 1171 s | 1 error every run, 889-1163 s | **0 errors in 3 of 4 runs, 601-1105 s** |

`container/list` was re-encoded to verify on Z3 4.16: it moved its ownership
from indices to a set, which removed a matching loop; see
`../container/list/VERIFICATION.md`. It is now solidly green.

`internal/bytealg` was reworked too -- `opaque` abstractions, non-linear
arithmetic moved to `arith/` so the package can run with `--disableNL`, and its
window lemmas rephrased to keep `seq(s)` out of a fragmented heap. Five of its
six members became cheap enough to be immune (four of the five chops finish in
under half a minute), and `IndexRabinKarpBytes` went from failing on every run
to failing on one of four. That is an improvement, not a fix, and CI will be
flaky on this package until the regression below is addressed upstream.
It was always the narrower of the two: it already failed on Z3 4.13.4, one patch
release before `container/list` used to break.

On the whole package the divergence is not merely slow. `move` and `remove`
grow a single Z3 process past 7.5 GB until the kernel kills it, and Silicon
reports

```
viper.silicon.reporting.ProverInteractionFailed: Interaction with prover
yielded null. This might indicate that the prover crashed.
```

Note that Silicon converts `--assertTimeout` into a `:rlimit` rather than a
`:timeout` (`proverEnableTimeBounds` is `false` by default, and
`z3ResourcesPerMillisecond` is 10000). An rlimit budget bounds *work*, not
*memory*, which is why a runaway query is not cut off before it exhausts RAM.

That conversion also overflows: `assertTimeout * z3ResourcesPerMillisecond` is
computed in a signed 32-bit int, so any `assert_timeout` above roughly 214748 ms
produces a negative rlimit and kills the run outright with

```
(error "line ... Expected values for parameter rlimit is an unsigned integer.
        It was given argument '-1294967296'")
```

which caps the option at about three and a half minutes.

Members that do not diverge outright instead spend long enough on individual
queries to exhaust their assert budget, and the resulting `unknown` surfaces as
an ordinary verification error. That is what produces reports such as

```
list_test.gobra:178:33 Inhale might fail.
                       Permission to {e1, e4, e3} might not suffice.
```

which is a budget symptom, not a hole in the proof: the same obligation is
discharged in seconds on Z3 4.13.4.

## Root cause: `smt.arith.solver`

Silicon's `z3config.smt2` pins the *legacy* arithmetic solver:

```
; Tested with Z3 4.8.7 and 4.12.1
...
(set-option :smt.arith.solver 2)
```

Solver 2 is what regressed in Z3 ≥ 4.14; 6 is Z3's modern default. Overriding
just that one option, with Z3 4.16.0 and everything else unchanged, restores
`container/list`:

| Z3 4.16.0 | `*List.move` | `container/list` |
|---|---|---|
| `smt.arith.solver 2` (as shipped) | diverges (>480 s) | aborted by prover crash |
| `smt.arith.solver=6` | 90 s, 0 errors | 416 s, **0 errors** |

The option cannot be set from this repository. Silicon sends its configuration
as `(set-option ...)` lines after start-up, so Z3 command-line parameters do not
override it; Silicon exposes `--proverConfigArgs`, but Gobra builds Silicon's
option vector itself (`ViperBackends.SiliconBasedBackend.buildOptions`) and has
no passthrough for it. The fix belongs upstream — in Silicon's `z3config.smt2`,
or in Gobra's pinned `Z3_VERSION` (`workflow-container/Dockerfile`), for which
4.13.0 is the newest release that verifies everything here.

### The setting is not a free win

`internal/bytealg` wants the opposite. Its Rabin-Karp proofs are nonlinear
(`pow * PowRK(sq, i) == PowRK(PrimeRK, len(sep))`), and solver 6 is weaker than
solver 2 on nonlinear multiplication. On Z3 4.16.0 with `smt.arith.solver=6`
`container/list` is green but `bytealg` failed two loop invariants it discharged
under solver 2:

```
bytealg.go:46:12  Loop invariant might not be preserved.
bytealg.go:108:12 Loop invariant might not be preserved.
                  pow*PowRK(sq, i) == PowRK(PrimeRK, len(sep)) might not hold
```

So `smt.arith.solver` was a trade-off between the two packages here, not a
setting that could simply be flipped. `IndexRabinKarpBytes` is also the single
most expensive member in the repository (~19 min of the ~20 min package run,
98.6% of its total), which left it with little margin: which of its obligations
fell over changed with the Z3 build. Across the configurations measured it
failed at three different places —

| Configuration | `internal/bytealg` |
|---|---|
| 4.8.7, solver 2 | 0 errors |
| 4.13.0, solver 2 | 0 errors |
| 4.13.4, solver 2 | `bytealg.go:155` postcondition `res != -1 ==> MatchesAt(...)` |
| 4.16.0, solver 2 | `bytealg.go:212` precondition of `lemmaNoMatchExtendWindow` |
| 4.16.0, solver 6 | `bytealg.go:46` and `:108` loop invariants (nonlinear) |

— which is the signature of a member sitting on its budget rather than of a
proof that is actually wrong.

Raising `assert_timeout` did not fix it either, and neither did anything else
reachable from configuration; `../internal/bytealg/GOBRA.md` records the sweep,
including that four identical runs reported two different failures, so the
package was unstable rather than merely slow.

What fixed it was proof engineering rather than configuration, and it sidesteps
`smt.arith.solver` entirely: `internal/bytealg` no longer asks the solver to do
non-linear arithmetic at all. Its recursive abstractions are `opaque`, and its
non-linear facts come from `arith/`, a small package verified normally and
imported; the package itself runs with `--disableNL`. That took four of its five
chops from ~20 minutes to 24 seconds and made the expensive member verify.

Per-member solver selection would still be useful — `smt.arith.solver=6` breaks
`bytealg` in `HashStrBytes`/`HashStrRevBytes`, whose invariants are non-linear,
but not in `IndexRabinKarpBytes`, which is the slow member. Gobra has the syntax
(`#backend[proverConfigArgs(...)]`) and Silicon reads it, but Gobra stringifies
multi-token annotation values as a Scala collection, so the option never arrives
intact. That is a small upstream fix, though no longer a blocking one here.

## Reproducing locally

The CI image cannot always be pulled (its blobs live on
`pkg-containers.githubusercontent.com`), but Gobra builds from source:

```sh
git clone https://github.com/viperproject/gobra
cd gobra && git submodule update --init --recursive
sbt assembly            # -> target/scala-2.13/gobra.jar
```

Then, from the repository root, with `Z3_EXE` pointing at the Z3 you want:

```sh
Z3_EXE=/path/to/z3 java -Xss1g -Xmx4g \
  -jar /path/to/gobra.jar --config "$PWD/src/container/list"
```

`--config` needs an **absolute** path: relative paths are resolved twice, once
against the directory holding `gobra-mod.json` and once more, and the run fails
with `File 'src/src/.' not found`. The action always passes an absolute path,
which is why this only bites locally.

To verify a single member, name its line with the chopper — the whole package
takes minutes, one member takes seconds:

```sh
java -jar gobra.jar -i src/container/list/list.go@287 \
  src/container/list/spec.gobra src/container/list/lemmas.gobra \
  src/container/list/list_test.gobra \
  -I src src/gobra -m std --onlyFilesWithHeader --requireTriggers \
  --experimentalFriendClauses --assertTimeout 20000
```

### A/B-ing a Z3 option

Since Silicon's `(set-option ...)` lines win over Z3's command line, testing a
different setting means editing the lines in flight. A small proxy on `Z3_EXE`
does that without rebuilding Silicon:

```python
#!/usr/bin/env python3
import os, re, subprocess, sys
real = os.environ["REAL_Z3"]
pairs = [kv.split("=", 1) for kv in os.environ.get("Z3_SUBS", "").split(";") if kv]
p = subprocess.Popen([real] + sys.argv[1:], stdin=subprocess.PIPE)
for raw in sys.stdin.buffer:
    s = raw.decode("utf-8", "replace")
    for k, v in pairs:
        s = re.sub(r"\(set-option :" + re.escape(k) + r"\s+[^)]*\)",
                   "(set-option :%s %s)" % (k, v), s)
    p.stdin.write(s.encode()); p.stdin.flush()
p.stdin.close(); sys.exit(p.wait())
```

```sh
REAL_Z3=/usr/local/bin/z3 Z3_SUBS="smt.arith.solver=6" Z3_EXE=./z3proxy.py \
  java -jar gobra.jar --config "$PWD/src/container/list"
```

## What was ruled out

This is about `container/list` as it stood before its re-encoding. None of
Gobra's own knobs rescued `*List.move` on Z3 4.16.0 — each still hit a
420 s cap where the member took 34 s on Z3 4.8.7:

- `--moreJoins all`
- `--disableNL`
- `--conditionalizePermissions`
- `--mceMode=off`

Neither did proof engineering at the obvious spot: removing `move`'s
pairwise-distinctness assertion, whose two-variable multi-pattern
`{es0[i1], es0[i2]}` was the natural suspect for a quantifier blow-up, changed
nothing. What did work was changing the encoding rather than the knobs, in both
packages: `container/list` moved its ownership off the index quantifiers that
were looping, and `internal/bytealg` took the non-linear arithmetic out of the
solver's hands. Note that `--disableNL` appears in this list as something that
did *not* help `container/list` and is nevertheless what `internal/bytealg`
now runs with — it is a flag that pays off only once a package's non-linear
facts are supplied as lemmas, and costs nothing in a package that has none.
