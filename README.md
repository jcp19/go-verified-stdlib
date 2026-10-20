# A verified Go standard library

This repository is an attempt to **formally specify and verify parts of the Go
standard library with [Gobra](https://github.com/viperproject/gobra)**, using an
LLM (Claude) to do the work with only a small amount of human supervision.

Gobra is a deductive verifier for Go, built on the
[Viper](https://www.pm.inf.ethz.ch/research/viper.html) infrastructure. Programs
are annotated with contracts, predicates and ghost code written in `//@` comments
and `.gobra` files; Gobra then proves, statically, that the implementation
satisfies them.

The interesting question here is not whether the standard library *can* be
verified — it is how much of that work can be delegated. Each verified package in
this repository was specified and proved by a model working from a package's
source and its tests, with a human setting the direction, reviewing the result,
and pushing back on weak or **non-idiomatic** specifications. The lessons from that review loop are
fed back into the [skills](#skills) below, so that the next package needs less
correction than the last.

The tree is a fork of [golang/go](https://github.com/golang/go) at
`go1.18.10`; everything outside the verified packages is upstream Go, unchanged
and under its original BSD-style [license](LICENSE). The verified packages are
upstream Go too — what a proof adds is annotations, not a rewrite, and the
handful of transformations that are permitted at all are spelled out under
[how the Go code may be changed](#how-the-go-code-may-be-changed).

## Status

| Package | Under verification | What is proved | Report |
| --- | --- | --- | --- |
| [`container/list`](src/container/list) | `list.go` — all 23 members | Memory safety, absence of panics, termination and **full functional correctness**, with **no assumptions and no trusted members**. The package's unit tests are reproduced as verified clients in [`list_test.gobra`](src/container/list/list_test.gobra). | [VERIFICATION.md](src/container/list/VERIFICATION.md) |
| [`internal/bytealg`](src/internal/bytealg) | `bytealg.go` — all 6 functions | Memory safety, termination, and functional specifications: the exact Rabin–Karp hash equations for the four hash functions, and full **first-occurrence** contracts for `IndexRabinKarpBytes` and `IndexRabinKarp`. Two trusted assumptions, both inventoried in the report. | [GOBRA.md](src/internal/bytealg/GOBRA.md) |
| [`sort`](src/sort) | — | Scaffolding only. The package is wired into the build and CI ([`gobra.json`](src/sort/gobra.json), [`spec.gobra`](src/sort/spec.gobra)), but no member carries a specification yet. | — |

Each verified package ships a report next to the code that states, in prose,
what was proved, what was assumed, which changes were made to the Go source, and
what defeated the tool.


## Gobra version

CI runs [`viperproject/gobra-action@main`](https://github.com/viperproject/gobra-action),
which verifies with the `ghcr.io/viperproject/gobra:latest` image. **No version
is pinned today**: each run uses whatever Gobra build — and whatever bundled Z3 —
that image currently ships.

Running a package locally against a Gobra build of your own — here,
`container/list`:

```sh
java -jar gobra.jar --config <absolute-path-to-repo>/src/container/list
```


## Project outline

Gobra is configured through JSON files rather than command-line flags, so a
package is brought under verification by adding configuration and specification
files next to it — never by restructuring the tree.

```
.github/workflows/gobra.yml     CI: one verification step per package
.claude/skills/                 the skills that drive the work (see below)
src/
  gobra-mod.json                module-wide Gobra configuration
  gobra/                        Gobra-only sources: stubs and specifications for
                                dependencies that are not verified themselves,
                                plus shared ghost-code utility packages
  <pkg>/
    gobra.json                  package-level Gobra configuration
    spec.gobra                  the ghost definitions the contracts speak about
    lemmas.gobra                the lemmas that discharge proofs about them
    assumptions.gobra           the trusted members, if any — the whole TCB
    <pkg>_test.gobra            the package's tests, as verified clients
    <pkg>.go                    upstream Go + the proof, in //@ annotations
    VERIFICATION.md             what was proved, assumed, and learned
```

The module-wide configuration ([`src/gobra-mod.json`](src/gobra-mod.json)) sets
the conventions the whole project follows:

- **`only_files_with_header`** — a `.go` file is verified only if it carries a
  `// +gobra` header, so bringing a file under verification is an explicit,
  reviewable act, and the rest of the standard library is left alone.
- **`includes: [".", "gobra/"]`** — imports resolve against `src/gobra/` as well
  as the module root, which is how stubs shadow unverifiable dependencies.
- **`require_triggers`** — every quantifier must carry an explicit trigger.
  Trigger discipline is the single biggest lever on whether a proof terminates.

One further rule holds across every package: **tests are the yardstick for the
specifications.** A package's unit tests are translated into `.gobra` clients
whose assertions must be *proved*, not run. No `assume` is added to make a test go through.

## How the Go code may be changed

**It is still the original implementation.** Verifying an algorithm you have
quietly rewritten proves nothing about the standard library, so the rule here is
that the Go source is *not* adapted to suit the verifier. The algorithm, the
control flow, the data structures and the observable behaviour of every verified
package are upstream Go's, unchanged.

What is added is proof, and proof is invisible to the Go toolchain. Contracts,
loop invariants, ghost fields, ghost parameters, lemma calls and proof asserts
all live inside `//@` line comments and `/*@ … @*/` blocks, which the Go
compiler sees as comments and Gobra sees as code. So a method that reads

```go
// @ preserves l.Mem()
// @ ensures   l.Es() == old(l.Es()) ++ seq[*Element]{ret}
func (l *List) PushBack(v any) (ret *Element)
```

still compiles as the upstream `func (l *List) PushBack(v any) *Element` — even
the ghost parameters that some methods take are written inside a comment block,
so the compiled package's API is byte-for-byte the one Go ships.

Beyond annotations, only these transformations are permitted, and each is
semantics-preserving:

| Transformation | Why it is needed | Example |
| --- | --- | --- |
| **Rename an identifier that clashes with a Gobra keyword** | `len`, `old`, `new`, `atomic`, `pred` and friends are keywords in the specification language and cannot name a variable or field. | `container/list`'s private field `len` → `length` |
| **Name result parameters** | A postcondition has to be able to refer to what the function returns. | `func ... (uint32, uint32)` → `func ... (rhash, rpow uint32)` |
| **Introduce a local for an intermediate result** | Ghost code and proof annotations can only be placed *between* statements, so a value that a proof step has to name must first be bound to a name. | `return l.root.next` → `res := l.root.next; return res` |
| **Use an indexed `for` loop instead of `range`** | `range` is not well supported by Gobra today. | (none of the currently verified packages needed it) |
| **Move a declaration Gobra cannot parse into a separate file** | Kept verbatim, in the same package, so the build output is identical. | `internal/bytealg`'s `unsafe.Offsetof` constants → `offsets.go` |

Everything else is off limits. In particular: no loop is restructured, no bound
is tightened, no case is dropped because it is hard to prove, and no behaviour
is weakened to fit a specification. Where the
verifier could not be satisfied, the report says so — as a limitation, a trusted
assumption, or a stub — rather than the code being bent to make the failure go
away.

Three checks keep this honest, and each package's report records them:

- **`go build`, `go vet` and `go test` still pass** on the transformed package,
  against the package's real, untranslated test suite.
- **The files stay `gofmt`-clean.** gofmt rewrites `//@` to `// @` and Gobra
  accepts both spellings, so the annotated sources pass both tools.
- **Stripping the annotations recovers upstream.** The remaining diff against
  `go1.18.10` is exactly the table above — renames, named results and
  intermediate locals — and each report lists it line by line, so a reviewer can
  confirm that what was verified is what Go ships.

Plain (non-annotation) comments added during verification are prefixed
`(Gobra)`, so upstream's comments stay distinguishable from ours.

## Skills

The project is driven through a set of [Claude Code
skills](https://docs.claude.com/en/docs/claude-code/skills) in
[`.claude/skills/`](.claude/skills). They are where the human supervision
accumulates: every review comment that had to be made twice became a rule in one
of these files, so the knowledge is reusable rather than re-explained per
session.

| Skill | What it does |
| --- | --- |
| [`setup-gobra`](.claude/skills/setup-gobra) | Wires Gobra into a repository and into a package: the CI workflow, `gobra-mod.json`, the `gobra/` directory, the per-package `gobra.json` and `spec.gobra`. |
| [`gobra-specify-verify`](.claude/skills/gobra-specify-verify) | The main loop: take an unverified package to a verified one — trivial contracts first, then memory safety, termination, and functional correctness, with the package's own tests as the yardstick. Includes the process rules on vacuity checks, termination measures and regression runs. |
| [`gobra-review-code`](.claude/skills/gobra-review-code) | Reviews Gobra code for the conventions a verifier will never complain about: annotation order, `.go`/`.gobra` file separation, purity, permission strength (read fractions vs. `write`), `old` expressions, unfolding in contracts, and interface specifications. |
| [`gobra-debug-perf`](.claude/skills/gobra-debug-perf) | Diagnoses a slow or diverging verification — which member, which query, which quantifier — before anything is changed. Ships scripts for ranking members by cost and summarising SMT queries. |
| [`gobra-improve-perf`](.claude/skills/gobra-improve-perf) | Acts on that diagnosis: outline statements, opaque functions, predicates, the chopper, `moreJoins`, `exhaleMode`, quantified permissions and triggers — validating each fix and reverting the ones that do not help. |

## Why Go 1.18

This work targets the `go1.18` release branch because **Gobra does not support
generics yet**. Go 1.18 is the release that introduced them, so it is the last
point at which the standard library is still generics-free in practice: the
packages of interest here are
written against interfaces and concrete types, and can be specified with the
constructs Gobra has today.

That is a temporary position, not a design decision. Verifying anything from a
current Go release means Gobra must be extended to support type parameters, and the
specification language must gain a way to talk about them (contracts over
constrained type parameters, and instantiation of predicates and ghost
functions). Figuring out how to move this project past Go 1.18 is future work.

## Upstream Go

For the Go language itself, see the upstream project:
[go.googlesource.com/go](https://go.googlesource.com/go), mirrored at
[github.com/golang/go](https://github.com/golang/go). Bug reports and proposals
about Go belong there, not here. Unless otherwise noted, the Go source files in
this repository are distributed under the BSD-style license found in the
[LICENSE](LICENSE) file.
