---
name: gobra-specify-verify
description: Verify a pre-existing package that is not yet verified. To be used when a request to formally specify and verify a Go package occurs. This skill uses Gobra.
---

# Gobra Specify & Verify.

## Quick start
> !!!! BEFORE WE START !!!!
> NEVER, EVER, CHANGE THE ORIGINAL GO CODE OTHER THAN TO PERFORM SIMPLE TRANSORMATIONS (E.G., USE FOR LOOPS INSTEAD OF RANGE -- because they are not well supported in Gobra right now; INTRODUCE VARIABLES THAT STORE INTERMEDIATE RESULTS -- so that we can name these results in ghost code and introduce proof annotations in between, AND RENAME VARIABLES TO AVOID NAME CLASHES WITH GOBRA'S KEYWORDS).

1. At this point we know the package that we want to verify. This package contains .go files. Not all of them are relevant: those ending in `_test.go` are tests, and we will ignore them for now. As a first step, we will provide a trivial specification for every function and method:
```gobra
trusted
requires false
```
For interface methods, only add the precondition `requires false`, do not put the `trusted` annotation.
These contracts are not yet meaningful, but this allows us to detect issues in our setup.
Keep an inventory of every stub you introduce (here, and in step 2 for dependencies) in a `gobra-status.md` file at the root of the package under verification, with one row per member: the symbol, the step it has reached, and whether it is still trusted, stubbed, or assumed. This file is the honest picture of what is actually proven, and it is the thing that tells you when you are done. **NEVER REPORT A PACKAGE AS VERIFIED WHILE ANY ROW IS STILL TRUSTED, STUBBED, OR ASSUMED.** Say explicitly which members are still taken on faith and why.
2. We wait for Gobra to run on the package (either locally, or in the CI of the repository -- check the skill `setup-gobra` if Gobra was not set-up yet). It is likelly that, even at this stage, Gobra will find some errors. There are a few common ones:
- parsing errors and typing errors: Gobra has more keywords than Go. Has such, it may be the case that Go programs name variables with identifiers that are keywords in Gobra. A common one is `as` and `elem`, but there are more. Make sure this is not the case. Gobra has a stricter type-checker than Go, so it may be the case that you need to add some annoation to make Gobra happy.
- importing errors: Gobra may not be able to resolve the imports. This is because the import path is not properly in `gobra-mod.json` or `gobra.json` (check the `setup-gobra` skill for more info), or more likely, there is nothing you can import right now. There are two kinds of imports:
  - Imports to the Go standard library and third-party libraries. For these, you need stubs for the libraries that contain the definitions of the types, as well as the signatures of the functions and members that you use and specifications that you infer. If you include a type, you should include all of its fields, or else you should introduce an opaque type `PrivateFields`, which is a stub for all private and non-included fields. Including all of its fields sounds preferrable, otherwise you change the notion of equality for that type used in Gobra.
  - Imports to first-party libraries. For these, if they are not yet verified, you should introduce a spec.gobra file in the corresponding packages (with the annotation `// +gobra` so that Gobra can find it when the config option `only_files_with_header` is passed, where you add the stubs for the members of the method.)
For now, create the minimal stubs (if they do not exist yet and if the corresponding packages are not yet verified), containing the bare minimum to make Gobra verify the current package and produce a message saying that it found 0 errors. If you need to stub any functions, make their contracts both `trusted` and `requires false`.
3. At this point, we have a functioning workspace. It is time to add a last piece of scaffolding that we will slowly flesh out: For each declared interface type, you introduce two members:
  1. A `IMem()` (i.e., `pred IMem()`) predicate, which stands for the memory footprint of the resource.
  2. An `Inv()` ghost pure function, which returns a `bool` indicating if the invariant of the implementation holds. Its precondition is `requires IMem()`, and it must have a termination measure. Given that Go does not favour recursion, `decreases` is usually enough, but we can refine the termination measure later.
For each struct type `T`, introduce a predicate `MemRef` predicate, whose receiver type is `*T` and the body is `acc(t)` where `t` is the receiver, introduce a `Mem()` predicate whose receiver is `T`, and introduce an `Inv` function determining whether the invariant holds. The receiver of `Inv` is of type `T`. Also, introduce a `Deref` function that must have the following structure:
```gobra
ghost
requires t != nil
requires t.MemRef()
decreases
pure func (t *T) Deref() (res T) {
  return unfolding t.MemRef() in
    // you may have to perform additional unfoldings here in
    // order to obtain permission to all fields.
    *t
}
```
Finally, you may introduce none, one, or both of the following methods: `View` and `DeepView`. `View` converts a value
of type `T` into its mathematical counterpart that we use for reasoning. It is a shallow view, similar to the trait `View` in Verus (https://verus-lang.github.io/verus/verusdoc/vstd/view/trait.View.html). The idea is that this determines a permission-free object that we can use in specifications. For example, if we have an implementation of a linked list `LList` as follows and we want to specify the concat function, it is much nicer to do this at a mathematical level, where we do not need to carry permissions around to provide specifications:
```gobra
type LList struct {
    Val int
    Next *LList
}

pred (l LList) Mem() {
    acc(l.Next) &&
    (l.Next != nil ==> l.Next.MemRef() && l.Next.Deref().Mem())
}

pred (l *LList) MemRef() {
    acc(l)
}

requires l.Mem()
decreases l.Mem()
pure func (l LList) View() seq[int] {
  return ... // computes a mathematical sequence from the list. we can use this sequence to provide specifications that are free of permissions
}

// example:
// here, we have a clear separation between the footprint annotations (pres and posts containing resources `MemRef` and `Mem`), and
// functional specs (the last post). The nice thing about these specs is that, other than the seq. `Deref().View()`, the rest of the
// spec is entirely free of permissions. This allows us to do nice proofs of equational reasoning on the abstraction, and then easily
// extend it to the implementation.
requires l1.MemRef() && l1.Deref().Mem()
requires l2.MemRef() && l2.Deref().Mem()
ensures  res.MemRef() && res.Deref().Mem()
ensures  res.Deref().View() == old(l1.Deref().View()) + old(l2.Deref().View())
func (l1 *LList) Concat(l2) (res *LList) {
  ... // computes concat list in-place
}

```
`DeepView` is analogous to Verus's `DeepView` trait (https://verus-lang.github.io/verus/verusdoc/vstd/view/trait.DeepView.html), and computes
a deep abstraction. For a concrete example, if we have a list of lists, the shallow view may abstract the list as a sequence whose element type
are the lists, i.e., it did not abstract over the elements stored in the list, whereas the deep view would be a sequence of sequences. All new types you introduce should be `ghost`.

A word of caution on interfaces: because Go uses structural subtyping, you cannot enumerate the implementations of an interface -- any type with the right method set is one, anywhere in the codebase, including in packages you have never looked at. Every time you strengthen an interface's contract, you owe a re-verification of every implementation proof that already exists, and you may discover an implementation that the new contract simply does not fit. As such, specify interfaces *late* (after you have specified two or three implementations, so that you know what they actually have in common) and *weakly* (the weakest contract that every client can live with).

4. Verification should proceed in two major steps: On the first, you find the footprint annotations to make it possible to prove that every method is memory safe. You iterate until you can prove that. These specs may still be too weak to prove anything interesting about functional properties, but Gobra requires that you have this done before you target the rest. After you have a passing proof for memory footprints with no assumptions!!!, you start implementing the funciontal steps. The most important point here is that you identify a good abstraction for the data-structures and then state your functional properties in terms of that abstraction. (e.g., above, we abstracted linked lists as sequences.)

Two decisions govern the order in which you work through the package. First, *what* to specify: going top-down from the public API, write down in one sentence per exported member the property a client of this package is entitled to. Second, *in what order to prove it*: go bottom-up, from the leaves of the call graph, so that every contract you write is already backed by verified callees. Purely top-down means strengthening the same leaf contracts over and over; purely bottom-up means specifying facts that no client needs.

The contracts themselves come from, in order of priority: (1) the bare minimum that makes the safety proof possible; (2) the doc comments and the documentation of the package -- for the standard library in particular, the doc comment *is* the normative specification; (3) what the callers in this repository actually rely on. **NEVER INVENT BEHAVIOUR.** Where the documentation is ambiguous, specify the weaker contract and record the ambiguity. A contract that is too weak fails later at a call site, loudly; one that is too strong is a silent hole in everything you conclude about clients.

In the memory safety step you will often find that safety depends on a functional fact (an index is in bounds, a pointer is non-nil, a tag has a given value). Add the *weakest* fact that closes the proof, and put it where it belongs: invariants of the data structure go in `Inv`, obligations on the caller go in the precondition. Otherwise the memory safety step quietly turns into the functional step, and you lose the benefit of having separated them.

Decide explicitly whether termination is in scope and write the decision down. Gobra only forces `decreases` on pure and ghost functions, so unless you make total correctness a goal it will silently never happen -- the impure functions and their loops stay unproven. If it is in scope, do it as its own pass right after memory safety: loops need a measure, and for recursion over the heap the predicate instance is usually the right one (`decreases l.Mem()`).

When a member starts verifying, check that it does so for a reason: put an `assert false` at the end of its body and re-run. Gobra **must** report an error. If it does not, the proof is vacuous -- almost always a `requires false` from step 1 or step 2 that was never discharged, or a precondition whose conjuncts contradict each other -- and everything proved downstream of that member is worthless. This workflow starts every member at `requires false`, so vacuity is the failure mode it is most exposed to. The check costs one run and it is not optional.

Keep the package green as you go. Record the baseline (which members verify, and how long a run takes) before changing anything, and after changing a contract re-verify its *callers*, not only the member you touched -- verification is modular, so a strengthened precondition breaks every caller silently until the next full run. Never leave a previously-verified member broken while you move on to the next one.

**YOU ARE NOT ALLOWED TO CHANGE THE IMPLEMENTATION CODE, EVER**, except in a few controlled ways: you are allowed to store intermediate results in new variables; you are allowed to name return parameters; you are allowed to rewrite range loops into for loops; and, where Gobra cannot express a type declaration at all, you are allowed to rewrite that declaration (record it, with the limitation that forced it). **FURTHERMORE, YOU SHOULD NEVER INTRODUCE ASSUMPTIONS, IF POSSIBLE**. If you do, document them and list them in a report.

**EXTREMELY IMPORTANT**: You may find bugs: while specifying and proving programs, you may find that an implementation cannot be proved against the expected specification. When this happens, question yourself: is this intended behaviour (in which case you need to extend the spec), or is this unexpected? It may be a bug. If you think that is the case, make it very clear!!!

An important point about memory safety proofs is that, in Go, often there is a lot of sharing. For example, a data-structure may have a slice stored as a field that is a subslice of another. Consider the example where you parse a packet:
```go
type Packet struct {
  SrcIP   []byte
  DstIP   []byte
  Type    uint8
  Version uint8
}
```
It is entirely possible that a parse function, that takes `[]byte` stores a subslice of the input in `SrcIP` and `DstIP`. As such, the
`Mem` predicate of `Packet` should now own the slice, but rather, the slice ownership should be passed explicitely when the slice is read.
If there is a relation that is maintained between the values of the fields and the slice, this can be captured via pure ghost functions with
signature `pure func (p Packet, s []byte) bool` that **may** have access to `p.Mem()`, and the slice elements.

5. Once you have a verifying program, it is time to judge the quality of your code. You can do that in various steps:
  a. you get feedback through the `gobra-review-code` skill, which looks out for common Gobra mistakes. Note that some pieces of feedback may be irrelevant. Be strict about which pieces of feedback are worth implementing, especially those that have to do with how predicates are organized.
  b. in case there are tests for the current package, you can use them as a yardstick for the quality of your specifications. You should reproduce the tests in a separate .gobra file (if the original is called `x_test.go`, you create a new file `x_test.gobra`). These files should have the same package clause as the implementation files (rather than a test package). It should be marked for verification with `// +gobra`. The idea is that you create a copy of each testing method and implement it, removing references to the testing framework (e.g., deleting `testing.T` parameters) and replacing whatever calls to the testing framework by `assert` statements. You may need to add proof annotations, but you may never add assumptions to make the proofs go through. This will tell you whether your specs are too strict (e.g., a call in a test does not satisfy the precondition, even though it is perfectly benign), or whether the functional specs are too weak (for example, a postcondition is not strong enough to prove an assertion in the program). You are not allowed to change the testing code other than the transformations I mentioned, except for one transform: you often see tests structured as maps, and the tests iterate through the maps (whose values contain the inputs to a test and the expected result). In those cases, I prefer that you create a separate function for the tests, where each function has only one of the entries of the map. NOTE: for now, the transformation of test functions needs to be done by hand. In the future, I may be able to create a deterministic transformation. The outcome of this step should be a concise list of points to incorporate. You use this feedback and start refining the specifications (go back to step 4) until (1) tests can be verified, (2) you fail to do it after 6 iterations. If you need to create new lemmas to prove the correctness of the tests, feel free to make reusable versions of the lemmas available to clients. Two kinds of test deserve extra attention: those that exercise error paths pin down the *precondition boundary*, i.e., they tell you which inputs the contract must still accept; and fuzz targets or property-based tests translate into *quantified* harnesses, which are far stronger evidence about a contract than any number of point-wise unit tests.

### Important notes:
- Timeouts may happen. Always make sure you start running verification with a short `assertTimeout` (e.g., 3000 to 5000 ms) and increase it over time if need be. However, if there are such slow assertions, you should debug them early, rather than letting these performance problems compound. If available, the skill `gobra-debug-perf` helps localize causes of bad performance and the skill `gobra-improve-perf` provides suggestions to fix it.
- disclaimer: any of the previous guidelines may be broken if there is a good reason: for example, we may not need to find an abstraction for a type when no interesting properties are proven on it. You may introduce assumptions if there is absolutely no way to prove relevant properties without them and the assumed conditions cannot be proven by Gobra, even though you are super confident they hold.
- Please generate a log of the relevant steps you took and upload it so that I can see the steps that were taken by you.
