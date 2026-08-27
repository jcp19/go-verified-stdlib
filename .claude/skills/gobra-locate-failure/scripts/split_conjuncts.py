#!/usr/bin/env python3
"""Decide whether a failing Gobra assertion can be decomposed, and if so split
it into its top-level conjuncts.

Usage:
    split_conjuncts.py "0 <= i && i <= len(s) && h == RKHash(seq(s))"
    split_conjuncts.py --file src/internal/bytealg/bytealg.go --line 191
    split_conjuncts.py --file x.gobra --line 33 --prefix "//@ assert "

Decomposing a failing assertion is the highest-yield proof action (SKILL.md
§3.1), but only when the expression's WEAKEST top-level operator is `&&`.
Gobra follows Viper's precedence, so `==>` binds more weakly than `||`, which
binds more weakly than `&&`:

    A ==> B && C        is   A ==> (B && C)
    forall i :: P && Q  is   forall i :: (P && Q)     -- the body extends right

Splitting the `&&` of either produces assertions the original does not imply,
which is how a "decomposition" ends up reporting a failure that was never
there. This script finds the weakest top-level operator instead of assuming
one, and names the action to use when that operator is not `&&`.

Precedence is not the only trap. Between impure assertions Viper's `&&` is a
SEPARATING conjunction, so splitting one `assert` into several is not always
meaning-preserving: `acc(x.f, 1/2) && acc(x.f, 1/2)` needs a whole permission,
while two asserts of `acc(x.f, 1/2)` each pass while holding only half. The
script flags conjuncts it can see are impure. Splitting a contract CLAUSE is
always safe -- several clauses mean their conjunction.

It is a scanner, not a parser: it tracks brackets and string literals, and it
knows the operators, but it does not type-check. Sanity-check the output.
"""

import argparse
import re
import sys

# Comment prefixes Gobra annotations use in .go files, longest first.
ANNOT_RE = re.compile(r"^\s*(//\s?@)\s*")
# Clause keywords that may precede the assertion on the line.
KEYWORD_RE = re.compile(
    r"^\s*(assert|assume|refute|inhale|exhale|requires|ensures|preserves|invariant)\b\s*"
)
# Constructs whose body extends as far right as possible.
TRAILING_BODY = {
    "forall": ("quantifier", "3.6"),
    "exists": ("quantifier", "3.6"),
    "let": ("let-binding", "3.1"),
    "unfolding": ("unfolding", "3.8"),
    "asserting": ("asserting", "3.1"),
}

OPEN, CLOSE = "([{", ")]}"
# Impure (resource) assertions the scanner can recognize. A bare predicate
# instance -- `l.Mem()` -- is also impure but is not syntactically distinct from
# a boolean call, so it cannot be detected here.
IMPURE_RE = re.compile(r"\bacc\s*\(|--\*")


def scan(expr):
    """Yield (index, token) for operators and separators found at bracket depth 0.

    Skips string, rune and raw-string literals. Multi-character operators are
    matched before their prefixes so that `==>` is never read as `==`, `&&`
    never as `&`, and `--*` never as `-`.
    """
    i, depth, n = 0, 0, len(expr)
    while i < n:
        c = expr[i]
        if c in "\"'`":
            quote, i = c, i + 1
            while i < n:
                if expr[i] == "\\" and quote != "`":
                    i += 2
                    continue
                if expr[i] == quote:
                    break
                i += 1
            i += 1
            continue
        if c in OPEN:
            depth += 1
            i += 1
            continue
        if c in CLOSE:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            for tok in ("==>", "--*", "<==>", "::", ":=", "==", "!=", "<=", ">=", "&&", "||"):
                if expr.startswith(tok, i):
                    yield i, tok
                    i += len(tok)
                    break
            else:
                if c in "?:":
                    yield i, c
                i += 1
            continue
        i += 1


def strip_outer_parens(expr):
    expr = expr.strip()
    while expr.startswith("(") and expr.endswith(")"):
        depth = 0
        for j, c in enumerate(expr):
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth -= 1
                if depth == 0 and j != len(expr) - 1:
                    return expr
        expr = expr[1:-1].strip()
    return expr


def leading_construct(expr):
    m = re.match(r"([A-Za-z_]\w*)\b", expr)
    if m and m.group(1) in TRAILING_BODY:
        return m.group(1)
    return None


def analyse(expr):
    """Return (kind, section, parts) for an expression.

    `parts` holds the operands of the weakest top-level operator, if any.
    """
    expr = strip_outer_parens(expr)
    if not expr:
        return "empty", "-", []

    kw = leading_construct(expr)
    if kw:
        kind, section = TRAILING_BODY[kw]
        return kind, section, []

    ops = list(scan(expr))

    def positions(*toks):
        return [i for i, t in ops if t in toks]

    if positions("?"):
        i = positions("?")[0]
        # The matching `:` is the first top-level `:` after the `?` that is not
        # part of `::` or `:=` (scan already emits those as their own tokens).
        colons = [j for j, t in ops if t == ":" and j > i]
        if colons:
            j = colons[0]
            return "ternary", "3.9", [expr[:i].strip(), expr[i + 1:j].strip(), expr[j + 1:].strip()]
        return "ternary", "3.9", []

    for toks, kind, section in (
        (("==>",), "implication", "3.5"),
        (("<==>",), "equivalence", "3.9"),
        (("--*",), "magic wand", "3.11"),
        (("||",), "disjunction", "3.9"),
        (("&&",), "conjunction", "3.1"),
    ):
        idx = positions(*toks)
        if idx:
            parts, prev = [], 0
            width = len(toks[0])
            for i in idx:
                parts.append(expr[prev:i].strip())
                prev = i + width
            parts.append(expr[prev:].strip())
            if kind in ("implication", "magic wand", "equivalence"):
                # Right-associative: everything after the first operator is the
                # consequent, so re-join all but the first part.
                parts = [parts[0], toks[0].join(parts[1:]).strip()] if len(parts) > 2 else parts
            return kind, section, parts

    return "atomic", "3.3", []


ADVICE = {
    "conjunction": "Splittable. Assert each conjunct on its own line; the first that fails is your real goal.",
    "implication": "Do NOT split the `&&` inside this. Introduce the hypothesis (§3.5):\n"
                   "    ghost if <antecedent> { assert <consequent> }\n"
                   "  then re-run this script on the consequent.",
    "equivalence": "Prove the two directions separately (§3.9).",
    "disjunction": "Not a conjunction. Case-split (§3.9), or find which disjunct you expect to hold and assert it alone.",
    "ternary":     "The weakest operator is `? :`. Case-split on the condition (§3.9):\n"
                   "    ghost if <cond> { assert <then> } else { assert <else> }",
    "quantifier":  "The body extends as far right as possible, so any `&&` you see belongs to the body.\n"
                   "  Extract a ghost lemma whose parameters are the bound variables (§3.6), or\n"
                   "  instantiate at a witness index to separate a missing fact from a trigger problem (§3.7).",
    "let-binding": "The body extends right. Decompose the body, keeping the binding in scope.",
    "unfolding":   "The body extends right. `unfold` the predicate as a statement first (§3.8), then decompose.",
    "asserting":   "The body extends right. Decompose the asserted side condition and the body separately.",
    "magic wand":  "A wand, not a conjunction (§3.11).",
    "atomic":      "Nothing left to decompose. This is your minimal failing goal — walk it up (§3.3).",
    "empty":       "Nothing to analyse.",
}


def read_from_file(path, lineno):
    """Read the clause starting at `lineno`, continuing while brackets are open."""
    try:
        with open(path) as f:
            lines = f.readlines()
    except OSError as e:
        sys.exit(f"could not read {path}: {e}")
    if not 1 <= lineno <= len(lines):
        sys.exit(f"{path} has {len(lines)} lines; no line {lineno}")

    def clean(s):
        return ANNOT_RE.sub("", s).strip()

    text = KEYWORD_RE.sub("", clean(lines[lineno - 1]))
    i = lineno
    while i < len(lines):
        depth = sum(1 for _c in text if _c in OPEN) - sum(1 for _c in text if _c in CLOSE)
        if depth <= 0 and not text.rstrip().endswith(("&&", "||", "==>", "+", ",")):
            break
        nxt = clean(lines[i])
        if not nxt:
            break
        text = text + " " + nxt
        i += 1
    return text.strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("expr", nargs="?", help="the assertion to analyse")
    ap.add_argument("--file", help="read the assertion from a source file instead")
    ap.add_argument("--line", type=int, help="1-based line number of the clause in --file")
    ap.add_argument("--prefix", default="//@ assert ", help='prefix for emitted lines (default "//@ assert ")')
    args = ap.parse_args()

    if args.file:
        if not args.line:
            sys.exit("--file requires --line")
        expr = read_from_file(args.file, args.line)
        print(f"{args.file}:{args.line}")
    elif args.expr:
        expr = args.expr
    else:
        sys.exit("give an expression, or --file and --line")

    kind, section, parts = analyse(expr)
    print(f"\n  {strip_outer_parens(expr)}\n")
    print(f"top-level operator: {kind}   ->  SKILL.md §{section}")
    print(f"{ADVICE[kind]}\n")

    if kind == "conjunction":
        for p in parts:
            print(f"{args.prefix}{p}")
        impure = [p for p in parts if IMPURE_RE.search(p)]
        if impure and "assert" in args.prefix:
            print("\nWARNING: separating conjunction. These conjuncts are impure:")
            for p in impure:
                print(f"  {p}")
            print("  Between impure assertions `&&` adds permissions up, so N asserts are a\n"
                  "  WEAKER check than the conjunction whenever one location is covered twice\n"
                  "  (same field, overlapping quantified ranges, two instances of one predicate).\n"
                  "  Safe for disjoint resources. Splitting a contract CLAUSE is always safe --\n"
                  '  re-run with --prefix "//@ invariant " (or requires/ensures) to do that instead.\n'
                  "  A bare predicate instance such as `l.Mem()` is also impure and is NOT\n"
                  "  detected here: only `acc(...)` and wands are.")
        nested = [(p, analyse(p)) for p in parts]
        follow = [(p, k, s) for p, (k, s, _) in nested if k not in ("atomic", "empty")]
        if follow:
            print("\nConjuncts that decompose further:")
            for p, k, s in follow:
                print(f"  [{k}, §{s}]  {p}")
    elif parts:
        labels = {
            "implication": ("antecedent", "consequent"),
            "equivalence": ("left", "right"),
            "magic wand": ("left", "right"),
            "ternary": ("condition", "then", "else"),
            "disjunction": None,
        }.get(kind)
        if labels:
            for label, p in zip(labels, parts):
                print(f"  {label}: {p}")
        else:
            for p in parts:
                print(f"  operand: {p}")


if __name__ == "__main__":
    main()
