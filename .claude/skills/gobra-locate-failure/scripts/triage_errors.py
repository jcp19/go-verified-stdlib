#!/usr/bin/env python3
"""Parse a Gobra run's output into one row per verification error and say which
proof action to try first on each.

Usage:
    triage_errors.py gobra-run.log [--json] [--all]
    gobra -p ./pkg --noStreamErrors 2>&1 | triage_errors.py

Gobra prints each verification error as

    <src/pkg/file.go:191:6> Assert might fail.
    Assertion forall k int :: ... might not hold.

where the first line names the *obligation* that failed and the following
line(s) give the *reason* the backend could not discharge it. The two carry
different information: the obligation picks the action, the reason says whether
you are looking at a missing fact, a missing resource, or a well-definedness
side condition. This script classifies both and maps the pair onto a section of
SKILL.md.

Run Gobra with --noStreamErrors so errors arrive grouped per package rather
than interleaved with progress output.
"""

import argparse
import json
import re
import sys

# `<file:line:column> message`, tolerant of any log prefix in front of it.
POS_RE = re.compile(r"<(?P<file>[^<>\s][^<>]*?):(?P<line>\d+):(?P<col>\d+)>\s*(?P<msg>.*)")

# Lines that are never part of an error's reason text.
NOISE_RE = re.compile(
    r"^\s*(Gobra\b|Verifying\b|Parsing\b|Type-?check|Progress\b|\[\d|INFO\b|DEBUG\b|WARN\b)",
    re.IGNORECASE,
)

# Error classes, matched against the first line. Order matters: the first
# pattern that matches wins, so more specific messages come first.
ERRORS = [
    ("assert_by",            r"Assert by might fail"),
    ("assert",               r"Assert might fail"),
    ("refute",               r"Refute statement failed"),
    ("postcondition",        r"Postcondition might not hold"),
    ("spec_postcondition",   r"Postcondition of spec .* might not hold"),
    ("precondition",         r"Precondition of call .* might not hold"),
    ("invariant_establish",  r"Loop invariant might not be established"),
    ("invariant_preserve",   r"Loop invariant might not be preserved"),
    ("invariant_wellformed", r"Loop invariant is not well-formed"),
    ("fold",                 r"Fold might fail"),
    ("unfold",               r"Unfold might fail"),
    ("exhale",               r"Exhale might fail"),
    ("inhale",               r"Inhale might fail"),
    ("assignment",           r"Assignment might fail"),
    ("load",                 r"Reading might fail"),
    ("call",                 r"Call might fail"),
    ("type_assertion",       r"Type assertion might fail"),
    ("comparison",           r"Comparison might panic"),
    ("overflow",             r"Expression may cause integer overflow"),
    ("loop_termination",     r"The loop .* might not terminate"),
    ("termination",          r"(Pure function|Function) might not terminate"),
    ("pure_wellformed",      r"The pure function is not well-formed"),
    ("contract_wellformed",  r"(Method contract|Contract) is not well-formed"),
    ("predicate_wellformed", r"Predicate body is not well-formed"),
    ("wand_wellformed",      r"Magic wand might not be well-formed"),
    ("wand_package",         r"Packaging wand might fail"),
    ("wand_apply",           r"Applying wand might fail"),
    ("impl_proof",           r"Generated implementation proof"),
    ("conditional",          r"Conditional statement might fail"),
    ("for_loop",             r"For loop statement might fail"),
    ("range_expr",           r"(range expression|Length of range expression)"),
    ("make_precondition",    r"The provided (length|length to)"),
    ("shift",                r"The shift count"),
    ("uncaught",             r"Encountered an unexpected Viper error"),
]

# Reason classes, matched against the lines following the error.
REASONS = [
    ("permission",        r"Permission to .* might not suffice"),
    ("refutation_true",   r"Assertion .* definitely holds"),
    ("assertion_false",   r"Assertion .* might not hold"),
    ("seq_index_high",    r"Index .* might exceed sequence length"),
    ("seq_index_neg",     r"Index .* might be negative"),
    ("map_key",           r"Key .* might not be contained"),
    ("division_by_zero",  r"Divisor .* might be zero"),
    ("overflow",          r"might cause integer overflow"),
    ("qp_not_injective",  r"Quantified resource .* might not be injective"),
    ("measure_decrease",  r"Termination measure might not decrease"),
    ("measure_bounded",   r"Termination measure might not be bounded"),
    ("termination_cond",  r"Required termination condition might not hold"),
    ("tuple_cond",        r"Required tuple condition might not hold"),
    ("no_witness",        r"Witness for assertion .* not found"),
    ("wand_not_found",    r"Magic wand instance not found"),
    ("nil_receiver",      r"The receiver might be nil"),
    ("by_body",           r"The proof block might not establish the assertion"),
    ("by_contra_body",    r"The proof block might not derive a contradiction"),
    ("negative_perm",     r"Expression .* might be negative"),
    ("label_not_reached", r"Did not reach labelled state"),
    ("go_call_pre",       r"might not satisfy the precondition of the callee"),
    ("not_a_subtype",     r"Dynamic value might not be a subtype"),
    ("incomparable",      r"might not have comparable values"),
]

# Reason-driven advice wins over error-driven advice: a permission failure is a
# resource problem whatever obligation it was reported on.
BY_REASON = {
    "permission":       ("3.11", "Resource failure, not a missing fact. Probe `assert acc(e, _)` first, then walk it up."),
    "refutation_true":  ("5",    "A `refute` fired: this state is unreachable or the assertion always holds. Expected if you placed it as a vacuity probe; otherwise the context is inconsistent."),
    "seq_index_high":   ("3.10", "Well-definedness. Assert the index bounds before the property."),
    "seq_index_neg":    ("3.10", "Well-definedness. Assert the index bounds before the property."),
    "map_key":          ("3.10", "Well-definedness. Assert key containment before the property."),
    "division_by_zero": ("3.10", "Well-definedness. Assert the divisor is non-zero before the property."),
    "overflow":         ("3.1",  "Decompose the arithmetic; consider stating the spec over `integer` (gobra-review-code §5)."),
    "qp_not_injective": ("3.11", "The quantified permission's receiver expression is not visibly injective — look for overlapping subslices in the footprint."),
    "measure_decrease": ("3.4",  "Snapshot the measure in a ghost variable and assert that it decreased."),
    "measure_bounded":  ("3.4",  "Snapshot the measure and assert its lower bound."),
    "termination_cond": ("3.4",  "The `decreases` condition itself fails; assert it where the call is made."),
    "tuple_cond":       ("3.4",  "Snapshot the measure tuple and compare component by component."),
    "no_witness":       ("2 Q3", "An assign-such-that found no witness. Inconclusive as a refutation; it does not mean the property holds."),
    "wand_not_found":   ("3.11", "The magic wand instance is not held here. Walk `assert` up to where it was packaged."),
    "nil_receiver":     ("3.9",  "Case-split on the receiver being nil."),
    "by_body":          ("3.1",  "The proof block does not establish the assertion. Decompose inside the block."),
    "by_contra_body":   ("3.1",  "The contradiction is not derived. Decompose inside the `by contra` block."),
    "negative_perm":    ("3.11", "A permission amount may be negative — check the fraction arithmetic in the contract."),
    "label_not_reached":("3.3",  "An `old[l]` refers to a state the execution may not reach on this path."),
    "not_a_subtype":    ("3.9",  "Case-split on the dynamic type."),
    "incomparable":     ("3.9",  "Case-split, or constrain the interface's dynamic type."),
}

BY_ERROR = {
    "assert":               ("3.1", "Decompose the assertion, then walk the failing conjunct up (§3.3)."),
    "assert_by":            ("3.1", "Decompose inside the proof block."),
    "refute":               ("2 Q1", "Expected if you placed this probe deliberately: the state is unreachable or the assertion always holds."),
    "postcondition":        ("3.2", "Copy the clause to an `assert` at each return, AFTER the results are assigned\n                          (`return e` -> `res = e; assert ...; return`), then decompose (§3.1)."),
    "spec_postcondition":   ("3.2", "Materialize the spec's postcondition in the implementing member."),
    "precondition":         ("3.2", "Copy the callee's `requires` (actuals for formals) to an `assert` before the call, then decompose."),
    "invariant_establish":  ("3.2", "Assert the clause BEFORE the loop, with the init value substituted for the loop variable."),
    "invariant_preserve":   ("3.2", "Assert the clause at the END of the loop body, with the post statement's effect substituted\n                          (`i+1` for `i` when the post is `i++`)."),
    "invariant_wellformed": ("1",   "The invariant reads state it does not own, or is ill-typed. Fix well-formedness before probing."),
    "fold":                 ("3.11","Assert each conjunct of the predicate body just before the `fold`."),
    "unfold":               ("3.11","Assert `acc(P(x), _)` before the `unfold`."),
    "exhale":               ("3.11","Resource transfer failed; localize the permission."),
    "inhale":               ("3.11","Check the assertion is self-framing and the amounts are positive."),
    "assignment":           ("3.11","Localize the permission to the assigned location."),
    "load":                 ("3.11","Localize the read permission to the location."),
    "call":                 ("3.11","Localize the resources the call consumes."),
    "type_assertion":       ("3.9", "Case-split on the dynamic type."),
    "comparison":           ("3.9", "Case-split, or constrain the operands' dynamic types."),
    "overflow":             ("3.1", "Decompose the arithmetic and assert bounds per operand (gobra-review-code §5)."),
    "termination":          ("3.4", "Snapshot the measure and assert that it decreased."),
    "loop_termination":     ("3.4", "Snapshot the measure and assert that it decreased across the body."),
    "pure_wellformed":      ("3.2", "Use `asserting <precondition> in <body>` — a pure function admits no statements."),
    "contract_wellformed":  ("1",   "The contract reads state it does not own (self-framing). Fix that before probing."),
    "predicate_wellformed": ("1",   "The predicate body is not self-framing or is ill-typed."),
    "wand_wellformed":      ("1",   "The wand's footprint is not self-framing."),
    "wand_package":         ("3.11","The wand's proof cannot produce the right-hand side; decompose it."),
    "wand_apply":           ("3.11","The wand instance or its left-hand side is not held here."),
    "impl_proof":           ("1",   "Compare the interface method's contract with the implementation's before probing."),
    "conditional":          ("3.5", "Introduce the hypothesis: probe inside each branch."),
    "for_loop":             ("3.2", "Probe the invariant at both ends of the body."),
    "range_expr":           ("3.11","Range expressions need read permission and immutability across the body."),
    "make_precondition":    ("3.1", "Assert the length/capacity bounds before the `make`."),
    "shift":                ("3.1", "Assert the shift count is non-negative before the expression."),
    "uncaught":             ("-",   "A Gobra bug (unexpected Viper error). Report it; no proof action applies."),
}


def classify(text, table):
    for name, pattern in table:
        if re.search(pattern, text):
            return name
    return None


def parse(lines):
    """Return a list of error records, in the order Gobra reported them."""
    records, cur = [], None
    for raw in lines:
        line = raw.rstrip("\n")
        m = POS_RE.search(line)
        if m:
            if cur:
                records.append(cur)
            cur = {
                "file": m.group("file"),
                "line": int(m.group("line")),
                "col": int(m.group("col")),
                "message": m.group("msg").strip(),
                "reason": "",
            }
            continue
        if cur is not None:
            stripped = line.strip()
            if not stripped or NOISE_RE.match(line):
                # Blank line or a log line ends the reason block.
                records.append(cur)
                cur = None
            else:
                cur["reason"] = (cur["reason"] + " " + stripped).strip()
    if cur:
        records.append(cur)

    for r in records:
        r["error_kind"] = classify(r["message"], ERRORS) or "unclassified"
        r["reason_kind"] = classify(r["reason"], REASONS) or "unclassified"
        section, advice = BY_REASON.get(
            r["reason_kind"],
            BY_ERROR.get(r["error_kind"], ("-", "Unrecognized message — read it against the tables in SKILL.md §1.")),
        )
        r["section"] = section
        r["action"] = advice
    return records


def dedupe(records):
    """Collapse identical (position, message, reason) rows, keeping a count."""
    seen, out = {}, []
    for r in records:
        key = (r["file"], r["line"], r["col"], r["message"], r["reason"])
        if key in seen:
            seen[key]["count"] += 1
        else:
            r = dict(r, count=1)
            seen[key] = r
            out.append(r)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", nargs="?", help="Gobra output; reads stdin when omitted")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    ap.add_argument("--all", action="store_true", help="do not collapse duplicate errors")
    args = ap.parse_args()

    try:
        src = open(args.log) if args.log else sys.stdin
        with src:
            records = parse(src)
    except OSError as e:
        sys.exit(f"could not read {args.log}: {e}")

    if not args.all:
        records = dedupe(records)
    else:
        records = [dict(r, count=1) for r in records]

    if args.json:
        json.dump(records, sys.stdout, indent=2)
        sys.stdout.write("\n")
        return

    if not records:
        print("No verification errors found in the input.")
        print("If the run produced errors, check that the log is the one Gobra wrote "
              "(stderr included) and that positions are printed as <file:line:col>.")
        return

    by_file = {}
    for r in records:
        by_file.setdefault(r["file"], []).append(r)

    for path in sorted(by_file):
        rows = sorted(by_file[path], key=lambda r: (r["line"], r["col"]))
        print(f"\n{path}")
        print("-" * max(len(path), 78))
        for r in rows:
            times = f"  (x{r['count']})" if r["count"] > 1 else ""
            print(f"  {r['line']}:{r['col']}  [{r['error_kind']} / {r['reason_kind']}]{times}")
            print(f"      {r['message']}")
            if r["reason"]:
                print(f"      {r['reason']}")
            print(f"      -> §{r['section']}  {r['action']}")

    total = sum(r["count"] for r in records)
    print(f"\n{total} error(s) at {len(records)} distinct position(s) in {len(by_file)} file(s).")

    kinds = {r["reason_kind"] for r in records}
    if "permission" in kinds:
        print("\nAt least one failure is a PERMISSION failure. No lemma, assert or reveal "
              "will produce a resource you do not hold — start at SKILL.md §3.11.")
    if "unclassified" in {r["error_kind"] for r in records}:
        print("\nSome messages did not match a known Gobra error. They may come from a newer "
              "Gobra than this script knows about; read them against the tables in SKILL.md §1.")

    print("\nSilicon stops each member at its FIRST failing obligation, so this list is a "
          "lower bound: fixing one error routinely reveals more. That is not a regression.")
    print("Before acting on any of it, run the §2 triage: reachable state, not a timeout, "
          "property actually true.")


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        # Piping into `head` closes the pipe early; that is not an error here.
        sys.stderr.close()
