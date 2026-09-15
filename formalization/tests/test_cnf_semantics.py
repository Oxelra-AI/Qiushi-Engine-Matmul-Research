#!/usr/bin/env python3
"""Compare small Lean CNFs with the public transparent encoder; no DRAT claim."""
import argparse
from collections import Counter
import importlib.util
import itertools
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ENCODER = ROOT / "proof/assets/structural/scripts/transparent_unary_dim2_cnf.py"
spec = importlib.util.spec_from_file_location("transparent_encoder", ENCODER)
encoder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(encoder)


def normalized(clauses):
    return Counter(tuple(sorted(set(clause))) for clause in clauses)


def sat(clauses, values):
    return all(any(values[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def witness(builder, inputs, n):
    values = {i + 1: value for i, value in enumerate(inputs)}
    values.update({i: False for i in range(n + 1, builder.top + 1)})
    for block in builder.ranges:
        width = block["thresholds"] + 1
        for i in range(block["n_prefix"] + 1):
            count = sum(inputs[:i])
            for j in range(width):
                values[block["start_var"] + i * width + j] = j <= count
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-log", type=Path, required=True)
    args = parser.parse_args()
    records = [json.loads(line) for line in args.lean_log.read_text().splitlines()
               if line.startswith('{"')]
    assert len(records) == 45, len(records)
    tested_inputs = exhaustive_cases = 0
    for rec in records:
        n, k, kind = rec["n"], rec["k"], rec["kind"]
        builder = encoder.CNFBuilder(top=n)
        if kind == "row":
            cap = k - 1
            encoder.add_row_atmost_forward(builder, list(range(1, n+1)), cap, "test")
        else:
            encoder.add_total_exact_prefix(builder, list(range(1, n+1)), k)
        assert normalized(rec["clauses"]) == normalized(builder.clauses), (kind, n, k)
        for inputs in itertools.product((False, True), repeat=n):
            legal = sum(inputs) <= cap if kind == "row" else sum(inputs) == k
            values = witness(builder, inputs, n)
            if legal:
                assert sat(builder.clauses, values), ("lifting", kind, n, k, inputs)
            tested_inputs += 1
            used_aux = sorted({abs(lit) for cl in builder.clauses for lit in cl if abs(lit) > n})
            if n <= 3 and len(used_aux) <= 12 and (kind == "row" or n > 0):
                exists = False
                for bits in itertools.product((False, True), repeat=len(used_aux)):
                    values.update(zip(used_aux, bits))
                    if sat(builder.clauses, values):
                        exists = True
                        break
                assert exists == legal, ("soundness", kind, n, k, inputs)
                exhaustive_cases += 1
    # Explicitly retain the reason for exactPrefixCNF_correct's n > 0 premise.
    empty = encoder.CNFBuilder(top=0)
    encoder.add_total_exact_prefix(empty, [], 1)
    assert sat(empty.clauses, {1: False, 2: True, 3: False})
    print(json.dumps({"clause_multiset_matches": len(records), "input_assignments": tested_inputs,
                      "exhaustive_extension_checks": exhaustive_cases,
                      "empty_positive_exact_counterexample_confirmed": True,
                      "frozen_cnf_or_drat_replay": False}, indent=2))


if __name__ == "__main__":
    main()
