#!/usr/bin/env python3
"""Consume completed masked transitions; emit only kernel-checked Lean certificates."""

import argparse
import hashlib
import json
from pathlib import Path

from generate_finite_orbits import transform

ROOT = Path(__file__).resolve().parents[1]


def xor_selected(basis, mask):
    value = 0
    for k, row in enumerate(basis):
        if (mask >> k) & 1:
            value ^= row
    return value


def reduce_code(basis, code):
    for row in basis:
        if (code >> max(0, row.bit_length() - 1)) & 1:
            code ^= row
    return code


def unpack(positions, mask):
    return sum(((mask >> k) & 1) << p for k, p in enumerate(positions))


def pack(positions, code):
    return sum(((code >> p) & 1) << k for k, p in enumerate(positions))


def integer(value, lower, upper):
    if type(value) is not int or not lower <= value < upper:
        raise ValueError(f"out-of-range integer: {value!r}")
    return value


def load_cases(bases_path, transitions_path):
    bases = json.loads(bases_path.read_text())
    if len(bases) != 496:
        raise ValueError("expected exactly 496 exported bases")
    for bs in bases:
        for code in bs:
            integer(code, 0, 512)
    records = [json.loads(line) for line in transitions_path.read_text().splitlines()]
    if not records or records[-1].get("complete") is not True:
        raise ValueError("missing successful terminal record")
    headers = [r for r in records[:-1] if "orbit" in r]
    if len(headers) != 496 or {r["orbit"] for r in headers} != set(range(496)):
        raise ValueError("missing or duplicate orbit headers")
    witnesses = {}
    for row in records[:-1]:
        if "orbit" in row:
            continue
        i = integer(row["source"], 0, 496)
        c = integer(row["code"], 1, 512)
        j = integer(row["target"], 0, 496)
        word, forward, backward = row["word"], row["forward"], row["backward"]
        if len(word) > 128:
            raise ValueError("unexpectedly long generator word")
        for g in word:
            integer(g, 0, 4)
        source = [c] + bases[i]
        target = list(bases[j])
        for g in reversed(word):
            target = [transform(g, x) for x in target]
        if len(forward) != len(source) or len(backward) != len(target):
            raise ValueError(f"mask lengths disagree at {(i, c)}")
        for mask in forward:
            integer(mask, 0, 2 ** len(target))
        for mask in backward:
            integer(mask, 0, 2 ** len(source))
        if [xor_selected(target, m) for m in forward] != source:
            raise ValueError(f"forward masks disagree at {(i, c)}")
        if [xor_selected(source, m) for m in backward] != target:
            raise ValueError(f"backward masks disagree at {(i, c)}")
        if (i, c) in witnesses:
            raise ValueError(f"duplicate extension {(i, c)}")
        witnesses[i, c] = (j, word, forward, backward)
    if len(witnesses) != records[-1]["extensions"]:
        raise ValueError("terminal extension count disagrees")
    cases, used = [], set()
    for i, bs in enumerate(bases):
        pivots = {b.bit_length() - 1 for b in bs if b}
        free = [p for p in range(9) if p not in pivots]
        for a in (1 << p for p in range(9)):
            residue = reduce_code(bs, a)
            if unpack(free, pack(free, residue)) != residue:
                raise ValueError(f"frozen row reduction is not normalized at {i}")
        rows = [(i, [], [0] + [1 << k for k in range(len(bs))],
                 [1 << (k + 1) for k in range(len(bs))])]
        for k in range(1, 2 ** len(free)):
            c = unpack(free, k)
            if (i, c) not in witnesses:
                raise ValueError(f"missing normalized extension {(i, c)}")
            rows.append(witnesses[i, c])
            used.add((i, c))
        cases.append((free, rows))
    if used != witnesses.keys():
        raise ValueError("unexpected noncanonical extension rows")
    return cases


def lean_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def emit_group(group, cases):
    namespace = f"QiushiMatmul.GlobalOrbit.Cases{group}"
    data_name = f"QiushiGlobalOrbitData{group}"
    check_name = f"QiushiGlobalOrbitChecks{group}"
    data = ["import QiushiGlobalOrbitNormalizer", "", f"namespace {namespace}",
            "set_option maxRecDepth 20000", "set_option maxHeartbeats 16000000", ""]
    check = [f"import {data_name}", "", f"namespace {namespace}",
             "set_option maxRecDepth 20000", "set_option maxHeartbeats 16000000", ""]
    for i in range(group * 16, (group + 1) * 16):
        free, rows = cases[i]
        data.append(f"def free{i} : List Nat := {lean_list(free)}\n")
        chunks = (len(rows) + 63) // 64
        for k in range(chunks):
            data.append(f"def rows{i}_{k} : Array Transition := #[")
            literals = ["  \u27e8" + str(j) + ", " + lean_list(w) + ", " + lean_list(f)
                        + ", " + lean_list(b) + "\u27e9" for j, w, f, b in rows[k * 64:(k + 1) * 64]]
            data.append(",\n".join(literals) + "]\n")
        data.append(f"def blocks{i} : Array (Array Transition) := #[" +
                    ", ".join(f"rows{i}_{k}" for k in range(chunks)) + "]\n")
        data.append(f"def rows{i} (k : Fin (2 ^ free{i}.length)) : Transition :=\n"
                    f"  ((blocks{i}.getD (k.val / 64) #[]).getD (k.val % 64) \u27e80, [], [], []\u27e9)\n")
        check.append(f"theorem normalized{i} : NormalizationCheck (frozenWangBasis {i}) free{i} := by\n"
                     "  decide +kernel +revert\n")
        check.append(f"theorem checked{i} : \u2200 k : Fin (2 ^ free{i}.length), TransitionCheck {i} (unpackCode free{i} k.val) (rows{i} k) := by\n"
                     "  decide +kernel +revert\n")
    check.append("theorem covered (j : Fin 16) : \u2200 c : Fin 512,\n"
                 f"    Covered (spanCodes (c.val :: frozenWangBasis \u27e8{16 * group} + j.val, by omega\u27e9)) := by\n"
                 "  fin_cases j")
    for i in range(group * 16, (group + 1) * 16):
        check.append(f"  \u00b7 exact extensions_of_normalized {i} free{i} normalized{i} rows{i} checked{i}")
    data.extend(["", f"end {namespace}", ""])
    check.extend(["", f"end {namespace}", ""])
    (ROOT / (data_name + ".lean")).write_text("\n".join(data))
    (ROOT / (check_name + ".lean")).write_text("\n".join(check))


def emit_root():
    lines = [f"import QiushiGlobalOrbitChecks{g}" for g in range(31)]
    lines += ["", "namespace QiushiMatmul.GlobalOrbit", "open PlaneOrbit",
              "set_option maxHeartbeats 4000000", "", "theorem extension_checks : ExtensionChecks := by",
              "  have block (b : Fin 31) : \u2200 j : Fin 16, \u2200 c : Fin 512,",
              "      Covered (spanCodes (c.val :: frozenWangBasis",
              "        \u27e816 * b.val + j.val, by omega\u27e9)) := by", "    fin_cases b"]
    lines += [f"    \u00b7 exact Cases{g}.covered" for g in range(31)]
    lines += ["  intro i c", "  let b : Fin 31 := \u27e8i.val / 16, by omega\u27e9",
              "  let j : Fin 16 := \u27e8i.val % 16, Nat.mod_lt _ (by decide)\u27e9",
              "  have he : 16 * b.val + j.val = i.val := Nat.div_add_mod i.val 16",
              "  have h := block b j c", "  simpa only [he] using h", "",
              "/-- Every actual matrix subspace lies in one of the 496 frozen direct-action orbits. -/",
              "theorem frozen_coverage (W : Space) :",
              "    \u2203 i : Fin 496, frozenWangTable.OrbitImage i W := coverage_of_extensions extension_checks W", "",
              "theorem all_dimensions_covered (d : Nat) : CoversDimension d := fun W _ => frozen_coverage W", "",
              "theorem frozen_annihilators_covered (i : Fin 496) : Covered (dual (representative i)) :=",
              "  frozen_coverage _", "", "#check frozen_coverage", "#check all_dimensions_covered",
              "#print axioms extension_checks", "#print axioms frozen_coverage",
              "#print axioms all_dimensions_covered", "", "end QiushiMatmul.GlobalOrbit", ""]
    (ROOT / "QiushiGlobalOrbitCoverage.lean").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--bases", type=Path, required=True)
    parser.add_argument("--transitions", type=Path, required=True)
    parser.add_argument("--group", type=int, choices=range(31), action="append")
    args = parser.parse_args()
    cases = load_cases(args.bases, args.transitions)
    for group in args.group if args.group is not None else range(31):
        emit_group(group, cases)
    if args.group is None:
        emit_root()
    print("Validated producer input; emitted requested Lean data/check modules.")
    print("Residue cases:", sum(len(rows) for _, rows in cases))
    print("Transitions SHA256:", hashlib.sha256(args.transitions.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
