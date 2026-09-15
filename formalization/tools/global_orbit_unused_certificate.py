"""Regenerate one unused occupation certificate from proved predecessor bounds."""

import argparse
from collections import deque
from fractions import Fraction
from functools import reduce
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog

from generate_certificate import emit_data, finish, rref, span
from generate_finite_orbits import transform
from generate_global_orbit_checks import load_cases, pack, reduce_code, unpack


def word_code(word, code):
    for g in reversed(word):
        code = transform(g, code)
    return code


def superspaces(node, bases, cases, space_limit=400):
    """Only enumerate the small quotient above this particular frozen node."""
    basis = tuple(bases[node])
    free = cases[node][0]
    sections = [unpack(free, k) for k in range(2 ** len(free))]
    found = {basis: (node, [])}
    pending = deque([basis])
    while pending:
        actual = pending.popleft()
        representative, word = found[actual]
        for code in sections:
            child = rref([*actual, code])
            if child in found:
                continue
            preimage = word_code(list(reversed(word)), code)
            residue = reduce_code(bases[representative], preimage)
            positions, transitions = cases[representative]
            target, tail, _, _ = transitions[pack(positions, residue)]
            child_word = word + tail
            if rref(word_code(child_word, c) for c in bases[target]) != child:
                raise ValueError("extension word failed explicit replay")
            if len(found) >= space_limit:
                raise ValueError("bounded quotient-subspace enumeration exhausted")
            found[child] = target, child_word
            pending.append(child)
    return found, sections


def source_rows(node, bases, cases, registry):
    spaces, sections = superspaces(node, bases, cases)
    known = {row["index"]: row for row in registry["entries"]}
    rows, unavailable = [], set()
    for basis, (target, word) in spaces.items():
        if target == node:
            continue
        entry = known.get(target)
        source = entry.get("source") if entry else None
        if not source or not span(bases[target]) <= span(source["basis"]):
            unavailable.add(target)
            continue
        preimages = [word_code(list(reversed(word)), c) for c in basis]
        if not all(c in span(source["basis"]) for c in preimages):
            raise ValueError("source containment disagrees with transport")
        rows.append(dict(idx=len(rows), basis=list(basis), orbit=target,
                         lb=entry["lb"], source=source, word=word, preimages=preimages))
    return rows, sections, sorted(unavailable), len(spaces)


def matrix_product(a, b):
    return sum((sum(((a >> (3 * i + k)) & 1) * ((b >> (3 * k + j)) & 1)
                    for k in range(3)) % 2) << (3 * i + j)
               for i in range(3) for j in range(3))


def transport(row):
    left, right, flip = 273, 273, False
    for g in reversed(row["word"]):
        if g == 3:
            left, right, flip = transform(3, right), transform(3, left), not flip
        else:
            left = matrix_product(transform(g, 273), left)
    inverse = next(q for q in range(512) if matrix_product(q, right) == 273)
    for code in range(512):
        actual = matrix_product(matrix_product(left, transform(3, code) if flip else code), right)
        if actual != word_code(row["word"], code):
            raise ValueError("word and explicit matrix transport disagree")
    return dict(P=transform(3, left), Q=transform(3, inverse), Qinv=transform(3, right),
                flip=flip, pairs=list(zip(row["basis"], row["preimages"])))


def exact_branch(data, node_limit=255, seconds=90):
    """The established LP branch procedure, with exact integer checks on every ray."""
    target = data["target"]
    source = data["rows"]
    dead_rows = [r for r in source if r["lb"] == target]
    if not dead_rows:
        raise ValueError("the existing extraction theorem requires a dead witness")
    dead = set().union(*(span(r["basis"]) for r in dead_rows))
    live = [q - 1 for q, c in enumerate(data["sections"]) if c not in dead]
    sections = [data["sections"][q + 1] for q in live]
    unique = {}
    for row in source:
        mask = tuple(int(c in span(row["basis"])) for c in sections)
        if any(mask) and (mask not in unique or unique[mask]["lb"] < row["lb"]):
            unique[mask] = row
    rows = list(unique.values())
    n = len(live)
    A = [[int(c in span(r["basis"])) for c in sections] for r in rows]
    b = [target - r["lb"] for r in rows]
    refs = [dict(type="occ", row=r["idx"]) for r in rows]
    A.append([-1] * n)
    b.append(-target)
    refs.append(dict(type="total_ge"))
    for j, q in enumerate(live):
        A.append([-int(k == j) for k in range(n)])
        b.append(0)
        refs.append(dict(type="nonneg", label=q + 1))
    leaves, used = [], {r["idx"] for r in dead_rows}
    started, visited = time.monotonic(), 0

    def lp(*args, **kwargs):
        return linprog(*args, **kwargs, method="highs", options={"threads": 1})

    def visit(path, branchA, branchb, branchrefs, lower, upper):
        nonlocal visited
        visited += 1
        if visited > node_limit or time.monotonic() - started > seconds:
            raise RuntimeError("bounded branch search exhausted")
        aa, bb, rr = np.array(A + branchA), np.array(b + branchb), refs + branchrefs
        result = lp(np.zeros(n), A_ub=aa, b_ub=bb, bounds=[(None, None)] * n)
        if result.status == 2:
            dual = lp(bb, A_eq=np.vstack([aa.T, np.ones(len(bb))]),
                      b_eq=np.r_[np.zeros(n), 1], bounds=(0, None))
            if not dual.success or dual.fun >= -1e-8:
                raise ValueError("no Farkas ray")
            fractions = [Fraction(float(x)).limit_denominator(100000) for x in dual.x]
            denominator = lcm(*(x.denominator for x in fractions))
            weights = [int(x * denominator) for x in fractions]
            divisor = reduce(gcd, weights)
            weights = [x // divisor for x in weights]
            rhs = sum(w * int(bb[i]) for i, w in enumerate(weights))
            if any(w < 0 for w in weights) or rhs >= 0 or any(
                    sum(w * int(aa[i, j]) for i, w in enumerate(weights)) for j in range(n)):
                raise ValueError("rationalized ray failed exact verification")
            used_rows = [dict(ref, multiplier=w) for ref, w in zip(rr, weights) if w]
            used.update(u["row"] for u in used_rows if u["type"] == "occ")
            leaves.append(dict(path=path, lower=lower, upper=upper, used_rows=used_rows, rhs=rhs))
            return dict(type="leaf", path=path)
        if not result.success:
            raise ValueError(result.message)
        fractional = np.abs(result.x - np.rint(result.x))
        j = int(np.argmax(fractional))
        if fractional[j] <= 1e-7:
            raise ValueError(f"integer occupation model: {result.x}")
        floor = int(np.floor(result.x[j] + 1e-8))
        q = live[j]
        unit = [int(j == k) for k in range(n)]
        left = visit(path + "L", branchA + [unit], branchb + [floor],
                     branchrefs + [dict(type="branch_upper", label=q + 1, bound=floor)],
                     lower, dict(upper, **{str(q): floor}))
        right = visit(path + "R", branchA + [[-x for x in unit]], branchb + [-floor - 1],
                      branchrefs + [dict(type="branch_lower", label=q + 1, bound=floor + 1)],
                      dict(lower, **{str(q): floor + 1}), upper)
        return dict(type="branch", path=path, label=q + 1, floor=floor, left=left, right=right)

    tree = visit("", [], [], [], {}, {})
    selected = [dict(r, orig=r["idx"]) for r in source if r["idx"] in used]
    for idx, row in enumerate(selected):
        row["idx"] = idx
    by_orig = {r["orig"]: r["idx"] for r in selected}
    node = data["node"]
    meta = dict(plane=node, name_tag="Unused", module_prefix=f"QiushiGlobalOrbitUnused{node}",
                target=target, basis=data["basis"], n_live=n, n_occ=len(selected),
                n_dead=len(dead_rows), live_list=live, source_rows=selected,
                dead_witnesses=[dict(basis=r["basis"], witness_source_idx=by_orig[r["idx"]])
                                for r in dead_rows])
    return meta, dict(basis=data["basis"], branch=dict(tree=tree, certs=leaves))


def emit_certificate(data, out):
    meta, cert = exact_branch(data)
    out.mkdir(parents=True, exist_ok=True)
    ledger = {"entries": {str(r["orbit"]): dict(orbit=r["orbit"], lb=r["source"]["bound"],
              basis_codes=r["source"]["basis"], theorem=r["source"]["theorem"],
              module=r["source"]["module"]) for r in meta["source_rows"]}}
    transports = {r["idx"]: transport(r) for r in meta["source_rows"]}
    for name, value in [("tables", meta), ("branch", cert), ("sources", ledger)]:
        (out / (name + ".json")).write_text(json.dumps(value, indent=2) + "\n")
    emit_data(meta, out)
    finish(meta, cert, ledger, out, transports=transports)
    print("Certificate:", meta["n_live"], "live,", meta["n_occ"], "source rows,",
          meta["n_dead"], "dead rows,", len(cert["branch"]["certs"]), "leaves")
    print("Selected predecessors:", sorted({r["orbit"] for r in meta["source_rows"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bases", type=Path, required=True)
    parser.add_argument("--transitions", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--node", type=int, choices=range(496), required=True)
    parser.add_argument("--bound", type=int, choices=range(1, 28), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    bases = json.loads(args.bases.read_text())
    cases = load_cases(args.bases, args.transitions)
    registry = json.loads(args.registry.read_text())
    rows, sections, unavailable, space_count = source_rows(args.node, bases, cases, registry)
    target = args.bound - 1
    matrix = np.array([[int(c in span(row["basis"])) for c in sections] for row in rows])
    caps = np.array([target - row["lb"] for row in rows])
    result = linprog(-np.ones(len(sections)), A_ub=matrix, b_ub=caps, bounds=(0, None),
                     method="highs", options={"threads": 1})
    data = dict(node=args.node, basis=bases[args.node], target=target, rows=rows,
                sections=sections, quotient_subspaces=space_count, unavailable=unavailable,
                lp_status=result.status, lp_total=None if result.fun is None else -result.fun)
    data["input_sha256"] = {name: hashlib.sha256(path.read_bytes()).hexdigest()
                            for name, path in [("bases", args.bases), ("transitions", args.transitions),
                                               ("registry", args.registry)]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: v for k, v in data.items() if k not in {"rows", "sections"}}))
    print("Available predecessors:", sorted({r["orbit"] for r in rows}))
    print("Source rows:", len(rows))
    if args.emit:
        emit_certificate(data, args.emit)


if __name__ == "__main__":
    main()
