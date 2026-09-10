#!/usr/bin/env python3
"""analysis: Ruling-line transport for Wang F2 support exclusion.

Mathematical basis
------------------
The 49 rank-1 matrices uv^T (u,v in F_2^3 \ {0}) form a 7x7 Segre grid.
A "ruling line" is a triple {uv1^T, uv2^T, uv3^T} where {v1,v2,v3} is a
projective line in PG(2,F_2) (left ruling), or the transpose version (right
ruling).  The Fano plane PG(2,F_2) has 7 points and 7 lines, so there are
7*7 = 49 left-ruling lines and 49 right-ruling lines, giving 98 total.

The DRAT-verified exclusion of prefix {1,2,3} (the left-ruling line with
u = (1,0,0) and v-line {(1,0,0),(0,1,0),(1,1,0)}) transports under
GL(3,2) x GL(3,2) : C_2 to all 98 ruling-line triples, because:
  - the group acts transitively on ruling-line triples (orbit size 98);
  - the Wang occupation LUT is equivariant under this group action.

For any prefix P, each ruling-line triple {a,b,c} yields:
  |{a,b,c} & P| = 3 --> prefix is infeasible
  |{a,b,c} & P| = 2 --> unit clause excluding the third point
  |{a,b,c} & P| = 1 --> binary clause (at-most-one of the other two)
  |{a,b,c} & P| = 0 --> ternary clause (at-most-two of all three)

For the rep2 prefix [1,2]: 1 unit (exclude point 3) + 10 binary + 87 ternary.
These constrain the FULL rep2 branch before any third-point marking.
For the matching branch: all matchings avoid ruling-line triples (no adjacent
pair), so ruling-line clauses are vacuous there.

Usage
-----
  # Enumerate only:
  python ruling_line_transport.py --prefix 1,2 --enumerate-only --out-dir OUT

  # Build augmented base + ruling-line CNF, solve, LUT-scan:
  python ruling_line_transport.py --prefix 1,2 --out-dir OUT

  # Custom solve time:
  python ruling_line_transport.py --prefix 1,2 --out-dir OUT --solve-time 600
"""
from __future__ import annotations
import argparse, json, os, pathlib, pickle, subprocess, sys, time
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

# ------------------------------------------------------------------ #
#  Ruling-line geometry on the 7x7 Segre grid                        #
# ------------------------------------------------------------------ #

def rank1_9bit(u: int, v: int) -> int:
    """9-bit projective index of rank-1 matrix uv^T over F_2.
    u, v are integers 1..7 encoding nonzero vectors in F_2^3."""
    val = 0
    for i in range(3):
        for j in range(3):
            val |= (((u >> i) & 1) * ((v >> j) & 1)) << (3 * i + j)
    return val

def fano_lines() -> List[Tuple[int, int, int]]:
    """The 7 lines of PG(2,F_2): (a, b, a^b) with a < b < a^b."""
    return [(a, b, a ^ b)
            for a in range(1, 8)
            for b in range(a + 1, 8)
            if (a ^ b) > b]

def all_ruling_triples() -> List[FrozenSet[int]]:
    """All 98 ruling-line triples as frozensets of 9-bit projective indices."""
    fl = fano_lines()
    ts: set[FrozenSet[int]] = set()
    # Left ruling: fix u, vary v along a Fano line
    for u in range(1, 8):
        for v1, v2, v3 in fl:
            ts.add(frozenset([rank1_9bit(u, v1), rank1_9bit(u, v2), rank1_9bit(u, v3)]))
    # Right ruling: fix v, vary u along a Fano line
    for v in range(1, 8):
        for u1, u2, u3 in fl:
            ts.add(frozenset([rank1_9bit(u1, v), rank1_9bit(u2, v), rank1_9bit(u3, v)]))
    assert len(ts) == 98, f"Expected 98 ruling-line triples, got {len(ts)}"
    return sorted(ts, key=lambda s: tuple(sorted(s)))

def all_rank1_set() -> Set[int]:
    """All 49 rank-1 projective indices."""
    return {rank1_9bit(u, v) for u in range(1, 8) for v in range(1, 8)}

# ------------------------------------------------------------------ #
#  Wang LUT utilities                                                 #
# ------------------------------------------------------------------ #

def load_lut(path: str) -> Dict[int, int]:
    with open(path, 'rb') as f:
        payload = pickle.load(f)
    if isinstance(payload, dict) and 'lut' in payload:
        return payload['lut']
    return payload

def unpack_basis(key: int) -> List[int]:
    """Canonical Wang LUT key decoder: low 4 bits are dimension, then d 9-bit rows."""
    d = int(key) & 0xF
    vecs: List[int] = []
    r = int(key) >> 4
    for _ in range(d):
        vecs.append(r & 0x1FF)
        r >>= 9
    return vecs

def span_of(basis: List[int]) -> Set[int]:
    n = len(basis)
    s: set[int] = set()
    for m in range(1, 1 << n):
        v = 0
        for i in range(n):
            if m & (1 << i):
                v ^= basis[i]
        s.add(v)
    return s

# ------------------------------------------------------------------ #
#  Clause simplification under a prefix                              #
# ------------------------------------------------------------------ #

def simplify_ruling(triples: List[FrozenSet[int]],
                    prefix_set: Set[int]) -> dict:
    """Simplify 98 ruling-line triples under a given prefix.
    
    Every ruling-line point is in {1,...,511}, so it is either in
    prefix_set or in the candidate set.  No 'satisfied' category needed.
    """
    unit: list[int] = []
    binary: list[tuple[int, int]] = []
    ternary: list[tuple[int, int, int]] = []
    contrad = 0
    for t in triples:
        in_pf = len(t & prefix_set)
        rest = sorted(t - prefix_set)
        if in_pf == 3:
            contrad += 1
        elif in_pf == 2:
            unit.append(rest[0])
        elif in_pf == 1:
            binary.append((rest[0], rest[1]))
        else:
            ternary.append((rest[0], rest[1], rest[2]))
    return {
        'unit': sorted(set(unit)),
        'binary': sorted(set(binary)),
        'ternary': sorted(set(ternary)),
        'contradictions': contrad,
    }

# ------------------------------------------------------------------ #
#  Base graph from LUT                                                #
# ------------------------------------------------------------------ #

def build_base(lut: Dict[int, int], prefix_set: Set[int],
               var_map: Dict[int, int], lb_cutoff: int = 17):
    """Residual-0 vertex exclusions and residual-1 edge exclusions.
    
    Only scans entries with lb >= lb_cutoff for efficiency.
    Returns (vex_set_of_vars, edge_set_of_var_pairs, scanned_count, seconds).
    """
    vex: set[int] = set()
    edges: set[tuple[int, int]] = set()
    t0 = time.time()
    scanned = 0
    for key, lb in lut.items():
        if lb < lb_cutoff:
            continue
        scanned += 1
        basis = unpack_basis(key)
        sp = span_of(basis)
        pocc = len(sp & prefix_set)
        res = (20 - lb) - pocc
        if res < 0:
            continue
        cands_in = [var_map[p] for p in sp
                    if p in var_map and p not in prefix_set]
        if res == 0:
            for v in cands_in:
                vex.add(v)
        elif res == 1:
            live = [v for v in cands_in if v not in vex]
            for i in range(len(live)):
                for j in range(i + 1, len(live)):
                    a, b = live[i], live[j]
                    edges.add((min(a, b), max(a, b)))
    return vex, edges, scanned, time.time() - t0

# ------------------------------------------------------------------ #
#  CaDiCaL runner                                                     #
# ------------------------------------------------------------------ #

def run_cadical(cnf_path: str, timeout: int = 300):
    try:
        r = subprocess.run(
            ['cadical', cnf_path],
            capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout
    except subprocess.TimeoutExpired:
        return -1, ''

# ------------------------------------------------------------------ #
#  Main                                                               #
# ------------------------------------------------------------------ #

def main():
    ap = argparse.ArgumentParser(description='Ruling-line transport for Wang F2 support')
    ap.add_argument('--prefix', required=True, help='Comma-separated prefix indices')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--solve-time', type=int, default=300)
    ap.add_argument('--enumerate-only', action='store_true')
    args = ap.parse_args()

    prefix = [int(x) for x in args.prefix.split(',')]
    prefix_set = set(prefix)
    candidates = sorted(p for p in range(1, 512) if p not in prefix_set)
    cand_set = set(candidates)
    var_map = {p: i + 1 for i, p in enumerate(candidates)}
    inv_var = {v: p for p, v in var_map.items()}
    n_cands = len(candidates)
    target = 20 - len(prefix)

    out = pathlib.Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)

    # ---- Ruling-line enumeration and verification ----
    triples = all_ruling_triples()
    r1 = all_rank1_set()
    assert len(r1) == 49
    for t in triples:
        assert t <= r1, f"Triple {sorted(t)} contains non-rank-1 point"
    assert frozenset([1, 2, 3]) in triples

    rc = simplify_ruling(triples, prefix_set)

    print(f"Prefix: {prefix}  Target: {target}  Candidates: {n_cands}")
    print(f"Ruling-line: {len(rc['unit'])} unit, {len(rc['binary'])} binary, "
          f"{len(rc['ternary'])} ternary, {rc['contradictions']} contrad")

    if rc['contradictions'] > 0:
        print("PREFIX INFEASIBLE: contains a complete ruling-line triple!")
        (out / 'summary.json').write_text(json.dumps(
            {'status': 'PREFIX_INFEASIBLE', 'prefix': prefix},
            indent=2, sort_keys=True) + '\n')
        return

    # Save ruling-line analysis
    ruling_info = {
        'prefix': prefix,
        'n_triples': 98,
        'n_rank1_points': 49,
        'simplified': rc,
        'binary_detail': [
            {'points': list(pair),
             'ruling_type': 'transported from {1,2,3} exclusion'}
            for pair in rc['binary']
        ],
    }
    (out / 'ruling_lines.json').write_text(
        json.dumps(ruling_info, indent=2, sort_keys=True) + '\n')

    if args.enumerate_only:
        # Also compute graph structure on rank-1 candidates
        r1_cands = sorted(r1 - prefix_set)
        print(f"\nRank-1 candidates: {len(r1_cands)}")
        print(f"Unit exclusions: {rc['unit']}")
        print(f"Binary exclusions (pairs):")
        for a, b in rc['binary']:
            print(f"  {a} -- {b}")
        print(f"Ternary exclusions: {len(rc['ternary'])} triples")
        print(json.dumps(ruling_info, sort_keys=True))
        return

    # ---- Load LUT and build base graph ----
    print(f"\nLoading LUT {args.lut}...")
    lut = load_lut(args.lut)
    print(f"  {len(lut):,} rows")

    vex, edges, scanned, base_sec = build_base(lut, prefix_set, var_map)
    survivors_base = [p for p in candidates if var_map[p] not in vex]
    print(f"  Base graph ({base_sec:.1f}s): scanned {scanned:,}, "
          f"{len(vex)} vex, {len(edges):,} edges, {len(survivors_base)} survivors")

    # ---- Apply ruling-line vertex exclusions ----
    ruling_vex = {var_map[p] for p in rc['unit'] if p in var_map}
    new_vex = ruling_vex - vex
    vex_combined = vex | ruling_vex
    survivors_rl = [p for p in candidates if var_map[p] not in vex_combined]
    print(f"  Ruling-line unit: {len(new_vex)} NEW vertex exclusions "
          f"(total survivors {len(survivors_rl)})")

    # Active (non-redundant) ruling binary/ternary
    active_bin = [(a, b) for a, b in rc['binary']
                  if var_map[a] not in vex_combined and var_map[b] not in vex_combined]
    active_ter = [(a, b, c) for a, b, c in rc['ternary']
                  if (var_map[a] not in vex_combined and
                      var_map[b] not in vex_combined and
                      var_map[c] not in vex_combined)]
    print(f"  Active ruling binary: {len(active_bin)}, ternary: {len(active_ter)}")

    # Rank-1 survivor analysis
    r1_survivors = sorted(r1 & set(survivors_rl))
    print(f"  Rank-1 survivors: {len(r1_survivors)}")

    # ---- Build CNF ----
    clauses: list[list[int]] = []

    # Vertex exclusions (unit clauses)
    for v in sorted(vex_combined):
        clauses.append([-v])

    # Wang edge exclusions (binary clauses from residual-1)
    for a, b in sorted(edges):
        clauses.append([-a, -b])

    # Ruling-line binary clauses
    ruling_bin_clauses = 0
    for a, b in rc['binary']:
        if a in var_map and b in var_map:
            clauses.append([-var_map[a], -var_map[b]])
            ruling_bin_clauses += 1

    # Ruling-line ternary clauses
    ruling_ter_clauses = 0
    for a, b, c in rc['ternary']:
        if a in var_map and b in var_map and c in var_map:
            clauses.append([-var_map[a], -var_map[b], -var_map[c]])
            ruling_ter_clauses += 1

    # Cardinality: exactly `target` selected from survivors_rl
    surv_vars = sorted(var_map[p] for p in survivors_rl)

    from pysat.card import CardEnc, EncType
    top = n_cands
    am = CardEnc.atmost(surv_vars, target, top_id=top, encoding=EncType.seqcounter)
    if am:
        top = max(abs(l) for c in am for l in c)
    al = CardEnc.atleast(surv_vars, target, top_id=top, encoding=EncType.seqcounter)
    if al:
        top = max(abs(l) for c in al for l in c)
    clauses.extend(am)
    clauses.extend(al)

    n_vars = top
    n_clauses = len(clauses)

    cnf_path = out / 'augmented_base.cnf'
    with open(cnf_path, 'w') as f:
        f.write(f'p cnf {n_vars} {n_clauses}\n')
        for cl in clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
    print(f"\n  CNF: {n_vars} vars, {n_clauses:,} clauses -> {cnf_path}")
    print(f"    (includes {ruling_bin_clauses} ruling binary, {ruling_ter_clauses} ruling ternary)")

    # ---- Solve ----
    print(f"  Solving with CaDiCaL ({args.solve_time}s timeout)...")
    t0 = time.time()
    ec, stdout = run_cadical(str(cnf_path), args.solve_time)
    solve_sec = time.time() - t0

    model = None
    violations = max_excess = None
    r1_in_model: list[int] = []

    if ec == 10:
        status = 'SAT'
        model = set()
        for line in stdout.splitlines():
            if line.startswith('v '):
                for lit in line[2:].split():
                    vi = int(lit)
                    if 0 < vi <= n_cands:
                        model.add(candidates[vi - 1])
        # Full LUT scan
        full_support = prefix_set | model
        violations = max_excess = 0
        for key, lb in lut.items():
            sp = span_of(unpack_basis(key))
            occ = len(sp & full_support)
            cap = 20 - lb
            if occ > cap:
                violations += 1
                max_excess = max(max_excess, occ - cap)
        r1_in_model = sorted(model & r1)
        print(f"  SAT ({solve_sec:.1f}s): {len(model)} selected, "
              f"|support|={len(full_support)}, violations={violations}, "
              f"max_excess={max_excess}, rank1_in_model={len(r1_in_model)}")
    elif ec == 20:
        status = 'UNSAT'
        print(f"  UNSAT ({solve_sec:.1f}s)!")
    else:
        status = 'UNKNOWN'
        print(f"  UNKNOWN ec={ec} ({solve_sec:.1f}s)")

    # ---- Also build and solve WITHOUT ruling-line clauses for comparison ----
    # (only base graph + cardinality)
    plain_clauses: list[list[int]] = []
    for v in sorted(vex):
        plain_clauses.append([-v])
    for a, b in sorted(edges):
        plain_clauses.append([-a, -b])
    surv_vars_plain = sorted(var_map[p] for p in survivors_base)
    top2 = n_cands
    am2 = CardEnc.atmost(surv_vars_plain, target, top_id=top2, encoding=EncType.seqcounter)
    if am2:
        top2 = max(abs(l) for c in am2 for l in c)
    al2 = CardEnc.atleast(surv_vars_plain, target, top_id=top2, encoding=EncType.seqcounter)
    if al2:
        top2 = max(abs(l) for c in al2 for l in c)
    plain_clauses.extend(am2)
    plain_clauses.extend(al2)

    plain_cnf_path = out / 'plain_base.cnf'
    with open(plain_cnf_path, 'w') as f:
        f.write(f'p cnf {top2} {len(plain_clauses)}\n')
        for cl in plain_clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')

    print(f"\n  Plain base CNF: {top2} vars, {len(plain_clauses):,} clauses -> {plain_cnf_path}")
    print(f"  Solving plain base...")
    t0 = time.time()
    ec2, stdout2 = run_cadical(str(plain_cnf_path), args.solve_time)
    solve_sec2 = time.time() - t0

    plain_model = None
    plain_violations = plain_max_excess = None
    r1_in_plain = []

    if ec2 == 10:
        plain_status = 'SAT'
        plain_model = set()
        for line in stdout2.splitlines():
            if line.startswith('v '):
                for lit in line[2:].split():
                    vi = int(lit)
                    if 0 < vi <= n_cands:
                        plain_model.add(candidates[vi - 1])
        full_plain = prefix_set | plain_model
        plain_violations = plain_max_excess = 0
        for key, lb in lut.items():
            sp = span_of(unpack_basis(key))
            occ = len(sp & full_plain)
            cap = 20 - lb
            if occ > cap:
                plain_violations += 1
                plain_max_excess = max(plain_max_excess, occ - cap)
        r1_in_plain = sorted(plain_model & r1)
        print(f"  Plain SAT ({solve_sec2:.1f}s): {len(plain_model)} selected, "
              f"violations={plain_violations}, rank1={len(r1_in_plain)}")
    elif ec2 == 20:
        plain_status = 'UNSAT'
        print(f"  Plain UNSAT ({solve_sec2:.1f}s)!")
    else:
        plain_status = 'UNKNOWN'
        print(f"  Plain UNKNOWN ec={ec2} ({solve_sec2:.1f}s)")

    # ---- Save summary ----
    result = {
        'prefix': prefix,
        'target': target,
        'n_candidates': n_cands,
        'base_graph': {
            'n_vex': len(vex),
            'n_edges': len(edges),
            'n_survivors': len(survivors_base),
            'build_sec': round(base_sec, 2),
        },
        'ruling_line': {
            'n_unit': len(rc['unit']),
            'unit_points': rc['unit'],
            'n_binary': len(rc['binary']),
            'n_binary_active': len(active_bin),
            'n_ternary': len(rc['ternary']),
            'n_ternary_active': len(active_ter),
            'new_vex': len(new_vex),
            'survivors_after': len(survivors_rl),
            'rank1_survivors': len(r1_survivors),
        },
        'augmented_cnf': {
            'n_vars': n_vars,
            'n_clauses': n_clauses,
            'status': status,
            'solve_sec': round(solve_sec, 2),
            'model_size': len(model) if model else None,
            'violations': violations,
            'max_excess': max_excess,
            'rank1_in_model': r1_in_model,
            'rank1_count': len(r1_in_model),
        },
        'plain_cnf': {
            'n_vars': top2,
            'n_clauses': len(plain_clauses),
            'status': plain_status,
            'solve_sec': round(solve_sec2, 2),
            'model_size': len(plain_model) if plain_model else None,
            'violations': plain_violations,
            'max_excess': plain_max_excess,
            'rank1_in_model': r1_in_plain,
            'rank1_count': len(r1_in_plain),
        },
    }
    (out / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f"\n{json.dumps(result, sort_keys=True)}")


if __name__ == '__main__':
    main()
