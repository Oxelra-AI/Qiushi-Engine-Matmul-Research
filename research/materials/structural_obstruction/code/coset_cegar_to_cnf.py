#!/usr/bin/env python3
"""Export the final active CEGAR model from surviving_coset_ansatz.py to CNF.

The active model is: choose 16 rank-one A-directions among a precomputed allowed
set for a fixed high-rank coset set H; enforce row/column caps and the full-Wang
rows that were added by the CEGAR loop.  This script reconstructs those active
constraints from a cegar_result.json and writes a SAT CNF with simple exact-one /
at-most constraints.  An UNSAT solver proof for this CNF certifies only the
active-row closure of the normalized ansatz, not by itself the global theorem.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Sequence

SCRIPT = Path(__file__).resolve().parent
import sys
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from surviving_coset_ansatz import load_lut, analyze_H, canonical_coset_points, rank_one_uv_map, iter_wang_rows  # type: ignore


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []

    def new_var(self) -> int:
        self.nv += 1
        return self.nv

    def add_clause(self, c: Sequence[int]):
        self.clauses.append([int(x) for x in c])

    def add_at_most(self, lits: Sequence[int], k: int):
        lits = list(lits)
        if k < 0:
            self.add_clause([])
        elif k >= len(lits):
            return
        elif k == 0:
            for x in lits:
                self.add_clause([-x])
        else:
            # Pair/subset encoding is tiny here: at most 43 variables and row supports are small in active rows.
            for S in combinations(lits, k + 1):
                self.add_clause([-x for x in S])

    def add_at_least(self, lits: Sequence[int], k: int):
        lits = list(lits)
        n = len(lits)
        if k <= 0:
            return
        if k > n:
            self.add_clause([])
            return
        # at least k is at most n-k false: for every subset of size n-k+1, one is true.
        for S in combinations(lits, n - k + 1):
            self.add_clause(list(S))

    def add_exactly(self, lits: Sequence[int], k: int):
        self.add_at_most(lits, k)
        self.add_at_least(lits, k)

    def write(self, path: Path, comments: Sequence[str] = ()): 
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as f:
            for c in comments:
                f.write(f"c {c}\n")
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def reconstruct_hrec(lut_path: Path, H: Sequence[int]) -> Dict:
    lut = load_lut(lut_path)
    return analyze_H(lut, H, canonical_coset_points()[0])


def build_active_cnf(cegar: Dict, lut_path: Path, binary: Path, out_cnf: Path) -> Dict:
    H = [int(x) for x in cegar['H']]
    H_mask = sum(1 << h for h in H)
    hrec = reconstruct_hrec(lut_path, H)
    allowed = [int(x) for x in hrec['allowed_rank_one']]
    uv = rank_one_uv_map()

    F = CNF()
    var = {x: F.new_var() for x in allowed}
    F.add_exactly([var[x] for x in allowed], 16)
    base_clause_count = len(F.clauses)
    for u in range(1, 8):
        xs = [var[x] for x in allowed if uv[x][0] == u]
        F.add_at_most(xs, 5)
    for v in range(1, 8):
        xs = [var[x] for x in allowed if uv[x][1] == v]
        F.add_at_most(xs, 5)
    cap_clause_count = len(F.clauses) - base_clause_count

    row_indices = []
    for rd in cegar['rounds']:
        scan = rd.get('scan_summary')
        # The cegar_result intentionally saved only summaries, not row masks.
        # Recover active rows by re-scanning final supports in the round order is impossible from summary alone.
        # Instead use the support sets to find their first add_per_round violations exactly as the original did.
        if 'support' not in rd:
            continue
        support_mask = sum(1 << int(x) for x in rd['support'])
        add_limit = int(cegar['parameters']['add_per_round'])
        added = 0
        for idx, cap, dim, rowmask in iter_wang_rows(binary):
            occ = (rowmask & (H_mask | support_mask)).bit_count()
            if occ > cap:
                row_indices.append(int(idx))
                added += 1
                if added >= add_limit:
                    break
    # Deduplicate, preserving order.
    seen = set(); row_indices_unique = []
    for i in row_indices:
        if i not in seen:
            seen.add(i); row_indices_unique.append(i)

    # Re-scan binary once and add these rows.
    wanted = set(row_indices_unique)
    rows_added = 0
    row_support_hist = {}
    for idx, cap, dim, rowmask in iter_wang_rows(binary):
        if idx not in wanted:
            continue
        rhs = int(cap) - (rowmask & H_mask).bit_count()
        pts = [x for x in allowed if (rowmask >> x) & 1]
        F.add_at_most([var[x] for x in pts], rhs)
        row_support_hist[len(pts)] = row_support_hist.get(len(pts), 0) + 1
        rows_added += 1
        if rows_added == len(wanted):
            break

    F.write(out_cnf, comments=[
        'surviving coset ansatz active CEGAR CNF',
        'H=' + ','.join(map(str, H)),
        'allowed=' + ','.join(map(str, allowed)),
        'variables correspond to allowed rank-one directions in listed order',
    ])
    return {
        'schema': 'coset_cegar_active_cnf_v1',
        'H': H,
        'allowed_rank_one': allowed,
        'allowed_count': len(allowed),
        'target': 16,
        'row_indices_count_raw': len(row_indices),
        'row_indices_count_unique': len(row_indices_unique),
        'rows_added': rows_added,
        'cnf_vars': F.nv,
        'cnf_clauses': len(F.clauses),
        'base_clause_count': base_clause_count,
        'line_cap_clause_count': cap_clause_count,
        'active_wang_clause_count': len(F.clauses) - base_clause_count - cap_clause_count,
        'row_support_hist': dict(sorted(row_support_hist.items())),
        'cnf_path': str(out_cnf),
    }


def run_solver(cnf: Path, proof: Path | None, solver_timeout: int) -> Dict:
    cmd = ['cadical', '-n', '-t', str(solver_timeout), str(cnf)]
    if proof is not None:
        proof.parent.mkdir(parents=True, exist_ok=True)
        cmd.append(str(proof))
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=solver_timeout + 30)
    return {
        'command': cmd,
        'returncode': proc.returncode,
        'elapsed_sec': time.time() - t0,
        'sat': False if proc.returncode == 20 else True if proc.returncode == 10 else None,
        'stdout_tail': '\n'.join(proc.stdout.splitlines()[-80:]),
        'stderr_tail': '\n'.join(proc.stderr.splitlines()[-80:]),
        'proof_path': str(proof) if proof else None,
        'proof_size': proof.stat().st_size if proof is not None and proof.exists() else None,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cegar', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--binary', type=Path, default=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'))
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--timeout', type=int, default=60)
    ap.add_argument('--with-proof', action='store_true')
    args = ap.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    cegar = json.loads(args.cegar.read_text())
    cnf = args.outdir / 'active_cegar.cnf'
    info = build_active_cnf(cegar, args.lut, args.binary, cnf)
    proof = args.outdir / 'active_cegar.drat' if args.with_proof else None
    sol = run_solver(cnf, proof, args.timeout)
    result = {'encoding': info, 'solver': sol}
    out = args.outdir / 'active_cegar_result.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(out), 'sat': sol['sat'], 'returncode': sol['returncode'], 'cnf_vars': info['cnf_vars'], 'cnf_clauses': info['cnf_clauses'], 'proof_size': sol['proof_size'], 'elapsed_sec': sol['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
