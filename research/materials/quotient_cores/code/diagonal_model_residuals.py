#!/usr/bin/env python3
"""
analysis: enumerate diagonal-collapse models and inspect symmetric residuals.

For m=4 (or another m) satisfying the 120 diagonal-collapse conditions, extract
primary orbit variables from SAT models and compute the residual
    R = T333 + sum orbit(U,V,W)
in the cyclic-invariant coordinate system.  If the degree-3 quotient constraints
hold then R lies in Sym^3(F_2^9); this script maps it to the 165 symmetric
monomial coordinates and measures cheap invariants relevant to Waring decoding:
Hamming weight, diagonal ANF degrees, and whether the residual can be represented
by <=4 cubes by a meet-in-the-middle decoder (useful for f=4 at m=6, and as a
sanity bound for other m).

The enumeration is bounded and is not an exhaustive decision unless the solver
reports exhaustion.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "diagonal_collapse"
N = 9

import sys
sys.path.insert(0, str(SCRIPT_DIR))
import f2_diagonal_collapse as diag


def cyclic_reps():
    return diag.cyclic_orbit_reps()


def sym_monomial_reps():
    reps = []
    # multisets i<=j<=k; dimension C(9+3-1,3)=165
    for i in range(N):
        for j in range(i, N):
            for k in range(j, N):
                reps.append((i, j, k))
    return reps


def orbit_value(U,V,W,i,j,k):
    return (U[i] & V[j] & W[k]) ^ (V[i] & W[j] & U[k]) ^ (W[i] & U[j] & V[k])


def build_residual_cyclic(orbits):
    T = diag.build_T333(); reps = cyclic_reps(); out = {}
    for r in reps:
        i,j,k = r
        val = T[i][j][k]
        for U,V,W in orbits:
            val ^= orbit_value(U,V,W,i,j,k)
        out[r] = val
    return out


def symmetrize_from_cyclic(cyc):
    """Return (is_symmetric, sym_coords, first_bad_pair)."""
    sym_reps = sym_monomial_reps()
    coords = []
    for rep in sym_reps:
        vals = []
        for p in set(itertools.permutations(rep, 3)):
            # reduce to cyclic representative for coordinate lookup
            orb = [p, (p[1],p[2],p[0]), (p[2],p[0],p[1])]
            cr = min(orb)
            vals.append(cyc[cr])
        if any(v != vals[0] for v in vals):
            return False, [], {"monomial": rep, "values": vals}
        coords.append(vals[0])
    return True, coords, None


def cube_sym_columns():
    reps = sym_monomial_reps()
    cols = []
    for mask in range(1, 1 << N):
        val = 0
        bits = [(mask >> i) & 1 for i in range(N)]
        for t, (i,j,k) in enumerate(reps):
            if bits[i] & bits[j] & bits[k]:
                val |= 1 << t
        cols.append((mask, val))
    return cols


def coords_to_int(coords):
    x = 0
    for i,b in enumerate(coords):
        if b: x |= 1 << i
    return x


def min_rank_le4(target_int, cols):
    """Return a representation of weight <=4 if it exists, else None."""
    if target_int == 0:
        return []
    col_dict = {v: [m] for m,v in cols}
    if target_int in col_dict:
        return col_dict[target_int]
    # two-sums
    sums: Dict[int, Tuple[int,int]] = {}
    n = len(cols)
    for a in range(n):
        ma, va = cols[a]
        for b in range(a+1, n):
            vb = va ^ cols[b][1]
            if vb not in sums:
                sums[vb] = (ma, cols[b][0])
    if target_int in sums:
        return list(sums[target_int])
    # weight 3: col + twosum
    for m,v in cols:
        need = target_int ^ v
        if need in sums:
            rep = [m] + list(sums[need])
            if len(set(rep)) == len(rep):
                return rep
    # weight 4: twosum + twosum
    for s, pair in sums.items():
        need = target_int ^ s
        if need in sums:
            rep = list(pair) + list(sums[need])
            # If repeated cube appears twice it cancels; this may reduce rank.  Accept only distinct.
            if len(set(rep)) == len(rep):
                return rep
    return None


def parse_model(stdout):
    assign = {}
    for line in stdout.splitlines():
        if line.startswith('v '):
            for tok in line[2:].split():
                lit = int(tok)
                if lit == 0: continue
                assign[abs(lit)] = 1 if lit > 0 else 0
    return assign


def primary_orbits_from_assign(assign, vmap, m):
    orbits=[]
    for o in range(m):
        U=[assign.get(vmap['U'][o][i],0) for i in range(N)]
        V=[assign.get(vmap['V'][o][i],0) for i in range(N)]
        W=[assign.get(vmap['W'][o][i],0) for i in range(N)]
        orbits.append((U,V,W))
    return orbits


def add_blocking_clause(cnf_path: Path, vars_vals: List[Tuple[int,int]], tmp_path: Path):
    lines = cnf_path.read_text().splitlines()
    header = lines[0].split()
    nv = int(header[2]); nc = int(header[3])
    block = []
    for var,val in vars_vals:
        block.append(-var if val else var)
    lines[0] = f"p cnf {nv} {nc+1}"
    lines.append(" ".join(map(str, block)) + " 0")
    tmp_path.write_text("\n".join(lines) + "\n")


def run_kissat(cnf, timeout):
    try:
        r = subprocess.run(['kissat', str(cnf)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', '', None
    if r.returncode == 10:
        return 'SAT', r.stdout, r.returncode
    if r.returncode == 20:
        return 'UNSAT', r.stdout, r.returncode
    return 'UNKNOWN', r.stdout + r.stderr, r.returncode


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--m', type=int, default=4)
    ap.add_argument('--models', type=int, default=100)
    ap.add_argument('--timeout', type=int, default=60)
    args=ap.parse_args()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    anf=diag.trM3_anf()
    targets={}
    for d in (2,3):
        for tup in itertools.combinations(range(N), d):
            mask=diag.mask_from_tuple(tup)
            targets[mask]=anf.get(mask,0)
    enc,vmap=diag.encode_diagonal(args.m, targets, sym_break=True)
    cnf=DATA_DIR / f'diag_highdeg_m{args.m}_enumerate_base.cnf'
    enc.write_dimacs(cnf)
    primary=[]
    for o in range(args.m):
        for arrname in ('U','V','W'):
            primary.extend(vmap[arrname][o])
    cols=cube_sym_columns()
    cur=cnf
    recs=[]
    exhausted=False
    for t in range(args.models):
        st,out,rc=run_kissat(cur,args.timeout)
        print(f"model {t}: {st}")
        if st!='SAT':
            exhausted=(st=='UNSAT')
            recs.append({'iteration':t,'status':st,'returncode':rc})
            break
        assign=parse_model(out)
        orbits=primary_orbits_from_assign(assign,vmap,args.m)
        cyc=build_residual_cyclic(orbits)
        ok,coords,bad=symmetrize_from_cyclic(cyc)
        assert ok, bad
        target=coords_to_int(coords)
        rep4=min_rank_le4(target,cols)
        # diagonal ANF of residual by evaluating polynomial on Boolean diagonal from tensor coords.
        hw=sum(coords)
        rec={'iteration':t,'status':'SAT','sym_hw':hw,'rank_le4': rep4 is not None,
             'rank_le4_rep': rep4[:8] if rep4 is not None else None,
             'nonzero_orbits':sum(1 for U,V,W in orbits if any(U) or any(V) or any(W)),
             'orbits':[[U,V,W] for U,V,W in orbits]}
        recs.append(rec)
        # block this primary orbit assignment only; auxiliary can differ.
        vars_vals=[(var,assign.get(var,0)) for var in primary]
        nxt=DATA_DIR / f'diag_highdeg_m{args.m}_enumerate_block_{t+1}.cnf'
        add_blocking_clause(cur, vars_vals, nxt)
        cur=nxt
    summary={'m':args.m,'requested_models':args.models,'exhausted':exhausted,
             'records':recs}
    outp=DATA_DIR / f'diag_m{args.m}_model_residuals.json'
    outp.write_text(json.dumps(summary,indent=2)+'\n')
    print(f"Saved {outp}")

if __name__=='__main__':
    main()
