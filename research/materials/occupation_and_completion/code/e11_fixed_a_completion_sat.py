#!/usr/bin/env python3
"""Fixed-A completion SAT for the E11 core over F2.

Given 19 fixed quotient A masks u_t, solve for B/C masks v_t,w_t such that
    XOR_{t: u_t[s]=1} v_t[b] w_t[c] = core[s,b,c]
for all 8*9*9 entries.  This is the exact B/C completion problem for one
A-list.  A SAT result is independently reconstructed and lifted by the E11
bridge; an UNSAT result is only a local fixed-A exclusion unless accompanied by
a proof certificate.

The script also has a mode to generate same-W two-deletion near-miss supports
from the rank-21 pool and test those surviving shadow + purity-side support
filters.  That family is a local construction probe, not a global support cover.
"""
from __future__ import annotations

import argparse
import collections
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import e11_shadow_filter as shadow  # noqa: E402
import e11_purity_2sat_filter as purity  # noqa: E402


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def build_core() -> np.ndarray:
    return build_t333()[1:9].copy()


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def reconstruct(terms: List[Tuple[int, int, int]], dims=(8, 9, 9)) -> np.ndarray:
    T = np.zeros(dims, dtype=np.uint8)
    for u, v, w in terms:
        T ^= (vec_from_mask(u, dims[0]).reshape(-1, 1, 1)
              * vec_from_mask(v, dims[1]).reshape(1, -1, 1)
              * vec_from_mask(w, dims[2]).reshape(1, 1, -1)).astype(np.uint8)
    return T


def lift_to_full(terms: List[Tuple[int, int, int]]) -> List[Tuple[int, int, int]]:
    return [(u << 1, v, w) for u, v, w in terms] + [(1, 1, 1), (1, 2, 2), (1, 4, 4)]


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []
    def new_var(self) -> int:
        self.nv += 1
        return self.nv
    def add(self, clause: Sequence[int]):
        self.clauses.append([int(x) for x in clause])
    def add_and2(self, out: int, a: int, b: int):
        self.add([-out, a]); self.add([-out, b]); self.add([out, -a, -b])
    def add_xor2(self, out: int, a: int, b: int):
        self.add([-a, -b, -out])
        self.add([-a, b, out])
        self.add([a, -b, out])
        self.add([a, b, -out])
    def add_xor_eq(self, xs: Sequence[int], rhs: int):
        xs = list(xs); rhs = int(rhs) & 1
        if not xs:
            if rhs:
                self.add([])
            return
        if len(xs) == 1:
            self.add([xs[0] if rhs else -xs[0]])
            return
        acc = self.new_var()
        self.add_xor2(acc, xs[0], xs[1])
        for x in xs[2:]:
            y = self.new_var()
            self.add_xor2(y, acc, x)
            acc = y
        self.add([acc if rhs else -acc])
    def write(self, path: Path, comments: Sequence[str] = ()): 
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as f:
            for c in comments:
                f.write(f'c {c}\n')
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for cl in self.clauses:
                f.write(' '.join(str(x) for x in cl) + ' 0\n')


def build_fixed_a_cnf(us: Sequence[int], add_cap3_purity: bool = True, add_half_purity_branch: Optional[Dict[str, bool]] = None) -> Tuple[CNF, dict]:
    """Build fixed-A CNF.  Currently only Brent equations plus optional cap3 purity.

    add_half_purity_branch is reserved for future explicit side assignments.
    """
    R = len(us)
    core = build_core()
    F = CNF()
    V = [[F.new_var() for b in range(9)] for t in range(R)]
    W = [[F.new_var() for c in range(9)] for t in range(R)]
    P = {}
    for t in range(R):
        for b in range(9):
            for c in range(9):
                q = F.new_var(); P[(t,b,c)] = q
                F.add_and2(q, V[t][b], W[t][c])

    # Optional cap-3 purity units from the theorem, useful propagation for fixed-A.
    cap3_units = 0
    if add_cap3_purity:
        group = [7, 56, 448]
        for s in range(8):
            active = [t for t,u in enumerate(us) if (int(u) >> s) & 1]
            if len(active) == 3:
                j_s, i_s = purity.SLICE_BLOCKS[s]
                for t in active:
                    for b in range(9):
                        if not ((group[j_s] >> b) & 1):
                            F.add([-V[t][b]]); cap3_units += 1
                    for c in range(9):
                        if not ((group[i_s] >> c) & 1):
                            F.add([-W[t][c]]); cap3_units += 1

    xor_terms_total = 0
    for s in range(8):
        active = [t for t,u in enumerate(us) if (int(u) >> s) & 1]
        for b in range(9):
            for c in range(9):
                xs = [P[(t,b,c)] for t in active]
                xor_terms_total += len(xs)
                F.add_xor_eq(xs, int(core[s,b,c]))
    meta = {
        'rank': R,
        'u_masks': [int(u) for u in us],
        'caps': purity.support_capacities(us),
        'total_a_weight': sum(int(u).bit_count() for u in us),
        'num_vars': F.nv,
        'num_clauses': len(F.clauses),
        'v_vars': R*9,
        'w_vars': R*9,
        'product_vars': R*81,
        'cap3_purity_units': cap3_units,
        'xor_terms_total': xor_terms_total,
        'semantics': 'fixed A masks; variables are v_t,w_t and q_tbc=v_tb&w_tc; XOR over active terms equals E11 core entry',
    }
    return F, meta


def parse_solver_output(text: str) -> Tuple[str, Dict[int,int]]:
    status = 'UNKNOWN'
    assign: Dict[int,int] = {}
    for line in text.splitlines():
        if line.startswith('s '):
            if 'SATISFIABLE' in line and 'UNSATISFIABLE' not in line:
                status = 'SAT'
            elif 'UNSATISFIABLE' in line:
                status = 'UNSAT'
            elif 'UNKNOWN' in line:
                status = 'UNKNOWN'
        elif line.startswith('v'):
            for tok in line.split()[1:]:
                lit = int(tok)
                if lit == 0:
                    continue
                assign[abs(lit)] = 1 if lit > 0 else 0
    return status, assign


def solve_cnf(cnf_path: Path, timeout_sec: float) -> Tuple[str, str, float, Optional[int]]:
    t0 = time.time()
    try:
        proc = subprocess.run(['cadical', str(cnf_path)], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout_sec)
        elapsed = time.time() - t0
        status, _ = parse_solver_output(proc.stdout)
        return status, proc.stdout + ('\n[stderr]\n' + proc.stderr if proc.stderr else ''), elapsed, proc.returncode
    except subprocess.TimeoutExpired as e:
        elapsed = time.time() - t0
        out = (e.stdout or '')
        if isinstance(out, bytes):
            out = out.decode(errors='replace')
        err = (e.stderr or '')
        if isinstance(err, bytes):
            err = err.decode(errors='replace')
        return 'TIMEOUT', out + ('\n[stderr]\n' + err if err else ''), elapsed, None


def decode_assignment(us: Sequence[int], assign: Dict[int,int]) -> List[Tuple[int,int,int]]:
    R = len(us)
    terms = []
    # variable order V then W then P, so V[t][b]=t*9+b+1; W starts R*9+1
    for t,u in enumerate(us):
        v = 0; w = 0
        for b in range(9):
            if assign.get(t*9 + b + 1, 0):
                v |= 1 << b
        w_base = R*9
        for c in range(9):
            if assign.get(w_base + t*9 + c + 1, 0):
                w |= 1 << c
        terms.append((int(u), v, w))
    return terms


def verify_terms(terms: List[Tuple[int,int,int]]) -> dict:
    core_diff = int(np.sum(reconstruct(terms, (8,9,9)) ^ build_core()))
    full_terms = lift_to_full(terms)
    full_diff = int(np.sum(reconstruct(full_terms, (9,9,9)) ^ build_t333()))
    return {
        'core_diff_count': core_diff,
        'core_verified': core_diff == 0,
        'full_lift_rank': len(full_terms),
        'full_diff_count': full_diff,
        'full_verified': full_diff == 0,
        'strict_nonzero_terms': sum(1 for u,v,w in terms if u and v and w),
    }


def bitrow(row: Sequence[int]) -> int:
    x = 0
    for i,b in enumerate(row):
        if int(b)&1:
            x |= 1<<i
    return x


def rank_int(rows: Iterable[int]) -> int:
    basis={}; r=0
    for x0 in rows:
        x=int(x0)
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else:
                basis[p]=x; r+=1; break
    return r


def consistent_int(rows: List[int], rhs: List[int], nvars: int):
    rA=rank_int(rows)
    rB=rank_int([row | ((int(b)&1)<<nvars) for row,b in zip(rows,rhs)])
    return rA==rB,rA,rB


def shadow_summary_for_support(us: List[int], inv_lams: List[int]) -> dict:
    nvars=9*len(us)
    tensor_rows,tensor_rhs=shadow.build_tensor_shadow_rows(us)
    tight=[lam for lam in inv_lams if sum(shadow.dot8(lam,u) for u in us)==9]
    rows=[bitrow(r) for r in tensor_rows]; rhs=list(tensor_rhs)
    for lam in tight:
        tr,tb=shadow.add_trace_rows(us,[lam],transpose_coeff=False)
        rows.extend(bitrow(r) for r in tr); rhs.extend(tb)
    ok,rA,rB=consistent_int(rows,rhs,nvars)
    return {'ok':ok,'rank':rA,'aug_rank':rB,'tight_count':len(tight),'tight':tight}


def same_w_deletion_supports(pool_path: Path, max_supports: Optional[int] = None) -> List[dict]:
    pool = np.load(pool_path)
    inv_lams = shadow.invertible_lambda_masks()
    out=[]; seen=set(); total=0
    for idx,row in enumerate(pool):
        terms=[(int(row[3*t]),int(row[3*t+1]),int(row[3*t+2])) for t in range(len(row)//3)]
        groups=collections.defaultdict(list)
        for t,(_u,_v,w) in enumerate(terms):
            groups[w].append(t)
        for w,inds in groups.items():
            for aa in range(len(inds)):
                for bb in range(aa+1,len(inds)):
                    total += 1
                    rem=[terms[t] for t in range(len(terms)) if t not in (inds[aa],inds[bb])]
                    us=[u for u,_v,_w in rem]
                    key=tuple(sorted(us))
                    if key in seen:
                        continue
                    seen.add(key)
                    sh=shadow_summary_for_support(us,inv_lams)
                    if not sh['ok']:
                        continue
                    pur=purity.build_purity_clauses(us,extended=True)
                    if pur['rejects_support']:
                        continue
                    out.append({'source':'same_w_deletion','pool_row':idx,'deleted_terms':[inds[aa],inds[bb]],'deleted_w':int(w),'u_masks':us,'shadow':{k:sh[k] for k in ['ok','rank','aug_rank','tight_count','tight']},'purity':{k:pur[k] for k in ['caps','total_weight','twosat_sat','rejects_support','n_clauses']}})
                    if max_supports and len(out)>=max_supports:
                        return out
    return out


def run_batch(args):
    supports = same_w_deletion_supports(args.pool, args.max_supports)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    results=[]
    t0=time.time()
    for idx,sup in enumerate(supports):
        us=sup['u_masks']
        cnf,meta=build_fixed_a_cnf(us, add_cap3_purity=not args.no_cap3_purity)
        cnf_path=args.out_dir/f'fixedA_{idx:03d}.cnf'
        log_path=args.out_dir/f'fixedA_{idx:03d}.cadical.log'
        cnf.write(cnf_path, comments=[f'fixed-A support index {idx}', json.dumps({k:sup[k] for k in sup if k!="u_masks"})[:500]])
        status,out,elapsed,rc=solve_cnf(cnf_path,args.timeout)
        log_path.write_text(out)
        rec={'index':idx,'support_record':sup,'cnf':str(cnf_path),'log':str(log_path),'cnf_meta':meta,'solver_status':status,'returncode':rc,'solve_sec':round(elapsed,3)}
        if status=='SAT':
            _,assign=parse_solver_output(out)
            terms=decode_assignment(us,assign)
            ver=verify_terms(terms)
            rec['decoded_terms']=[list(t) for t in terms]
            rec['verification']=ver
            if ver['core_verified']:
                wit=args.out_dir/f'fixedA_{idx:03d}_witness.npz'
                np.savez_compressed(wit,
                    u_masks=np.array([u for u,_v,_w in terms],dtype=np.uint16),
                    v_masks=np.array([v for _u,v,_w in terms],dtype=np.uint16),
                    w_masks=np.array([w for _u,_v,w in terms],dtype=np.uint16),
                    terms=np.array([x for term in terms for x in term],dtype=np.uint16),
                    full_terms=np.array([x for term in lift_to_full(terms) for x in term],dtype=np.uint16))
                rec['witness_npz']=str(wit)
        results.append(rec)
        print(json.dumps({'idx':idx,'status':status,'solve_sec':round(elapsed,3),'vars':meta['num_vars'],'clauses':meta['num_clauses'],'caps':meta['caps'],'weight':meta['total_a_weight']},sort_keys=True), flush=True)
        if status=='SAT' and rec.get('verification',{}).get('core_verified'):
            break
    summary={
        'purpose':'fixed-A exact B/C completion SAT on shadow+purity surviving same-W deletion supports',
        'pool':str(args.pool),
        'supports_generated':len(supports),
        'supports_tested':len(results),
        'timeout_per_support_sec':args.timeout,
        'status_hist':dict(collections.Counter(r['solver_status'] for r in results)),
        'sat_verified': [r for r in results if r.get('verification',{}).get('core_verified')],
        'results_head':results[:20],
        'all_results':results if args.store_all else None,
        'interpretation':'A SAT verified core is a rank-19 E11 witness and lifts to full rank 22. UNSAT/TIMEOUT results are local fixed-A evidence; without proof logs, UNSAT is not a final theorem.',
        'elapsed_sec':round(time.time()-t0,3),
    }
    args.summary.parent.mkdir(parents=True,exist_ok=True)
    args.summary.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'summary':str(args.summary),'supports_generated':len(supports),'supports_tested':len(results),'status_hist':summary['status_hist'],'sat_verified_count':len(summary['sat_verified']),'elapsed_sec':summary['elapsed_sec']},indent=2,sort_keys=True))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pool',type=Path,default=Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy'))
    ap.add_argument('--out-dir',type=Path,default=Path('data/fixed_a_completion/same_w_shadow_purity'))
    ap.add_argument('--summary',type=Path,default=Path('data/fixed_a_completion/same_w_shadow_purity_summary.json'))
    ap.add_argument('--max-supports',type=int,default=5)
    ap.add_argument('--timeout',type=float,default=10.0)
    ap.add_argument('--store-all',action='store_true')
    ap.add_argument('--no-cap3-purity',action='store_true')
    args=ap.parse_args()
    run_batch(args)


if __name__=='__main__':
    main()
