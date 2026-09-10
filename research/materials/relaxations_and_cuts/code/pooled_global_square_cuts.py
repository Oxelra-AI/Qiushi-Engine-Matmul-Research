#!/usr/bin/env python3
"""analysis: Pooled exact global square cuts from integer PSD failures.

For any actual 19-point support, the orbit-averaged moment matrix M ≽ 0.
For any integer vector v, v^T M v ≥ 0 gives a linear inequality in (n_a, m_j).
We extract these from PSD-failing integer pair-count matrices, express them
as global cuts valid for ALL count vectors, pool them, and test whether
they exclude remaining count branches at integer pair-count level.

The global cut form: multiply v^T M v by 1152 (= |G|, divisible by all orbit sizes)
to get integer coefficients:
  1152·v₀² + Σ_a (1152/|O_a|)·(2v₀S_a + Q_a)·n_a + Σ_j (1152/|P_j|)·R_j·m_j ≥ 0
where S_a = Σ_{p∈O_a} v_{p+1}, Q_a = Σ_{p∈O_a} v_{p+1}², R_j = Σ_{{p,q}∈P_j} 2v_{p+1}v_{q+1}.
"""
import json, time, sys, os, pickle
import numpy as np
from pathlib import Path
from fractions import Fraction
from itertools import product as iproduct
from collections import defaultdict

t_start = time.time()
WS = Path(__file__).resolve().parent.parent
DATA = WS / "data"
OUT = DATA / "pooled_square_cuts"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(WS / "scripts"))

print("analysis: Pooled exact global square cuts", flush=True)

# ═══════════════════════════════════════════════════════════════════════════
# Phase 1: Infrastructure (from analysis pattern)
# ═══════════════════════════════════════════════════════════════════════════
print("  Phase 1: Build infrastructure", flush=True)
t1 = time.time()

N = 255

def _int_to_mat(p):
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            k = 3*i+j
            if k == 0: continue
            M[i,j] = (p >> (k-1)) & 1
    return M

_MATS = [_int_to_mat(p) for p in range(256)]

def _mat_to_int(M):
    p = 0
    for i in range(3):
        for j in range(3):
            k = 3*i+j
            if k == 0: continue
            if int(M[i,j]) % 2: p |= 1 << (k-1)
    return p

def _gl3f2_stab_e1():
    res = []
    for entries in iproduct(range(2), repeat=9):
        M = np.array(entries, dtype=np.uint8).reshape(3,3)
        if M[0,0]!=1 or M[1,0]!=0 or M[2,0]!=0: continue
        if int(round(np.linalg.det(M.astype(float)))) % 2 != 1: continue
        res.append(M)
    return res

def build_stabilizer():
    stab = _gl3f2_stab_e1()
    all_perms = set()
    for P in stab:
        for Q in stab:
            pd = [0]*256; pt = [0]*256
            for p in range(256):
                M = _MATS[p]
                Md = (P.astype(int) @ M.astype(int) @ Q.T.astype(int)) % 2; Md[0,0]=0
                pd[p] = _mat_to_int(Md)
                Mt = (Q.astype(int) @ M.T.astype(int) @ P.T.astype(int)) % 2; Mt[0,0]=0
                pt[p] = _mat_to_int(Mt)
            all_perms.add(tuple(pd)); all_perms.add(tuple(pt))
    return np.array(list(all_perms), dtype=np.uint16)

perms = build_stabilizer()
G = perms.shape[0]
print(f"     |G|={G}", flush=True)
assert G == 1152

# Point orbits
def compute_point_orbits(perms):
    par = list(range(256))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    def union(a,b):
        a,b=find(a),find(b)
        if a!=b: par[max(a,b)]=min(a,b)
    for perm in perms:
        for p in range(1,256): union(p, int(perm[p]))
    omap={}; orbits=[]
    pt_orb=[0]*256
    for p in range(1,256):
        r=find(p)
        if r not in omap: omap[r]=len(orbits); orbits.append([])
        idx=omap[r]; orbits[idx].append(p); pt_orb[p]=idx
    return pt_orb, orbits

pt_orb, orbits = compute_point_orbits(perms)
K = len(orbits)
pt_sizes = [len(o) for o in orbits]
reps = [o[0] for o in orbits]
print(f"     K={K}, sizes={pt_sizes}", flush=True)

# Pair orbits
def compute_pair_orbits(perms, pt_orb):
    pp=[]; qq=[]
    for p in range(1,256):
        for q in range(p+1,256):
            pp.append(p); qq.append(q)
    pp=np.array(pp,dtype=np.uint16); qq=np.array(qq,dtype=np.uint16)
    ip = perms[:, pp]; iq = perms[:, qq]
    pmin = np.minimum(ip,iq); pmax = np.maximum(ip,iq)
    keys = pmin.astype(np.uint32)*256 + pmax.astype(np.uint32)
    canon = keys.min(axis=0)
    ukeys = np.unique(canon)
    k2id = {int(k):i for i,k in enumerate(ukeys)}
    Mpair = len(ukeys)
    pair_orb = {}; pair_sizes = [0]*Mpair; pair_ep = [None]*Mpair
    # Also collect pair lists for each orbit
    pair_members = [[] for _ in range(Mpair)]
    for idx in range(len(pp)):
        p,q = int(pp[idx]),int(qq[idx])
        oid = k2id[int(canon[idx])]
        pair_orb[(p,q)] = oid
        pair_sizes[oid] += 1
        pair_members[oid].append((p,q))
        if pair_ep[oid] is None:
            a,b = pt_orb[p], pt_orb[q]
            pair_ep[oid] = (min(a,b), max(a,b))
    return pair_orb, pair_sizes, pair_ep, Mpair, pair_members

pair_orb, pair_sizes, pair_ep, Mpair, pair_members = compute_pair_orbits(perms, pt_orb)
print(f"     Mpair={Mpair}", flush=True)

# n_aj[a][j] = number of pairs (rep_a, q) with q in the point set that land in pair orbit j
n_aj = [[0]*Mpair for _ in range(K)]
for a in range(K):
    pa = reps[a]
    for q in range(1,256):
        if q==pa: continue
        key = (min(pa,q),max(pa,q))
        n_aj[a][pair_orb[key]] += 1

# Block-total equations: for each (a,b) pair of orbits,
# Σ_{P_j ⊂ O_a×O_b or C(O_a,2)} m_j = n_a*n_b or C(n_a,2)
block_total_info = []
for a in range(K):
    # diagonal: Σ_{P_j ⊂ C(O_a,2)} m_j = C(n_a,2)
    jset = set()
    for p in orbits[a]:
        for q in orbits[a]:
            if p < q:
                jset.add(pair_orb[(p,q)])
    block_total_info.append(('diag', a, a, sorted(jset)))
for a in range(K):
    for b in range(a+1, K):
        jset = set()
        for p in orbits[a]:
            for q in orbits[b]:
                key = (min(p,q), max(p,q))
                jset.add(pair_orb[key])
        block_total_info.append(('cross', a, b, sorted(jset)))

print(f"     block_total_equations={len(block_total_info)}", flush=True)

# Load Wang LUT and build E11 quotient records
from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints

LUT_PATH = Path(str(WS / "data/wang_f2_lb20/wang_subspace_lut.pkl"))
lut, _ = load_lut(LUT_PATH)
records, wmeta = build_core_constraints(CoreQuotient(1), lut)
print(f"     Wang records={len(records)}", flush=True)

# Build orbit-averaged Wang RLT constraints (same as analysis)
wang_eq_A = []; wang_eq_b = []
wang_ub_A = []; wang_ub_b = []
NV = K + Mpair  # 6 + 97 = 103 variables

# Cardinality: Σ|O_a|x_a = 19
row=[0.0]*NV
for a in range(K): row[a]=float(pt_sizes[a])
wang_eq_A.append(row); wang_eq_b.append(19.0)

# Pair cardinality: Σ_j n_aj y_j - 18 x_a = 0
for a in range(K):
    row=[0.0]*NV; row[a]=-18.0
    for j in range(Mpair): row[K+j]=float(n_aj[a][j])
    wang_eq_A.append(row); wang_eq_b.append(0.0)

# Pair upper bounds and McCormick
for j in range(Mpair):
    al,be = pair_ep[j]
    r1=[0.0]*NV; r1[K+j]=1.0; r1[al]=-1.0; wang_ub_A.append(r1); wang_ub_b.append(0.0)
    if be!=al:
        r2=[0.0]*NV; r2[K+j]=1.0; r2[be]=-1.0; wang_ub_A.append(r2); wang_ub_b.append(0.0)
for j in range(Mpair):
    al,be = pair_ep[j]
    r=[0.0]*NV; r[al]+=1.0; r[be]+=1.0; r[K+j]=-1.0
    wang_ub_A.append(r); wang_ub_b.append(1.0)

# Wang first-order + RLT
seen = set()
def add_ub(coef_tup, rhs):
    key = (coef_tup, rhs)
    if key not in seen:
        seen.add(key)
        wang_ub_A.append(list(coef_tup)); wang_ub_b.append(rhs)
        return True
    return False

wang_ct = 0
for ri, rec in enumerate(records):
    if ri % 50000 == 0 and ri > 0:
        print(f"      processed {ri}/{len(records)} records, {len(seen)} unique constraints", flush=True)
    bs  = int(rec["point_bitset"])
    L   = int(rec["L"])
    cap = 19 - L
    if cap <= 0: continue
    pts = []
    tmp = bs
    while tmp:
        bit = tmp & -tmp
        pts.append(bit.bit_length())
        tmp ^= bit
    n_orb = [0]*K
    for p in pts: n_orb[pt_orb[p]] += 1
    coef_fo = tuple([float(n_orb[a]) for a in range(K)] + [0.0]*Mpair)
    if add_ub(coef_fo, float(cap)): wang_ct += 1
    for a in range(K):
        pa = reps[a]
        in_S = (bs >> (pa - 1)) & 1
        c_eff = cap - in_S
        mj = [0]*Mpair
        for q in pts:
            if q == pa: continue
            mj[pair_orb[(min(pa,q),max(pa,q))]] += 1
        coef_xp = [0.0]*NV
        coef_xp[a] = -float(c_eff)
        for j in range(Mpair):
            if mj[j]: coef_xp[K+j] = float(mj[j])
        if add_ub(tuple(coef_xp), 0.0): wang_ct += 1
        coef_1xp = [0.0]*NV
        for i in range(K): coef_1xp[i] = float(n_orb[i])
        coef_1xp[a] += float(c_eff)
        for j in range(Mpair):
            if mj[j]: coef_1xp[K+j] = -float(mj[j])
        if add_ub(tuple(coef_1xp), float(cap)): wang_ct += 1
print(f"     Wang RLT unique ub={len(seen)}", flush=True)

# Triangle/Fortet rows: skip for this run, rely on Wang RLT + block totals + square cuts
# (5913 triangle rows would strengthen, but are not required for the square-cut test)
tri_ub_A = []; tri_ub_b = []
print("     Triangle rows: skipped (relying on Wang RLT + block totals + square cuts)", flush=True)

t1_end = time.time()
print(f"     Infrastructure built in {t1_end-t1:.1f}s", flush=True)

# ═══════════════════════════════════════════════════════════════════════════
# Phase 2: Extract exact global square cuts from analysis PSD failures
# ═══════════════════════════════════════════════════════════════════════════
print("  Phase 2: Extract exact global square cuts", flush=True)

# Load analysis integer pair-count PSD failures
with open(DATA/"integer_pair_psd_loop/integer_pair_psd_loop.json") as f:
    psd_loop_data = json.load(f)

def build_moment_matrix(n_vec, m_vec):
    """Build 256x256 moment matrix from integer (n, m).
    Index 0 = constant; indices 1-255 = the 255 directions.
    """
    M = np.zeros((256, 256), dtype=np.float64)
    M[0, 0] = 1.0
    # Point contributions
    for a in range(K):
        if n_vec[a] == 0: continue
        x_a = n_vec[a] / pt_sizes[a]
        for p in orbits[a]:
            M[0, p] = x_a
            M[p, 0] = x_a
            M[p, p] = x_a
    # Pair contributions
    for j in range(Mpair):
        if m_vec[j] == 0: continue
        y_j = m_vec[j] / pair_sizes[j]
        for p, q in pair_members[j]:
            M[p, q] = y_j
            M[q, p] = y_j
    return M

def exact_quadratic_form(v_int, n_vec, m_vec):
    """Compute v^T M v exactly using integer arithmetic.
    Returns a Fraction.
    """
    val = Fraction(int(v_int[0]) ** 2)
    # Point orbit contributions
    for a in range(K):
        if n_vec[a] == 0: continue
        S_a = sum(int(v_int[p]) for p in orbits[a])
        Q_a = sum(int(v_int[p]) ** 2 for p in orbits[a])
        val += Fraction(n_vec[a], pt_sizes[a]) * (2 * int(v_int[0]) * S_a + Q_a)
    # Pair orbit contributions
    for j in range(Mpair):
        if m_vec[j] == 0: continue
        R_j = sum(2 * int(v_int[p]) * int(v_int[q]) for p, q in pair_members[j])
        val += Fraction(m_vec[j], pair_sizes[j]) * R_j
    return val

def compute_global_cut(v_int):
    """Compute integer coefficients for the global linear cut.
    The cut: Σ_a A_a·n_a + Σ_j B_j·m_j ≥ -C
    where C = 1152·v₀², A_a = (1152/|O_a|)·(2v₀S_a + Q_a), B_j = (1152/|P_j|)·R_j.
    All are integers.
    """
    v0 = int(v_int[0])
    C = 1152 * v0 * v0
    A = [0] * K
    for a in range(K):
        S_a = sum(int(v_int[p]) for p in orbits[a])
        Q_a = sum(int(v_int[p]) ** 2 for p in orbits[a])
        A[a] = (1152 // pt_sizes[a]) * (2 * v0 * S_a + Q_a)
    B = [0] * Mpair
    for j in range(Mpair):
        R_j = sum(2 * int(v_int[p]) * int(v_int[q]) for p, q in pair_members[j])
        B[j] = (1152 // pair_sizes[j]) * R_j
    return A, B, C

def extract_cuts_from_matrix(n_vec, m_vec, top_k=10, scale=100000):
    """Extract exact global square cuts from a PSD-failing moment matrix."""
    M = build_moment_matrix(n_vec, m_vec)
    evals, evecs = np.linalg.eigh(M)
    cuts = []
    for idx in range(len(evals)):
        if evals[idx] > -1e-4:
            break
        v = evecs[:, idx]
        v_scaled = v * scale
        v_int = np.round(v_scaled).astype(np.int64)
        # Skip zero vectors
        if np.all(v_int == 0):
            continue
        # Verify exact negativity
        exact_val = exact_quadratic_form(v_int, n_vec, m_vec)
        if exact_val >= 0:
            # Try larger scale
            v_scaled2 = v * (scale * 10)
            v_int2 = np.round(v_scaled2).astype(np.int64)
            exact_val2 = exact_quadratic_form(v_int2, n_vec, m_vec)
            if exact_val2 >= 0:
                continue
            v_int = v_int2
            exact_val = exact_val2
        # Compute global cut coefficients
        A, B, C = compute_global_cut(v_int)
        cuts.append({
            'A': A, 'B': B, 'C': C,
            'exact_value_at_source': str(exact_val),
            'source_eigenvalue': float(evals[idx]),
            'scale_used': scale if np.max(np.abs(v_int)) < scale * 5 else scale * 10,
        })
        if len(cuts) >= top_k:
            break
    return cuts

# Collect all (n, m) failure points from analysis
all_nm_pairs = []
for res in psd_loop_data['results']:
    n_vec = res['n']
    for rd in res['rounds']:
        m_vec = rd['m_vec']
        all_nm_pairs.append((n_vec, m_vec, rd['min_eig']))

print(f"     {len(all_nm_pairs)} (n,m) failure points from analysis", flush=True)

# Extract cuts from each
all_cuts = []
for idx, (n_vec, m_vec, min_eig) in enumerate(all_nm_pairs):
    print(f"     Extracting from point {idx+1}/{len(all_nm_pairs)}: n={n_vec}, min_eig={min_eig:.4f}", flush=True)
    cuts = extract_cuts_from_matrix(n_vec, m_vec, top_k=10, scale=100000)
    for c in cuts:
        c['source_n'] = n_vec
        c['source_min_eig'] = min_eig
    all_cuts.extend(cuts)
    print(f"       extracted {len(cuts)} verified cuts", flush=True)

# Deduplicate by (A, B, C) signature
unique_sigs = {}
for c in all_cuts:
    sig = (tuple(c['A']), tuple(c['B']), c['C'])
    if sig not in unique_sigs:
        unique_sigs[sig] = c
pooled_cuts = list(unique_sigs.values())

print(f"     Total cuts: {len(all_cuts)}, unique: {len(pooled_cuts)}", flush=True)

# Verify cuts are valid at all 8 source points (global validity check)
print("     Verifying global validity at all source points...", flush=True)
violation_count = 0
for c in pooled_cuts:
    A, B, C = c['A'], c['B'], c['C']
    for n_vec, m_vec, _ in all_nm_pairs:
        val = C
        for a in range(K): val += A[a] * n_vec[a]
        for j in range(Mpair): val += B[j] * m_vec[j]
        if val < 0:
            violation_count += 1
print(f"     Violations at source points: {violation_count} (expected: most cuts violate their source)", flush=True)

# ═══════════════════════════════════════════════════════════════════════════
# Phase 3: Find integer m for untested survivors; extract more cuts
# ═══════════════════════════════════════════════════════════════════════════
print("  Phase 3: Test remaining 4 count survivors for integer m", flush=True)

SIX_SURVIVORS = [
    [0,0,3,5,4,7], [1,0,3,6,2,7], [1,0,4,5,2,7],
    [1,0,3,6,3,6], [2,0,3,5,3,6], [1,0,4,5,3,6]
]
TESTED_COUNTS = {tuple(r['n']) for r in psd_loop_data['results']}
UNTESTED = [n for n in SIX_SURVIVORS if tuple(n) not in TESTED_COUNTS]

from ortools.sat.python import cp_model as cpmod

# Pre-convert Wang RLT constraints to SPARSE integer form (done once, reused per count)
# Constraint: Σ_a row[a]*n_a/|O_a| + Σ_j row[K+j]*m_j/|P_j| <= rhs
# ×1152: Σ_a coeff_a*n_a + Σ_j coeff_j*m_j <= rhs_int
print("     Pre-converting Wang RLT to sparse integer form...", flush=True)
mult_pt = [1152 // pt_sizes[a] for a in range(K)]
mult_pr = [1152 // pair_sizes[j] for j in range(Mpair)]

wang_ub_int = []  # list of (pt_coeffs[6], sparse_pair_list, rhs_int)
for i in range(len(wang_ub_A)):
    row = wang_ub_A[i]; rhs = wang_ub_b[i]
    pt_c = [int(round(row[a])) * mult_pt[a] for a in range(K)]
    sparse_pr = []
    for j in range(Mpair):
        c = int(round(row[K+j])) * mult_pr[j]
        if c != 0:
            sparse_pr.append((j, c))
    if sparse_pr:
        wang_ub_int.append((pt_c, sparse_pr, int(round(rhs * 1152))))
print(f"     Integer Wang ub rows with pair vars: {len(wang_ub_int)}", flush=True)

# Also pre-convert equality constraints (pair-cardinality)
wang_eq_int = []
for i in range(len(wang_eq_A)):
    row = wang_eq_A[i]; rhs = wang_eq_b[i]
    pt_c = [int(round(row[a])) * mult_pt[a] for a in range(K)]
    sparse_pr = []
    for j in range(Mpair):
        c = int(round(row[K+j])) * mult_pr[j]
        if c != 0:
            sparse_pr.append((j, c))
    if sparse_pr:
        wang_eq_int.append((pt_c, sparse_pr, int(round(rhs * 1152))))
print(f"     Integer equality rows: {len(wang_eq_int)}", flush=True)

def find_integer_m(n_vec, extra_cuts=None, timeout=60):
    """CP-SAT: find integer m with block totals + pair-cardinality + Wang RLT + cuts."""
    model = cpmod.CpModel()
    m_vars = [model.NewIntVar(0, pair_sizes[j], f"m{j}") for j in range(Mpair)]
    
    # Block-total equations
    for info in block_total_info:
        kind, a, b, jset = info
        lhs = sum(m_vars[j] for j in jset)
        if kind == 'diag':
            rhs_val = n_vec[a] * (n_vec[a] - 1) // 2
        else:
            rhs_val = n_vec[a] * n_vec[b]
        model.Add(lhs == rhs_val)
    
    # Equality constraints (pair-cardinality, from orbit-averaged model)
    for pt_c, sparse_pr, rhs_i in wang_eq_int:
        fixed = sum(pt_c[a] * n_vec[a] for a in range(K))
        expr = sum(c * m_vars[j] for j, c in sparse_pr)
        model.Add(expr == rhs_i - fixed)
    
    # Wang RLT inequality constraints (sparse)
    for pt_c, sparse_pr, rhs_i in wang_ub_int:
        fixed = sum(pt_c[a] * n_vec[a] for a in range(K))
        expr = sum(c * m_vars[j] for j, c in sparse_pr)
        model.Add(expr <= rhs_i - fixed)
    
    # Pooled square cuts
    if extra_cuts:
        for c in extra_cuts:
            A, B, C_val = c['A'], c['B'], c['C']
            fixed_part = C_val + sum(A[a] * n_vec[a] for a in range(K))
            lhs_expr = sum(B[j] * m_vars[j] for j in range(Mpair) if B[j] != 0)
            model.Add(lhs_expr >= -fixed_part)
    
    solver = cpmod.CpSolver()
    solver.parameters.max_time_in_seconds = timeout
    solver.parameters.num_workers = 8
    status = solver.Solve(model)
    
    if status in (cpmod.FEASIBLE, cpmod.OPTIMAL):
        m_sol = [solver.Value(m_vars[j]) for j in range(Mpair)]
        return 'FEASIBLE', m_sol
    elif status == cpmod.INFEASIBLE:
        return 'INFEASIBLE', None
    else:
        return 'UNKNOWN', None

# Find integer m for untested counts, extract cuts if non-PSD
print(f"     Untested survivors: {UNTESTED}", flush=True)
new_nm_pairs = []
integer_m_results = {}

for n_vec in UNTESTED:
    print(f"     Finding integer m for n={n_vec}...", flush=True)
    t_s = time.time()
    status, m_sol = find_integer_m(n_vec, extra_cuts=pooled_cuts, timeout=60)
    t_e = time.time()
    print(f"       status={status}, time={t_e-t_s:.1f}s", flush=True)
    integer_m_results[tuple(n_vec)] = {'status': status, 'time': t_e-t_s}
    
    if status == 'FEASIBLE' and m_sol is not None:
        # Check PSD
        M_mat = build_moment_matrix(n_vec, m_sol)
        evals = np.linalg.eigvalsh(M_mat)
        min_eig = float(evals[0])
        neg_count = int(np.sum(evals < -1e-8))
        print(f"       PSD check: min_eig={min_eig:.6f}, neg_eigs={neg_count}", flush=True)
        integer_m_results[tuple(n_vec)]['min_eig'] = min_eig
        integer_m_results[tuple(n_vec)]['neg_eigs'] = neg_count
        integer_m_results[tuple(n_vec)]['m_vec'] = m_sol
        
        if min_eig < -1e-8:
            new_nm_pairs.append((n_vec, m_sol, min_eig))
            # Extract more cuts
            new_cuts = extract_cuts_from_matrix(n_vec, m_sol, top_k=10, scale=100000)
            for c in new_cuts:
                c['source_n'] = n_vec
                c['source_min_eig'] = min_eig
                sig = (tuple(c['A']), tuple(c['B']), c['C'])
                if sig not in unique_sigs:
                    unique_sigs[sig] = c
                    pooled_cuts.append(c)
            print(f"       Extracted {len(new_cuts)} new cuts (pool now {len(pooled_cuts)})", flush=True)
        else:
            print(f"       *** PSD WITNESS FOUND! ***", flush=True)
            integer_m_results[tuple(n_vec)]['psd_witness'] = True

print(f"     Pool after Phase 3: {len(pooled_cuts)} unique cuts", flush=True)

# ═══════════════════════════════════════════════════════════════════════════
# Phase 4: Test all 6 survivors with integer m + pooled cuts
# ═══════════════════════════════════════════════════════════════════════════
print("  Phase 4: Test all 6 survivors with pooled cuts", flush=True)

phase4_results = []
for n_vec in SIX_SURVIVORS:
    print(f"     Testing n={n_vec}...", flush=True)
    t_s = time.time()
    status, m_sol = find_integer_m(n_vec, extra_cuts=pooled_cuts, timeout=120)
    t_e = time.time()
    result = {'n': n_vec, 'status': status, 'time': round(t_e-t_s, 1)}
    
    if status == 'FEASIBLE' and m_sol is not None:
        # Check PSD
        M_mat = build_moment_matrix(n_vec, m_sol)
        evals = np.linalg.eigvalsh(M_mat)
        min_eig = float(evals[0])
        neg_count = int(np.sum(evals < -1e-8))
        result['min_eig'] = min_eig
        result['neg_eigs'] = neg_count
        result['m_nonzero'] = int(np.sum(np.array(m_sol) > 0))
        print(f"       FEASIBLE, min_eig={min_eig:.6f}, neg_eigs={neg_count}, time={t_e-t_s:.1f}s", flush=True)
        
        if min_eig < -1e-8:
            # Extract cuts for iterative strengthening
            iter_cuts = extract_cuts_from_matrix(n_vec, m_sol, top_k=5, scale=100000)
            for c in iter_cuts:
                c['source_n'] = n_vec
                c['source_min_eig'] = min_eig
                sig = (tuple(c['A']), tuple(c['B']), c['C'])
                if sig not in unique_sigs:
                    unique_sigs[sig] = c
                    pooled_cuts.append(c)
            result['new_cuts'] = len(iter_cuts)
        else:
            result['psd_witness'] = True
            print(f"       *** PSD INTEGER PAIR WITNESS! ***", flush=True)
    else:
        print(f"       {status}, time={t_e-t_s:.1f}s", flush=True)
    
    phase4_results.append(result)

# ═══════════════════════════════════════════════════════════════════════════
# Phase 5: Second pass with expanded pool (if any new cuts were found)
# ═══════════════════════════════════════════════════════════════════════════
feasible_in_phase4 = [r for r in phase4_results if r['status'] == 'FEASIBLE' and r.get('min_eig', 0) < -1e-8]
if feasible_in_phase4 and len(pooled_cuts) > len(all_cuts):
    print(f"  Phase 5: Re-test with expanded pool ({len(pooled_cuts)} cuts)", flush=True)
    phase5_results = []
    for n_vec in SIX_SURVIVORS:
        print(f"     Re-testing n={n_vec}...", flush=True)
        t_s = time.time()
        status, m_sol = find_integer_m(n_vec, extra_cuts=pooled_cuts, timeout=120)
        t_e = time.time()
        result = {'n': n_vec, 'status': status, 'time': round(t_e-t_s, 1)}
        if status == 'FEASIBLE' and m_sol is not None:
            M_mat = build_moment_matrix(n_vec, m_sol)
            evals = np.linalg.eigvalsh(M_mat)
            result['min_eig'] = float(evals[0])
            result['neg_eigs'] = int(np.sum(evals < -1e-8))
            print(f"       FEASIBLE, min_eig={result['min_eig']:.6f}", flush=True)
        else:
            print(f"       {status}, time={t_e-t_s:.1f}s", flush=True)
        phase5_results.append(result)
else:
    phase5_results = None

# ═══════════════════════════════════════════════════════════════════════════
# Summary
# ═══════════════════════════════════════════════════════════════════════════
elapsed = time.time() - t_start
print(f"\n  Summary:", flush=True)
print(f"     Total pooled cuts: {len(pooled_cuts)}", flush=True)
print(f"     Source (n,m) pairs: {len(all_nm_pairs) + len(new_nm_pairs)}", flush=True)

excluded = [r for r in phase4_results if r['status'] == 'INFEASIBLE']
unknown = [r for r in phase4_results if r['status'] == 'UNKNOWN']
feasible = [r for r in phase4_results if r['status'] == 'FEASIBLE']
psd_witnesses = [r for r in phase4_results if r.get('psd_witness')]

print(f"     Phase 4: excluded={len(excluded)}, feasible={len(feasible)}, unknown={len(unknown)}", flush=True)
for r in excluded:
    print(f"       EXCLUDED: n={r['n']}", flush=True)
for r in psd_witnesses:
    print(f"       PSD WITNESS: n={r['n']}", flush=True)

# Save results
summary = {
    'schema': 'pooled_square_cuts_v1',
    'elapsed_sec': round(elapsed, 1),
    'total_pooled_cuts': len(pooled_cuts),
    'source_nm_pairs': len(all_nm_pairs) + len(new_nm_pairs),
    'six_survivors': SIX_SURVIVORS,
    'phase3_untested_results': {str(k): v for k, v in integer_m_results.items()},
    'phase4_results': phase4_results,
    'phase5_results': phase5_results,
    'cut_summary': {
        'from': len(all_cuts),
        'from_phase3': len(pooled_cuts) - len(all_cuts),
        'unique_total': len(pooled_cuts),
    },
    'meaning': "Global exact square cuts derived from PSD-violating integer pair-count "
               "matrices. Each cut is v^T M v >= 0, expressed as an integer linear "
               "inequality in (n_a, m_j) valid for every actual support average. "
               "INFEASIBLE = no integer m exists under block totals + Wang RLT + "
               "triangle + pooled cuts, eliminating that count branch at integer "
               "pair-count level. This is CP-SAT status, not a replayed proof.",
}

with open(OUT / "pooled_square_cuts_results.json", "w") as f:
    json.dump(summary, f, indent=2)

# Save cut coefficients for reuse
cut_records = []
for i, c in enumerate(pooled_cuts):
    cut_records.append({
        'id': i,
        'A': c['A'],
        'B': c['B'],
        'C': c['C'],
        'source_n': c.get('source_n'),
        'source_eigenvalue': c.get('source_eigenvalue'),
        'exact_value_at_source': c.get('exact_value_at_source'),
    })
with open(OUT / "pooled_cuts_coefficients.json", "w") as f:
    json.dump(cut_records, f, indent=2)

print(f"\n  Result: {OUT / 'pooled_square_cuts_results.json'}", flush=True)
print(json.dumps({
    'total_cuts': len(pooled_cuts),
    'excluded_counts': len(excluded),
    'feasible_counts': len(feasible),
    'psd_witnesses': len(psd_witnesses),
    'elapsed_sec': round(elapsed, 1),
}, indent=2), flush=True)
