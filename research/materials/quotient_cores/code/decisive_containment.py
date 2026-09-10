#!/usr/bin/env python3
"""analysisD: DECISIVE containment check after deleting each fixed term.

The projection analysis shows term 1 has zero L_sym projection, so the remaining
6 project surjectively onto L_sym. But projection surjectivity does NOT imply
containment. The decisive test is:
  rank(F + remaining_fixed + L_1) = 22  =>  containment holds  =>  rank-22 scheme!
  rank(F + remaining_fixed + L_1) = 23  =>  containment fails
"""
import numpy as np
import json
from pathlib import Path

P = 65521; IROOT = 41224
WS = Path(__file__).resolve().parent.parent
DATA = WS / "data" / "two_sector"

def mod(x): return np.asarray(x, dtype=object) % P
def inv_mod(a): return pow(int(a) % P, -1, P)
def rank_mod(M):
    M = mod(M).copy(); m, n = M.shape; r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if int(M[i,c]) % P), None)
        if piv is None: continue
        if piv != r: M[[r, piv]] = M[[piv, r]]
        M[r,:] = (M[r,:] * inv_mod(M[r,c])) % P
        for i in range(m):
            if i != r and int(M[i,c]) % P:
                M[i,:] = (M[i,:] - M[i,c] * M[r,:]) % P
        r += 1
    return r

# L_1 basis
L1_vecs = []
for a in range(3):
    for b in range(3):
        row = np.zeros(81, dtype=object)
        for k in range(3): row[9*(3*b+k) + (3*k+a)] = 1
        L1_vecs.append(row)
L1 = np.vstack(L1_vecs)

# L_sym / L_anti
sym_vecs, anti_vecs = [], []
for a in range(3): sym_vecs.append(L1_vecs[3*a+a])
for a in range(3):
    for b in range(a+1, 3):
        sym_vecs.append((L1_vecs[3*a+b] + L1_vecs[3*b+a]) % P)
        anti_vecs.append((L1_vecs[3*a+b] - L1_vecs[3*b+a]) % P)
L_sym = mod(np.vstack(sym_vecs))
L_anti = mod(np.vstack(anti_vecs))

# Transport Laderman
src = (WS/"scripts"/"laderman_tau_decomp.py").read_text()
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(WS/"scripts"/"laderman_tau_decomp.py"), "__name__": "defs_only"}
exec(compile(prefix, str(WS/"scripts"/"laderman_tau_decomp.py"), "exec"), ns)
terms = [(mod(a), mod(b), mod(c)) for a, b, c in ns['terms']]
eps1, pi12 = mod(ns['eps1']), mod(ns['pi12'])
def mat_inv(A):
    A = mod(A); n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=object)], axis=1) % P
    for c in range(n):
        piv = next(i for i in range(c, n) if int(aug[i,c]) % P)
        if piv != c: aug[[c, piv]] = aug[[piv, c]]
        aug[c,:] = (aug[c,:] * inv_mod(aug[c,c])) % P
        for i in range(n):
            if i != c and int(aug[i,c]) % P:
                aug[i,:] = (aug[i,:] - aug[i,c]*aug[c,:]) % P
    return aug[:, n:] % P
Q_mat = (eps1 @ pi12) % P; R_mat = np.diag([IROOT, 1, 1]).astype(object) % P
Qinv = mat_inv(Q_mat); Rinv = mat_inv(R_mat)
transported = [(a @ Qinv % P, Q_mat @ b @ Rinv % P, R_mat @ c % P) for a, b, c in terms]

free_pairs = [(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
free_indices = [i for p in free_pairs for i in p]
fixed_indices = [i for i in range(23) if i not in free_indices]
def vec9(M): return mod(M).reshape(9)

# Build all slice matrices
all_slices = []
for idx in range(23):
    _, b, c = transported[idx]
    all_slices.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)

F_vecs = [all_slices[i] for i in free_indices]
F = mod(np.vstack(F_vecs))

# Baseline verification
all_mat = mod(np.vstack(all_slices))
rk_all = rank_mod(all_mat)
rk_all_L1 = rank_mod(mod(np.vstack([all_mat, L1])))
print(f"Baseline: rank(all 23 terms) = {rk_all}")
print(f"Baseline: rank(all 23 + L_1) = {rk_all_L1} (should = {rk_all} if containment)")
print(f"Containment at rank 23: {'YES' if rk_all_L1 == rk_all else 'NO'}")

# DECISIVE TEST: for each fixed term deletion
print(f"\n{'='*60}")
print("DECISIVE CONTAINMENT TEST: delete each fixed term")
print(f"{'='*60}")
results = []
for fi, fix_idx in enumerate(fixed_indices):
    remaining_indices = [i for i in range(23) if i != fix_idx]
    remaining = mod(np.vstack([all_slices[i] for i in remaining_indices]))
    
    rk_rem = rank_mod(remaining)
    rk_rem_L1 = rank_mod(mod(np.vstack([remaining, L1])))
    rk_rem_Lsym = rank_mod(mod(np.vstack([remaining, L_sym])))
    rk_rem_Lanti = rank_mod(mod(np.vstack([remaining, L_anti])))
    
    L1_contained = (rk_rem_L1 == rk_rem)
    Lsym_contained = (rk_rem_Lsym == rk_rem)
    Lanti_contained = (rk_rem_Lanti == rk_rem)
    
    status = "RANK-22 CANDIDATE!" if L1_contained else "FAILS"
    print(f"\n  Delete fixed {fix_idx+1} (0-based {fix_idx}):")
    print(f"    rank(remaining 22 terms) = {rk_rem}")
    print(f"    rank(remaining + L_1) = {rk_rem_L1}")
    print(f"    rank(remaining + L_sym) = {rk_rem_Lsym}")
    print(f"    rank(remaining + L_anti) = {rk_rem_Lanti}")
    print(f"    L_1 contained: {L1_contained}")
    print(f"    L_sym contained: {Lsym_contained}")
    print(f"    L_anti contained: {Lanti_contained}")
    print(f"    STATUS: {status}")
    
    results.append({
        "deleted_1based": fix_idx+1,
        "rank_remaining": int(rk_rem),
        "rank_with_L1": int(rk_rem_L1),
        "rank_with_Lsym": int(rk_rem_Lsym),
        "rank_with_Lanti": int(rk_rem_Lanti),
        "L1_contained": L1_contained,
        "Lsym_contained": Lsym_contained,
        "Lanti_contained": Lanti_contained,
    })

# Also try deleting free orbits (for comparison)
print(f"\n{'='*60}")
print("Delete each free orbit (control check)")
print(f"{'='*60}")
for oi, (i1, i2) in enumerate(free_pairs):
    remaining_indices = [i for i in range(23) if i not in (i1, i2)]
    remaining = mod(np.vstack([all_slices[i] for i in remaining_indices]))
    rk_rem = rank_mod(remaining)
    rk_rem_L1 = rank_mod(mod(np.vstack([remaining, L1])))
    L1_ok = (rk_rem_L1 == rk_rem)
    print(f"  Delete orbit ({i1+1},{i2+1}): rank={rk_rem}, L_1 contained={L1_ok}")

out = {"field": f"F_{P}", "deletion_results": results}
out_path = DATA / "decisive_containment.json"
out_path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {out_path}")
