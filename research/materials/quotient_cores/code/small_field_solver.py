#!/usr/bin/env python3
"""analysis: Systematic containment solver over small finite fields.

Since random search fails completely (codimension ~45 barrier), we need 
algebraic construction. Over small fields F_q, we can:
1. Build a "coverage matrix" showing how each rank-1 matrix covers L_1
2. Use greedy/LP methods to find minimum-weight covers
3. Check tau-structure compatibility

Key insight: in the projected K^{27} space, each pair (v,w) gives a specific
27-vector. We need the span of ≤22 such vectors to contain the 9-dim L_1.
This is equivalent to: the projection of the 22 vectors onto L_1^perp has
rank ≤ 22-9 = 13 in the quotient K^{27}/L_1 (18-dim).

Equivalently: the 22 vectors, projected onto L_1, span all of L_1.
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "small_field_solver"
DATA_DIR.mkdir(parents=True, exist_ok=True)

def gf_rank(M, q):
    """Rank of matrix over GF(q) using Gaussian elimination."""
    M = M.copy() % q
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        if r >= rows: break
        pivot = None
        for row in range(r, rows):
            if M[row, col] % q != 0:
                pivot = row; break
        if pivot is None: continue
        M[[r, pivot]] = M[[pivot, r]]
        # Find inverse mod q
        val = int(M[r, col]) % q
        inv = None
        for x in range(1, q):
            if (val * x) % q == 1: inv = x; break
        if inv is None: continue
        M[r] = (M[r] * inv) % q
        for row in range(rows):
            if row == r: continue
            if M[row, col] % q != 0:
                M[row] = (M[row] - (M[row, col] % q) * M[r]) % q
        r += 1
    return r

def project_rank1_gf(v, w, q):
    """Project v w^T to 27 relevant coords over GF(q)."""
    result = np.zeros(27, dtype=int)
    for r in range(9):
        k = r % 3
        for a in range(3):
            result[r * 3 + a] = (int(v[r]) * int(w[3*k + a])) % q
    return result % q

def build_L_projected_gf(q):
    """Projected L_1 basis over GF(q)."""
    basis = []
    for a in range(3):
        for b in range(3):
            vec = np.zeros(27, dtype=int)
            for k in range(3):
                vec[(3*b + k) * 3 + a] = 1
            basis.append(vec)
    return np.array(basis, dtype=int) % q

def transpose_vec(v, q):
    """3x3 matrix transpose on a 9-vector."""
    V = v.reshape(3, 3)
    return (V.T.ravel()) % q

def l1_coverage(vec, L_proj, q):
    """How many new L_1 dimensions does this vector cover?
    Returns the rank increase when adding vec to L_proj rows."""
    r_before = gf_rank(L_proj.copy(), q)
    augmented = np.vstack([L_proj, vec.reshape(1, -1)]) % q
    r_after = gf_rank(augmented.copy(), q)
    return r_after - r_before

def greedy_cover(L_proj, candidates, q, max_pairs=22):
    """Greedily select pairs to cover L_1."""
    current_span = np.zeros((0, 27), dtype=int)
    selected = []
    l1_remaining = gf_rank(L_proj.copy(), q)  # should be 9
    
    for iteration in range(max_pairs):
        if l1_remaining <= 0: break
        
        best_score = -1
        best_idx = -1
        
        for idx, (v, w, proj_vec) in enumerate(candidates):
            if idx in [s[0] for s in selected]: continue
            
            # Check if this vector helps
            if current_span.shape[0] == 0:
                test = np.vstack([L_proj, proj_vec.reshape(1, -1)]) % q
            else:
                test = np.vstack([current_span, L_proj, proj_vec.reshape(1, -1)]) % q
            r_with = gf_rank(test.copy(), q)
            
            if current_span.shape[0] == 0:
                r_without = gf_rank(L_proj.copy(), q)
            else:
                test2 = np.vstack([current_span, L_proj]) % q
                r_without = gf_rank(test2.copy(), q)
            
            score = r_with - r_without  # How much this reduces defect
            
            if score > best_score:
                best_score = score
                best_idx = idx
        
        if best_score <= 0:
            # No more improvement possible with remaining candidates
            break
        
        v, w, proj_vec = candidates[best_idx]
        selected.append((best_idx, v, w))
        if current_span.shape[0] == 0:
            current_span = proj_vec.reshape(1, -1)
        else:
            current_span = np.vstack([current_span, proj_vec.reshape(1, -1)]) % q
        
        # Recheck L1 defect
        test = np.vstack([current_span, L_proj]) % q
        joint_rank = gf_rank(test.copy(), q)
        span_rank = gf_rank(current_span.copy(), q)
        l1_remaining = joint_rank - span_rank
    
    return selected, l1_remaining

# ======================================================================
# Search over F_3
# ======================================================================
q = 3
print(f"=== Searching over GF({q}) ===")
L_proj = build_L_projected_gf(q)
print(f"L_1 rank over GF({q}): {gf_rank(L_proj.copy(), q)}")

# Enumerate all nonzero v, w pairs and their projections
all_vecs = []
for v_int in range(1, q**9):  # skip 0
    v = np.array([(v_int // (q**i)) % q for i in range(9)], dtype=int)
    if np.all(v == 0): continue
    all_vecs.append(v)
print(f"Nonzero vectors over GF({q}): {len(all_vecs)}")

# Build candidate tau-structured pairs
# Fixed: (v, T(v)) for all nonzero v
# Free orbit: (v, w) and (T(w), T(v)) for v, w nonzero with w != T(v)
print("Building candidate projected vectors...")

# First, just check general (non-tau) pairs with greedy
# Use a sample of pairs for speed
np.random.seed(0)
sample_size = min(5000, len(all_vecs)**2)
candidates = []
seen_projs = set()
for _ in range(sample_size):
    i = np.random.randint(len(all_vecs))
    j = np.random.randint(len(all_vecs))
    v = all_vecs[i]
    w = all_vecs[j]
    proj = project_rank1_gf(v, w, q)
    proj_key = tuple(proj.tolist())
    if proj_key not in seen_projs and not np.all(proj == 0):
        seen_projs.add(proj_key)
        candidates.append((v, w, proj))

print(f"Distinct nonzero projected vectors: {len(candidates)}")

# Greedy search for general pairs
print("\nGreedy cover (general pairs):")
selected, defect = greedy_cover(L_proj, candidates, q, max_pairs=22)
print(f"  Selected {len(selected)} pairs, L_1 defect = {defect}")
if defect == 0:
    print(f"  SUCCESS: L_1 covered with {len(selected)} general pairs!")

# Try with fewer
for target in [9, 10, 11, 12, 15, 18, 22]:
    sel, def_ = greedy_cover(L_proj, candidates, q, max_pairs=target)
    covered = (def_ == 0)
    print(f"  N≤{target:2d}: {len(sel)} pairs, defect={def_}, covered={covered}")

# Now with tau structure
print(f"\n=== Tau-structured greedy search over GF({q}) ===")
tau_candidates = []
seen_tau = set()

# Sample tau pairs
for _ in range(sample_size):
    i = np.random.randint(len(all_vecs))
    j = np.random.randint(len(all_vecs))
    v = all_vecs[i]
    w = all_vecs[j]
    tv = transpose_vec(v, q)
    tw = transpose_vec(w, q)
    
    proj1 = project_rank1_gf(v, w, q)
    proj2 = project_rank1_gf(tw, tv, q)
    
    # For a free orbit, both projections contribute
    combined_proj = np.vstack([proj1.reshape(1,-1), proj2.reshape(1,-1)])
    key = (tuple(proj1.tolist()), tuple(proj2.tolist()))
    if key not in seen_tau and not (np.all(proj1 == 0) and np.all(proj2 == 0)):
        seen_tau.add(key)
        tau_candidates.append((v, w, proj1, proj2))

print(f"Distinct tau pairs: {len(tau_candidates)}")

# Greedy for tau (each free orbit adds 2 vectors to span)
def greedy_tau_cover(L_proj, candidates, q, max_total=22):
    current_span = np.zeros((0, 27), dtype=int)
    selected = []
    total_terms = 0
    
    for iteration in range(max_total // 2 + 1):
        if total_terms >= max_total: break
        
        best_score = -1
        best_idx = -1
        
        for idx, (v, w, p1, p2) in enumerate(candidates):
            if idx in [s[0] for s in selected]: continue
            
            new_vecs = np.vstack([p1.reshape(1,-1), p2.reshape(1,-1)]) % q
            if current_span.shape[0] == 0:
                test = np.vstack([L_proj, new_vecs]) % q
                r_without = gf_rank(L_proj.copy(), q)
            else:
                test = np.vstack([current_span, L_proj, new_vecs]) % q
                test2 = np.vstack([current_span, L_proj]) % q
                r_without = gf_rank(test2.copy(), q)
            r_with = gf_rank(test.copy(), q)
            score = r_with - r_without
            
            if score > best_score:
                best_score = score
                best_idx = idx
        
        if best_score <= 0: break
        
        v, w, p1, p2 = candidates[best_idx]
        selected.append((best_idx, v, w))
        if current_span.shape[0] == 0:
            current_span = np.vstack([p1.reshape(1,-1), p2.reshape(1,-1)]) % q
        else:
            current_span = np.vstack([current_span, p1.reshape(1,-1), p2.reshape(1,-1)]) % q
        total_terms += 2
        
        test = np.vstack([current_span, L_proj]) % q
        joint_rank = gf_rank(test.copy(), q)
        span_rank = gf_rank(current_span.copy(), q)
        defect = joint_rank - span_rank
        if defect == 0: break
    
    return selected, total_terms, defect

tau_sel, tau_total, tau_def = greedy_tau_cover(L_proj, tau_candidates, q, max_total=22)
print(f"Tau greedy: {len(tau_sel)} orbits ({tau_total} terms), defect={tau_def}")
if tau_def == 0:
    print(f"SUCCESS: L_1 covered with {tau_total} tau-structured terms!")

results = {
    "field": q,
    "general_greedy": {"pairs": len(selected), "defect": int(defect)},
    "tau_greedy": {"orbits": len(tau_sel), "terms": tau_total, "defect": int(tau_def)}
}

out_path = DATA_DIR / f"small_field_gf{q}_search.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2, default=lambda o: int(o) if isinstance(o, (np.integer,)) else float(o))
print(f"\nSAVED {out_path}")
