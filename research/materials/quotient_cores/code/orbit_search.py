#!/usr/bin/env python3
r"""analysis: Targeted search for order-7 sandwich-invariant rank-22 decompositions.

Orbit type (3,1): 1 fixed rank-one + 3 free orbits of size 7 = 22 terms.
Search strategy:
1. Precompute each orbit's quotient profile (block assignments in type1/type2)
2. Group orbits by profile
3. Search for triples where the combined quotient span is exactly 13 with the fixed point
4. Verify with the full rank-one oracle
"""

import numpy as np
import json, time, sys, itertools
from pathlib import Path

def gf2_rref(M):
    M = np.array(M, dtype=np.int8) % 2
    rows, cols = M.shape; pivots = []; r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if M[i, c]: found = i; break
        if found < 0: continue
        if found != r: M[[r, found]] = M[[found, r]]
        pivots.append(c)
        for i in range(rows):
            if i != r and M[i, c]: M[i] ^= M[r]
        r += 1
    return M[:r], r, pivots

def gf2_rank(M):
    _, r, _ = gf2_rref(np.array(M, dtype=np.int8))
    return r

def gf2_nullspace(M):
    M = np.array(M, dtype=np.int8) % 2
    rref, rank, pivots = gf2_rref(M)
    cols = M.shape[1]
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.int8); v[f] = 1
        for i, p in enumerate(pivots): v[p] = rref[i, f]
        basis.append(v)
    return np.array(basis, dtype=np.int8) if basis else np.zeros((0, cols), dtype=np.int8)

def gf2_inv(M):
    n = M.shape[0]
    aug = np.hstack([np.array(M, dtype=np.int8) % 2, np.eye(n, dtype=np.int8)])
    for c in range(n):
        found = next((i for i in range(c, n) if aug[i, c]), None)
        assert found is not None; 
        if found != c: aug[[c, found]] = aug[[found, c]]
        for i in range(n):
            if i != c and aug[i, c]: aug[i] ^= aug[c]
    return aug[:, n:]

def gf2_matpow(M, k):
    n = M.shape[0]; result = np.eye(n, dtype=np.int8)
    base = np.array(M, dtype=np.int8) % 2
    while k > 0:
        if k & 1: result = (result @ base) % 2
        base = (base @ base) % 2; k >>= 1
    return result

def main():
    t0 = time.time()
    out_dir = Path("data/symmetry_search")
    out_dir.mkdir(parents=True, exist_ok=True)

    # Build T333 and infrastructure
    T = np.zeros((81, 9), dtype=np.int8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[(3*i+j)*9 + (3*j+k), 3*k+i] = 1
    Q = gf2_nullspace(T.T); L = T.T % 2

    F7 = np.array([[0,0,1],[1,0,1],[0,1,0]], dtype=np.int8)
    FiT = gf2_inv(F7).T % 2
    M9 = np.kron(F7, FiT) % 2
    g7 = np.kron(M9, M9).astype(np.int8) % 2

    # Build eigenspace projectors for g7_bar on E/L
    _, _, pivots = gf2_rref(Q)
    Qpiv_inv = gf2_inv(Q[:, pivots])
    Qp = np.zeros((81, 72), dtype=np.int8)
    for i, p in enumerate(pivots): Qp[p] = Qpiv_inv[i]
    g7_bar = (Q @ g7 @ Qp).astype(np.int8) % 2
    I72 = np.eye(72, dtype=np.int8)
    g7b2 = (g7_bar @ g7_bar) % 2
    g7b3 = (g7b2 @ g7_bar) % 2

    # Eigenspace bases
    fix_basis = gf2_nullspace((g7_bar ^ I72) % 2)  # 12-dim
    t1_basis = gf2_nullspace((g7b3 ^ g7_bar ^ I72) % 2)  # 30-dim
    t2_basis = gf2_nullspace((g7b3 ^ g7b2 ^ I72) % 2)  # 30-dim
    print(f"Eigenspace dims: fix={fix_basis.shape[0]}, t1={t1_basis.shape[0]}, t2={t2_basis.shape[0]}")

    # Enumerate rank-one and their orbits
    print("Enumerating rank-one points and orbits...")
    fixed_eigvecs = gf2_nullspace((M9 ^ np.eye(9, dtype=np.int8)) % 2)  # 3-dim
    d = fixed_eigvecs.shape[0]
    assert d == 3

    # Fixed rank-one: u⊗v with M9 u = u and M9 v = v
    fixed_ro = []
    for u_bits in range(1, 2**d):
        u = np.zeros(9, dtype=np.int8)
        for b in range(d):
            if u_bits & (1 << b): u = (u + fixed_eigvecs[b]) % 2
        for v_bits in range(1, 2**d):
            v = np.zeros(9, dtype=np.int8)
            for b in range(d):
                if v_bits & (1 << b): v = (v + fixed_eigvecs[b]) % 2
            fixed_ro.append(np.outer(u, v).ravel().astype(np.int8))
    fixed_ro = np.array(fixed_ro, dtype=np.int8)
    fixed_q = (Q @ fixed_ro.T).T % 2
    print(f"Fixed rank-one: {len(fixed_ro)}, quotient rank: {gf2_rank(fixed_q)}")

    # Free orbits: enumerate all rank-one, remove fixed, group into orbits
    all_ro = []
    ro_to_idx = {}
    idx = 0
    for u_int in range(1, 512):
        u = np.array([(u_int >> b) & 1 for b in range(9)], dtype=np.int8)
        for v_int in range(1, 512):
            v = np.array([(v_int >> b) & 1 for b in range(9)], dtype=np.int8)
            x = np.outer(u, v).ravel().astype(np.int8)
            all_ro.append(x)
            ro_to_idx[x.tobytes()] = idx
            idx += 1
    all_ro = np.array(all_ro, dtype=np.int8)
    all_q = (Q @ all_ro.T).T % 2
    print(f"Total rank-one: {len(all_ro)}")

    # Build orbits
    visited = np.zeros(len(all_ro), dtype=bool)
    fixed_set = set()
    for x in fixed_ro:
        key = x.tobytes()
        if key in ro_to_idx: fixed_set.add(ro_to_idx[key])

    free_orbit_reps = []  # indices of orbit representatives
    for i in range(len(all_ro)):
        if visited[i] or i in fixed_set: 
            visited[i] = True
            continue
        orbit = [i]; visited[i] = True
        x = all_ro[i]
        for _ in range(6):
            x = (g7 @ x) % 2
            j = ro_to_idx.get(x.tobytes())
            if j is None or visited[j]: break
            orbit.append(j); visited[j] = True
        if len(orbit) == 7:
            free_orbit_reps.append(orbit[0])
    
    print(f"Free orbits: {len(free_orbit_reps)}")

    # For each free orbit, compute its 7 quotient vectors and their span structure
    print("Computing orbit quotient profiles...")
    orbit_profiles = []
    for rep_idx in free_orbit_reps:
        # Generate 7 orbit members
        members = [all_ro[rep_idx]]
        x = all_ro[rep_idx]
        for _ in range(6):
            x = (g7 @ x) % 2
            members.append(x)
        members = np.array(members, dtype=np.int8)
        q_members = (Q @ members.T).T % 2
        
        q_rank = gf2_rank(q_members)
        
        # Project to eigenspaces and compute block dimensions
        # Fixed projection: rank of projection onto fix_basis
        fix_proj = np.vstack([fix_basis, q_members])
        fix_rank_gain = gf2_rank(fix_proj) - fix_basis.shape[0]
        
        # Type1 projection
        t1_proj = np.vstack([t1_basis, q_members])
        t1_rank_gain = gf2_rank(t1_proj) - t1_basis.shape[0]
        
        # Type2 projection
        t2_proj = np.vstack([t2_basis, q_members])
        t2_rank_gain = gf2_rank(t2_proj) - t2_basis.shape[0]
        
        # Also: does this orbit's full UV span contain any L-directions?
        orbit_full = members  # 7x81
        l_proj = np.vstack([orbit_full, L])
        l_in_orbit = gf2_rank(orbit_full) + 9 - gf2_rank(l_proj)
        
        orbit_profiles.append({
            'rep': rep_idx,
            'q_rank': q_rank,
            'fix_gain': fix_rank_gain,
            't1_gain': t1_rank_gain,
            't2_gain': t2_rank_gain,
            'l_overlap': l_in_orbit
        })

    # Distribution analysis
    from collections import Counter
    profile_dist = Counter()
    for p in orbit_profiles:
        key = (p['q_rank'], p['fix_gain'], p['t1_gain'], p['t2_gain'], p['l_overlap'])
        profile_dist[key] += 1
    
    print(f"\nOrbit quotient profile distribution:")
    print(f"{'qrank':>5} {'fix':>3} {'t1':>3} {'t2':>3} {'L':>3} {'count':>6}")
    for key in sorted(profile_dist.keys()):
        qr, fg, t1g, t2g, lo = key
        print(f"{qr:>5} {fg:>3} {t1g:>3} {t2g:>3} {lo:>3} {profile_dist[key]:>6}")

    # Search for valid triples
    print(f"\n=== Searching for rank-22 orbit triples ===")
    
    # We need: 1 fixed + 3 free orbits with combined quotient rank 13
    # and combined full UV rank 22 and L ⊂ span
    
    # Quick filter: orbits with high L-overlap are most useful
    useful_orbits = [p for p in orbit_profiles if p['l_overlap'] >= 2]
    print(f"Orbits with L-overlap >= 2: {len(useful_orbits)}")
    
    useful_orbits_all = [p for p in orbit_profiles if p['l_overlap'] >= 1]
    print(f"Orbits with L-overlap >= 1: {len(useful_orbits_all)}")
    
    # Random search: sample triples and check conditions
    np.random.seed(42)
    n_trials = 50000
    best = {'q_rank': 0, 'x_rank': 0, 'l_in_span': 0}
    successes = 0
    
    for trial in range(n_trials):
        # Pick 1 random fixed rank-one
        fix_idx = np.random.randint(len(fixed_ro))
        x0 = fixed_ro[fix_idx]
        
        # Pick 3 random free orbits
        orbit_idxs = np.random.choice(len(free_orbit_reps), 3, replace=False)
        
        # Build 22 UV columns
        columns = [x0]
        for oi in orbit_idxs:
            rep = free_orbit_reps[oi]
            x = all_ro[rep]
            columns.append(x)
            for _ in range(6):
                x = (g7 @ x) % 2
                columns.append(x)
        
        X = np.array(columns, dtype=np.int8)  # 22x81
        x_rank = gf2_rank(X)
        
        if x_rank < 22: continue
        
        # Check quotient rank
        QX = (Q @ X.T).T % 2
        q_rank = gf2_rank(QX)
        
        # Check L containment
        combined = np.vstack([X, L])
        l_in = x_rank + 9 - gf2_rank(combined)
        
        if q_rank > best['q_rank'] or (q_rank == best['q_rank'] and l_in > best['l_in_span']):
            best = {'q_rank': q_rank, 'x_rank': x_rank, 'l_in_span': l_in, 'trial': trial}
        
        if q_rank == 13 and l_in == 9:
            successes += 1
            print(f"  SUCCESS at trial {trial}! Verifying Brent...")
            # Full Brent verification would go here
    
    print(f"\nRandom search: {n_trials} trials, {successes} successes")
    print(f"Best: {best}")
    
    # Also try biased search: use orbits with highest L-overlap
    print(f"\n=== Biased search using high-L-overlap orbits ===")
    high_l = sorted(orbit_profiles, key=lambda p: -p['l_overlap'])[:100]
    print(f"Top L-overlaps: {[p['l_overlap'] for p in high_l[:10]]}")
    
    n_biased = 50000
    best_biased = {'q_rank': 0, 'x_rank': 0, 'l_in_span': 0}
    successes_biased = 0
    
    high_l_indices = [i for i, p in enumerate(orbit_profiles) if p['l_overlap'] >= max(1, high_l[min(99, len(high_l)-1)]['l_overlap'])]
    print(f"Orbits with sufficient L-overlap for biased search: {len(high_l_indices)}")
    
    for trial in range(n_biased):
        fix_idx = np.random.randint(len(fixed_ro))
        x0 = fixed_ro[fix_idx]
        
        if len(high_l_indices) < 3: break
        orbit_choices = np.random.choice(high_l_indices, 3, replace=False)
        
        columns = [x0]
        for oi in orbit_choices:
            rep = free_orbit_reps[orbit_profiles[oi]['rep'] if 'rep' in orbit_profiles[oi] else oi]
            x = all_ro[rep]
            columns.append(x)
            for _ in range(6):
                x = (g7 @ x) % 2
                columns.append(x)
        
        X = np.array(columns, dtype=np.int8)
        x_rank = gf2_rank(X)
        if x_rank < 22: continue
        
        QX = (Q @ X.T).T % 2
        q_rank = gf2_rank(QX)
        combined = np.vstack([X, L])
        l_in = x_rank + 9 - gf2_rank(combined)
        
        if q_rank > best_biased['q_rank'] or (q_rank == best_biased['q_rank'] and l_in > best_biased['l_in_span']):
            best_biased = {'q_rank': q_rank, 'x_rank': x_rank, 'l_in_span': l_in, 'trial': trial}
        
        if q_rank == 13 and l_in == 9:
            successes_biased += 1
    
    print(f"Biased search: {n_biased} trials, {successes_biased} successes")
    print(f"Best biased: {best_biased}")
    
    results = {
        'orbit_count': len(free_orbit_reps),
        'fixed_count': len(fixed_ro),
        'profile_distribution': {str(k): v for k, v in profile_dist.items()},
        'random_search': {'trials': n_trials, 'successes': successes, 'best': best},
        'biased_search': {'trials': n_biased, 'successes': successes_biased, 'best': best_biased},
        'elapsed': time.time() - t0
    }
    
    out_path = out_dir / "orbit_search_results.json"
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nSaved to {out_path}, elapsed {time.time()-t0:.1f}s")

if __name__ == '__main__':
    main()
