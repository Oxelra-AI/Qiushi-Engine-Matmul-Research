#!/usr/bin/env python3
"""analysis: Klein V4 vs BILR conjugacy via PGL_3-invariant plane discriminants.

BILR: det restricted to each plane ≡ 0; killing conic det = -2 on all 4 planes.
Method: convert everything to standard sl_3 basis, then compute invariants.
"""
import numpy as np, itertools, json, sys, importlib.util
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'klein_conjugacy'
OUT.mkdir(parents=True, exist_ok=True)

spec = importlib.util.spec_from_file_location('s57', WS / 'scripts' / 'invariant_linear_section.py')
s57 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)

pts_data = json.loads((WS / 'data' / 'exterior_linear_sections' / 'f5_extracted_symmetry_points.json').read_text())

P = 5

# sl_3 basis -> 3x3 traceless matrix
SL3_MATS = [
    np.array([[0,1,0],[0,0,0],[0,0,0]]),   # E01
    np.array([[0,0,1],[0,0,0],[0,0,0]]),   # E02
    np.array([[0,0,0],[1,0,0],[0,0,0]]),   # E10
    np.array([[0,0,0],[0,0,1],[0,0,0]]),   # E12
    np.array([[0,0,0],[0,0,0],[1,0,0]]),   # E20
    np.array([[0,0,0],[0,0,0],[0,1,0]]),   # E21
    np.array([[1,0,0],[0,-1,0],[0,0,0]]),  # H0
    np.array([[0,0,0],[0,1,0],[0,0,-1]]),  # H1
]

def sl_vec_to_mat(c, p):
    M = np.zeros((3,3), dtype=np.int64)
    for k in range(8): M = (M + int(c[k]) * SL3_MATS[k]) % p
    return M % p

def det3(M, p):
    return int((M[0,0]*(M[1,1]*M[2,2]-M[1,2]*M[2,1])
               -M[0,1]*(M[1,0]*M[2,2]-M[1,2]*M[2,0])
               +M[0,2]*(M[1,0]*M[2,1]-M[1,1]*M[2,0])) % p)

def plane_discriminants(plane_vecs_sl, p):
    """3 vectors in sl_3 (8-coords) -> (n_det_nonzero, killing_gram, gram_det)."""
    mats = [sl_vec_to_mat(v, p) for v in plane_vecs_sl]
    # Det trilinear form
    det_coeffs = {}
    for i,j,k in itertools.product(range(3), repeat=3):
        key = tuple(sorted([i,j,k]))
        val = 0
        for perm in itertools.permutations(range(3)):
            inv = sum(1 for a in range(3) for b in range(a+1,3) if perm[a]>perm[b])
            sgn = 1 if inv % 2 == 0 else p-1
            val = (val + sgn * int(mats[i][0,perm[0]]) * int(mats[j][1,perm[1]]) * int(mats[k][2,perm[2]])) % p
        det_coeffs[key] = (det_coeffs.get(key,0) + val) % p
    det_coeffs = {k: v for k, v in det_coeffs.items() if v % p}
    gram = np.zeros((3,3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            gram[i,j] = int(np.sum(mats[i] * mats[j].T)) % p
    return len(det_coeffs), gram.tolist(), det3(gram, p)

def get_all_four_planes_std(family, pivot, vals, p):
    """Return list of 4 planes, each as [vec0, vec1, vec2] in STANDARD sl_3 basis."""
    gens_ad, _ = s57.group_ad_generators(family, p)
    E, _ = s57.simultaneous_eigenbasis(gens_ad, family, p)
    
    # Build plane basis in eigenbasis from chart vals
    nonpiv = [j for j in range(8) if j not in pivot]
    B_eig = [[0]*8 for _ in range(3)]
    for r, c in enumerate(pivot): B_eig[r][c] = 1
    it = iter(vals)
    for c in nonpiv:
        for r in range(3): B_eig[r][c] = int(next(it)) % p
    
    # Group ops in eigenbasis (Gnew = E^{-1} A E)
    Einv = s57.mat_inv(E, p)
    Gnew = [s57.mat_mul(s57.mat_mul(Einv, A, p), E, p) for A in gens_ad]
    if family.startswith('c4'):
        ops_eig = [s57.mat_pow(Gnew[0], k, p) for k in range(4)]
    else:
        ops_eig = [s57.mat_mul(s57.mat_pow(Gnew[0],a,p),s57.mat_pow(Gnew[1],b,p),p)
                    for a in range(2) for b in range(2)]
    
    planes = []
    for Op in ops_eig:
        # Transform plane basis in eigenbasis
        vecs_eig = [s57.mat_vec(Op, B_eig[r], p) for r in range(3)]
        # Convert eigenbasis -> standard: v_std = E @ v_eig
        vecs_std = [np.array(s57.mat_vec(E, ve, p), dtype=np.int64) % p for ve in vecs_eig]
        planes.append(vecs_std)
    return planes

# --- BILR reference ---
bilr_inv = json.loads((WS/'data'/'plane_invariants'/'bilr_plane_invariants.json').read_text())
print("=== BILR (analysis) ===")
for pid in range(4):
    bp = bilr_inv['planes'][pid]
    print(f"  Plane {pid}: det='{bp['determinant_cubic_factor']}', killing_det={bp['killing_conic_det']}")
bilr_gd = (-2) % P
print(f"  Killing det mod 5 = {bilr_gd}\n")

# --- Klein V4 ---
print("=== Klein V4 ===")
kd = pts_data['klein_diag']
kpiv = tuple(kd['pivot'])
klein_res = []
for idx in range(min(8, len(kd['records']))):
    vals = kd['records'][idx]['vals']
    planes = get_all_four_planes_std('klein_diag', kpiv, vals, P)
    pinvs = []
    for pid, pvecs in enumerate(planes):
        ndc, gram, gd = plane_discriminants(pvecs, P)
        pinvs.append({'det_nz': ndc, 'gram_det': gd})
    gds = [pi['gram_det'] for pi in pinvs]
    all_det0 = all(pi['det_nz']==0 for pi in pinvs)
    klein_res.append({'idx': idx, 'det0': all_det0, 'gds': gds})
    print(f"  Point {idx}: det_all_zero={all_det0}, gram_dets={gds}")

# --- C4 regular ---
print("\n=== C4 regular ===")
cd = pts_data['c4_regular']
cpiv = tuple(cd['pivot'])
c4_res = []
for idx in range(min(8, len(cd['records']))):
    vals = cd['records'][idx]['vals']
    planes = get_all_four_planes_std('c4_regular', cpiv, vals, P)
    pinvs = []
    for pid, pvecs in enumerate(planes):
        ndc, gram, gd = plane_discriminants(pvecs, P)
        pinvs.append({'det_nz': ndc, 'gram_det': gd})
    gds = [pi['gram_det'] for pi in pinvs]
    all_det0 = all(pi['det_nz']==0 for pi in pinvs)
    c4_res.append({'idx': idx, 'det0': all_det0, 'gds': gds})
    print(f"  Point {idx}: det_all_zero={all_det0}, gram_dets={gds}")

# --- Summary ---
k_gd_sets = [tuple(sorted(r['gds'])) for r in klein_res]
c_gd_sets = [tuple(sorted(r['gds'])) for r in c4_res]
summary = {
    'bilr_reference': 'all 4 planes have det≡0 and killing_det=-2 (=3 mod 5)',
    'klein_det_zero_all': [r['det0'] for r in klein_res],
    'klein_gram_det_multisets': [list(s) for s in k_gd_sets],
    'c4_det_zero_all': [r['det0'] for r in c4_res],
    'c4_gram_det_multisets': [list(s) for s in c_gd_sets],
}
bilr_sig = (True, (3,3,3,3))  # all det zero, all gram_det = 3
klein_match = any(r['det0'] and tuple(sorted(r['gds']))==(3,3,3,3) for r in klein_res)
c4_match = any(r['det0'] and tuple(sorted(r['gds']))==(3,3,3,3) for r in c4_res)
summary['klein_bilr_match_found'] = klein_match
summary['c4_bilr_match_found'] = c4_match

print(f"\n=== Conjugacy summary ===\n{json.dumps(summary, indent=2)}")
path = OUT / 'klein_conjugacy_discriminants.json'
path.write_text(json.dumps(summary, indent=2) + '\n')
print(f"SAVED {path}")
