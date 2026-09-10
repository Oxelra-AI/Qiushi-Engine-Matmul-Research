#!/usr/bin/env python3
"""analysis: exact scalar check for the Laderman tau-type automorphism.

analysis matched Phi3*Phi4 to the 23 Laderman projective terms.  This
script checks the actual rank-one tensors: for each term, it records whether
Phi(term) equals +term_j or -term_j as a tensor.  This is necessary because a
projective term permutation is not, by itself, a weighted decomposition
symmetry.
"""
import json, runpy, contextlib, io
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "laderman_tau_flip"
OUT.mkdir(parents=True, exist_ok=True)

# Reuse the audited analysis term transcription, but execute only the
# definitions before the script's first print/output side effect.
src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
src = src_path.read_text()
prefix = src.split('print(f"Loaded {len(terms)} Laderman terms")')[0]
ns = {"__file__": str(src_path), "__name__": "defs_only"}
exec(compile(prefix, str(src_path), "exec"), ns)
terms = ns["terms"]
eps1 = ns["eps1"]
eps2 = ns["eps2"]
pi12 = ns["pi12"]

def Phi3(a, b, c):
    return (b.T @ eps2, eps2 @ a.T, c.T)

def Phi4(a, b, c):
    return (eps1 @ c @ pi12, pi12 @ a @ pi12 @ eps1, eps1 @ pi12 @ b @ eps1)

def compose_phi(f, g, a, b, c):
    a1, b1, c1 = g(a, b, c)
    return f(a1, b1, c1)

def vec_term(t):
    a,b,c = t
    return np.einsum('i,j,k->ijk', a.reshape(-1), b.reshape(-1), c.reshape(-1)).reshape(-1)

def scalar_relation(x, y):
    """Return lambda in {-1,1} if x=lambda*y over Z, else None."""
    nz = np.nonzero(y)[0]
    if len(nz) == 0:
        return None
    lam = None
    for idx in nz:
        if y[idx] != 0:
            if x[idx] % y[idx] != 0:
                # entries are small, but relation should be +/- exact
                pass
            lam = x[idx] / y[idx]
            break
    if lam is None:
        return None
    if np.array_equal(x, lam*y):
        if lam == 1 or lam == -1:
            return int(lam)
        return lam
    return None

vectors = [vec_term(t) for t in terms]
phi_vectors = [vec_term(compose_phi(Phi3, Phi4, *t)) for t in terms]
perm = []
coeffs = []
bad = []
for i, x in enumerate(phi_vectors):
    found = None
    for j, y in enumerate(vectors):
        lam = scalar_relation(x, y)
        if lam is not None:
            found = (j, lam)
            break
    if found is None:
        bad.append(i+1)
        perm.append(None)
        coeffs.append(None)
    else:
        perm.append(found[0]+1)
        coeffs.append(found[1])

# Check whether the signed permuted sum equals T termwise.
sum_vec = np.sum(vectors, axis=0)
phi_sum_vec = np.sum(phi_vectors, axis=0)

# Over F3, -1 is 2.
coeffs_mod3 = [None if c is None else (c % 3) for c in coeffs]

fixed = []
two_cycles = []
seen=set()
for i,p in enumerate(perm):
    if p is None: continue
    j=p-1
    if j==i:
        fixed.append({"term": i+1, "coeff_Z": coeffs[i], "coeff_F3": coeffs_mod3[i]})
    elif i not in seen:
        two_cycles.append({"terms": [i+1,j+1], "coeffs_Z": [coeffs[i], coeffs[j]], "coeffs_F3": [coeffs_mod3[i], coeffs_mod3[j]], "roundtrip_coeff_Z": None if coeffs[i] is None or coeffs[j] is None else coeffs[i]*coeffs[j]})
        seen.add(i); seen.add(j)

out={
    "perm": perm,
    "coeffs_Z": coeffs,
    "coeffs_F3": coeffs_mod3,
    "bad_terms": bad,
    "all_projective_terms_matched": len(bad)==0,
    "phi_preserves_total_tensor_over_Z": bool(np.array_equal(sum_vec, phi_sum_vec)),
    "phi_preserves_total_tensor_over_F3": bool(np.array_equal(sum_vec % 3, phi_sum_vec % 3)),
    "fixed": fixed,
    "two_cycles": two_cycles,
    "num_negative_tensor_images_Z": int(sum(1 for c in coeffs if c == -1)),
    "num_positive_tensor_images_Z": int(sum(1 for c in coeffs if c == 1)),
    "note": "coeff_Z=-1 means Phi sends that summand to the negative of the listed Laderman summand as a rank-one tensor; the total tensor can still be Phi-invariant only with the signed weights considered."
}
path=OUT/"laderman_phi_coefficients.json"
path.write_text(json.dumps(out, indent=2)+"\n")
print(json.dumps(out, indent=2))
print("SAVED", path)
