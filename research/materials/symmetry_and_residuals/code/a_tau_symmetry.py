#!/usr/bin/env python3
"""analysisa: Fast τ-symmetry check for rank-23 schemes."""
import numpy as np, json, sys
from pathlib import Path

OUT = Path("data/transpose_layer")
OUT.mkdir(parents=True, exist_ok=True)

def parse_qmm(path):
    terms = []
    current = {}
    for line in open(path):
        line = line.strip()
        if line.startswith("term "):
            if current: terms.append(current)
            current = {}
        elif line.startswith("u "): current["u"] = np.array([int(x) for x in line.split()[1:]]).reshape(3,3)
        elif line.startswith("v "): current["v"] = np.array([int(x) for x in line.split()[1:]]).reshape(3,3)
        elif line.startswith("w "): current["w"] = np.array([int(x) for x in line.split()[1:]]).reshape(3,3)
    if current: terms.append(current)
    return [(t["u"], t["v"], t["w"]) for t in terms]

def check_tau(terms, name):
    n = len(terms)
    matched = [False]*n
    fixed, free_orbits, scalars = [], [], []
    for i in range(n):
        if matched[i]: continue
        u,v,w = terms[i]
        tu, tv, tw = u.T, w.T, v.T  # τ-image
        for j in range(i, n):
            if matched[j] and j!=i: continue
            uj,vj,wj = terms[j]
            # check (tu,tv,tw) = λ*(uj,vj,wj)
            flat1 = np.concatenate([tu.ravel(), tv.ravel(), tw.ravel()])
            flat2 = np.concatenate([uj.ravel(), vj.ravel(), wj.ravel()])
            nz1 = np.nonzero(flat1)[0]
            nz2 = np.nonzero(flat2)[0]
            if set(nz1) != set(nz2): continue
            if len(nz1) == 0: continue  # skip zero
            s = flat2[nz1[0]] / flat1[nz1[0]]
            if np.allclose(flat1 * s, flat2, atol=1e-10):
                if i==j:
                    matched[i]=True; fixed.append((i, s))
                else:
                    matched[i]=matched[j]=True; free_orbits.append((i,j,s))
                break
    unmatched = [i for i in range(n) if not matched[i]]
    f,m = len(fixed), len(free_orbits)
    print(f"  {name}: τ-inv={len(unmatched)==0}, f={f}, m={m}, N={f+m}, unmatched={unmatched}")
    for idx in unmatched[:3]:
        u,v,w = terms[idx]
        print(f"    term {idx}: u_sym={np.allclose(u,u.T)}, v-w^T match={np.allclose(v,w.T)}")
    return {"name":name,"tau_invariant":len(unmatched)==0,"f":f,"m":m,"N":f+m,
            "unmatched":unmatched, "fixed_scalars":[s for _,s in fixed]}

# Naive 27-term 
naive = []
for i in range(3):
    for j in range(3):
        for k in range(3):
            u=np.zeros((3,3),int); u[i,j]=1
            v=np.zeros((3,3),int); v[j,k]=1
            w=np.zeros((3,3),int); w[k,i]=1
            naive.append((u,v,w))

cn122 = parse_qmm("data/cn122_r23_reproduce/scheme.qmm")

# BILR from stored data
data = json.load(open("data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json"))
a0 = np.array(data["a0"], dtype=float)
a0i = np.linalg.inv(a0)
bilr = []
for cube in data["cubes"]:
    L = np.array(cube)
    bilr.append((L, L, L))
for orb in data["free_orbit_representatives"]:
    U,V,W = np.array(orb["U"],dtype=float), np.array(orb["V"],dtype=float), np.array(orb["W"],dtype=float)
    for k in range(3):
        bilr.append((np.round(U).astype(int), np.round(V).astype(int), np.round(W).astype(int)))
        U2 = a0 @ V @ a0i; V2 = a0 @ W @ a0i; W2 = a0 @ U @ a0i
        U,V,W = U2,V2,W2

print("=== τ-symmetry check ===")
r1 = check_tau(naive, "naive_27")
r2 = check_tau(cn122, "cn122_23")
r3 = check_tau(bilr, "BILR_23")

# Dimension verification
count = sum(1 for i in range(3) for k in range(3) for l in range(3))  # 27
print(f"\nτ fixed basis elements: {count}")
print(f"τ-invariant dim: (729+{count})/2 = {(729+count)//2}")

# For naive: check what the fixed/free structure tells us about Gram
print(f"\nNaive Gram analysis:")
print(f"  f={r1['f']} fixed terms, m={r1['m']} free orbits")
print(f"  N = f+m = {r1['N']} (this is the number of Gram products)")
print(f"  Rank check: f + 2m = {r1['f'] + 2*r1['m']} (should be 27)")
# Fixed terms have u=u^T symmetric, so the Gram contribution is tr(u·S)·[tr(v·Y)]^2
for idx, s in r1.get("fixed_scalars", [])[:3]:
    u,v,w = naive[idx]
    print(f"  Fixed term {idx}: u=e_{np.argwhere(u)}, symmetric={np.allclose(u,u.T)}, scalar={s}")

out = {"naive":r1, "cn122":r2, "BILR":r3,
       "tau_invariant_dim": (729+27)//2,
       "naive_gram_N": r1["N"]}
path = OUT / "tau_symmetry_check.json"
path.write_text(json.dumps(out, indent=2, default=float) + "\n")
print(f"\nSAVED {path}")
