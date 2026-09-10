#!/usr/bin/env python3
r"""analysis: extract trace-inconsistent near-miss supports and generate certificates.

Find the A_cols for each trace-inconsistent batch record, build the combined
tensor+trace system, and extract a parity certificate. Then analyze cross-support
parity and the 9D V_trace decomposition.
"""
from __future__ import annotations
import json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, gf2_linear_consistency, mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"
NEAR_MISS = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2

def popcount(x): return bin(x).count('1')

def gf2_rref_basis(vecs):
    basis = []
    for v in vecs:
        for b in basis: v = min(v, v^b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis

def gf2_in_span_decomp(target, generators):
    n = len(generators)
    basis = []
    for i, g in enumerate(generators):
        v, m = g, 1<<i
        for bv, bm in basis:
            v2 = v^bv
            if v2 < v: v, m = v2, m^bm
        if v: basis.append((v, m))
    v, m = target, 0
    for bv, bm in basis:
        v2 = v^bv
        if v2 < v: v, m = v2, m^bm
    return (v==0, m if v==0 else None)

def compute_phi_q(M_inv):
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c,b]) & 1: result |= 1<<(b*9+c)
    return result


def build_trace_system(T_core, A_support):
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc
    def vi(s,b,c): return s*nb*nc + b*nc + c
    rows, labels = [], []
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    if (int(a)>>i) & 1: row ^= 1<<vi(s,b,c)
                row |= (int(T_core[i,b,c])&1)<<nvars
                rows.append(row)
                labels.append(("tensor",i,b,c))
    for q in range(1, 1<<na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9: continue
        I = [s for s,a in enumerate(A_support) if popcount(int(a)&q)&1]
        if len(I) != 9: continue
        M_inv = gf2_mat_inv(M)
        if M_inv is None: continue
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    if int(M_inv[c,b])&1: row ^= 1<<vi(s,b,c)
            row |= 1<<nvars
            rows.append(row)
            labels.append(("trace",q,s))
    return rows, labels, nvars


def extract_cert_parity(labels, cert_mask, A_support, T_core, phi_vectors):
    na, nb, nc = T_core.shape
    tensor_masks = {}
    cert_trace_by_term = defaultdict(list)
    tensor_rhs, trace_cnt = 0, 0
    for idx in range(len(labels)):
        if not ((cert_mask >> idx) & 1): continue
        lbl = labels[idx]
        if lbl[0] == "tensor":
            i,b,c = int(lbl[1]),int(lbl[2]),int(lbl[3])
            tensor_masks[(b,c)] = tensor_masks.get((b,c),0) ^ (1<<i)
            tensor_rhs ^= int(T_core[i,b,c]) & 1
        elif lbl[0] == "trace":
            q, s = int(lbl[1]), int(lbl[2])
            cert_trace_by_term[s].append(q)
            trace_cnt += 1
    total_rhs = tensor_rhs ^ (trace_cnt % 2)

    cert_qs = set()
    for qs in cert_trace_by_term.values(): cert_qs.update(qs)

    forced = {}
    for p in range(1, 256):
        F_p = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b,c),0)
                if popcount(p&mask) & 1: F_p |= 1<<(b*nc+c)
        if F_p == 0:
            forced[p] = 0
            continue
        cphis = [phi_vectors[q] for q in cert_qs if popcount(q&p)&1]
        ok, dec = gf2_in_span_decomp(F_p, cphis)
        if ok:
            forced[p] = popcount(dec) % 2

    return forced, tensor_rhs, total_rhs, list(cert_qs)


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()
    na = T_core.shape[0]

    # Build phi vectors
    phi_vectors = {}
    for q in range(1, 1<<na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9: continue
        M_inv = gf2_mat_inv(M)
        if M_inv is not None: phi_vectors[q] = compute_phi_q(M_inv)

    # Load batch results to get supports
    batch = json.load(open(ROOT/"workspace/data/completion/distinct_candidate_completion_repaired.json"))
    # Load compressed trace to get consistency status
    ctrace = json.load(open(ROOT/"workspace/data/corrected_independent-verification-record"))

    # Map name -> (support, trace_consistent)
    name_to_support = {}
    for rec in batch["best_analyses"]:
        name_to_support[rec["name"]] = rec["A_cols"]

    trace_inconsistent = []
    for rec in ctrace["existing_candidate_batch_records"]:
        name = rec["name"]
        cons = rec.get("compressed_trace_consistent", True)
        if not cons and name in name_to_support:
            trace_inconsistent.append((name, name_to_support[name], rec.get("complete_wang_violations", "?")))

    print(f"Trace-inconsistent supports with known A_cols: {len(trace_inconsistent)}")

    # Generate certificates for up to 6 trace-inconsistent supports
    targets = [(NEAR_MISS, "near_miss_primary", 12)] + [(s,n,w) for n,s,w in trace_inconsistent[:7]]

    certs_all = []
    forced_maps = []
    for sup, name, wv in targets:
        rows, labels, nvars = build_trace_system(T_core, sup)
        ok, rk, cert = gf2_linear_consistency(rows, nvars)
        if not ok and cert is not None:
            forced, t_rhs, total_rhs, cert_qs = extract_cert_parity(
                labels, cert, sup, T_core, phi_vectors)
            # Self-check
            all_forced = all(p in forced for p in sup)
            if all_forced:
                parity = sum(forced[p] for p in sup) % 2
                contradiction = (parity != t_rhs)
            else:
                parity = "escape"
                contradiction = False

            info = {
                "name": name, "wang_viol": wv, "nterms": len(sup),
                "cert_qs": len(cert_qs), "forced": len(forced),
                "escape": 255 - len(forced), "tensor_rhs": t_rhs,
                "self_parity": parity, "self_contradiction": contradiction,
                "support_head": sup[:5],
            }
            certs_all.append(info)
            forced_maps.append(forced)
            print(f"  {name}: wv={wv} cert_qs={len(cert_qs)} forced={len(forced)} "
                  f"esc={255-len(forced)} parity={parity} t_rhs={t_rhs} contr={contradiction}")
        else:
            print(f"  {name}: trace-consistent or no cert")
            certs_all.append({"name": name, "trace_consistent": True})
            forced_maps.append({})

    # Cross-certificate analysis
    print(f"\n=== Cross-certificate parity check ===")
    # For each certificate i, check each support j
    cross_results = []
    for i, fi in enumerate(forced_maps):
        if not fi: continue
        t_rhs_i = certs_all[i]["tensor_rhs"]
        for j, (sup_j, name_j, _) in enumerate(targets):
            all_f = all(p in fi for p in sup_j)
            if all_f:
                par = sum(fi[p] for p in sup_j) % 2
                contr = (par != t_rhs_i)
                cross_results.append({
                    "cert": i, "cert_name": certs_all[i]["name"],
                    "support": j, "support_name": name_j,
                    "parity": par, "tensor_rhs": t_rhs_i, "contradiction": contr,
                })
                if i != j:
                    print(f"  Cert[{i}] applied to support[{j}]: parity={par} "
                          f"t_rhs={t_rhs_i} contr={contr}")

    # Union forced analysis: directions forced by ALL certificates
    # (Intersection of forced sets)
    all_forced_sets = [set(fm.keys()) for fm in forced_maps if fm]
    if all_forced_sets:
        common_forced = all_forced_sets[0]
        for s in all_forced_sets[1:]:
            common_forced &= s
        print(f"\nCommon forced directions across {len(all_forced_sets)} certs: {len(common_forced)}/255")

    # Parity vectors: for each direction, vector of forced values across certs
    print(f"\n=== Parity vector analysis ===")
    n_certs = len([fm for fm in forced_maps if fm])
    parity_vectors = {}
    for p in range(1, 256):
        vec = []
        for fm in forced_maps:
            if fm and p in fm:
                vec.append(fm[p])
            else:
                vec.append(None)
        parity_vectors[p] = vec

    # Check which directions have different forced values across certs
    # (This would mean different certificates give different parity constraints)
    varying_dirs = 0
    for p, vec in parity_vectors.items():
        vals = [v for v in vec if v is not None]
        if len(set(vals)) > 1:
            varying_dirs += 1
    print(f"Directions with varying forced values across certs: {varying_dirs}")

    elapsed = time.time() - t0
    result = {
        "schema": "multi_cert_coverage_v1",
        "elapsed_sec": round(elapsed, 3),
        "certificates": certs_all,
        "cross_results": cross_results,
        "common_forced_count": len(common_forced) if all_forced_sets else 0,
        "varying_directions": varying_dirs,
    }
    out = OUTDIR / "multi_cert_coverage.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
