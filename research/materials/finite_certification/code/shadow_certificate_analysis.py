#!/usr/bin/env python3
r"""analysis: exact 3x3 shadow contradiction extraction and guarded support relations.

This script uses the corrected E11 convention M_lambda = Lambda^T \otimes I_3.
For a fixed 19-point quotient A-support and a set of saturated rank-9 contractions,
it builds the 3x3 shadow linear system over F2, extracts a row-combination proof
0=1 when the system is inconsistent, and translates that row combination into a
support-dependent guarded relation.

The relation is only valid under its saturation guard: every contraction lambda in
the certificate must have weight 9 on the tested support.  It is a necessary
condition for B/C completion, not a rank-one realization or a full tensor proof.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

A_POSITIONS = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
TRACE_INCONSISTENT_9V = [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219]
TRACE_CONSISTENT_9V = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
OUTDIR = Path("data/shadow_certificate")


def popparity(x: int) -> int:
    return int(x.bit_count() & 1)


def gf2_rank(M: np.ndarray) -> int:
    A = np.array(M, dtype=np.uint8, copy=True) & 1
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return r


def gf2_rref_augmented_with_combo(A: np.ndarray, b: np.ndarray) -> Tuple[bool, int, int, Optional[List[int]]]:
    """Return consistency plus one row-combination certificate if inconsistent.

    The certificate is a list of original row indices whose XOR has zero variable
    coefficients and right-hand side one.
    """
    A = np.array(A, dtype=np.uint8, copy=True) & 1
    b = np.array(b, dtype=np.uint8, copy=True).reshape(-1, 1) & 1
    M = np.hstack([A, b])
    m, n_aug = M.shape
    n = n_aug - 1
    combo = np.eye(m, dtype=np.uint8)
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if M[i, c]:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
            combo[[r, piv]] = combo[[piv, r]]
        for i in range(m):
            if i != r and M[i, c]:
                M[i] ^= M[r]
                combo[i] ^= combo[r]
        r += 1
        if r == m:
            break
    for i in range(m):
        if not M[i, :n].any() and M[i, n]:
            cert = [j for j in range(m) if combo[i, j]]
            return False, r, r + 1, cert
    rankA = gf2_rank(A)
    rankAb = gf2_rank(np.hstack([A, b]))
    return rankA == rankAb, rankA, rankAb, None


def gf2_solve_one(A: np.ndarray, b: np.ndarray) -> Optional[np.ndarray]:
    """One GF(2) solution of A x = b, or None."""
    A = np.array(A, dtype=np.uint8, copy=True) & 1
    b = np.array(b, dtype=np.uint8, copy=True).reshape(-1, 1) & 1
    m, n = A.shape
    M = np.hstack([A, b])
    pivots = []
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if M[i, c]:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        for i in range(m):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        pivots.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if not M[i, :n].any() and M[i, n]:
            return None
    x = np.zeros(n, dtype=np.uint8)
    for i, c in enumerate(pivots):
        x[c] = M[i, n]
    return x


def lambda_to_mat(lam: int) -> np.ndarray:
    M = np.zeros((3, 3), dtype=np.uint8)
    for bit, (i, j) in enumerate(A_POSITIONS):
        if (lam >> bit) & 1:
            M[i, j] = 1
    return M


def mat_inv_gf2_3x3(M: np.ndarray) -> Optional[np.ndarray]:
    M = np.array(M, dtype=np.uint8, copy=True) & 1
    A = np.hstack([M, np.eye(3, dtype=np.uint8)])
    r = 0
    for c in range(3):
        piv = -1
        for i in range(r, 3):
            if A[i, c]:
                piv = i
                break
        if piv < 0:
            return None
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(3):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, 3:] & 1


def h_mask_for_lambda(lam: int) -> int:
    Linv = mat_inv_gf2_3x3(lambda_to_mat(lam))
    if Linv is None:
        raise ValueError(f"lambda {lam} is singular over F2")
    mask = 0
    # Shadow variables ordered Y[j,i] as bit 3*j+i; coeff is Lambda^{-1}[j,i].
    for j in range(3):
        for i in range(3):
            if Linv[j, i]:
                mask |= 1 << (3*j + i)
    return mask


def shadow_target_mask_for_slice(k: int) -> int:
    ai, aj = A_POSITIONS[k]
    # slice (ai,aj) maps to shadow E_{aj,ai}
    return 1 << (3*aj + ai)


def find_tight_rank9(support: Sequence[int]) -> List[int]:
    tight = []
    for lam in range(1, 256):
        if gf2_rank(lambda_to_mat(lam)) != 3:
            continue
        wt = sum(popparity(int(p) & lam) for p in support)
        if wt == 9:
            tight.append(lam)
    return tight


def build_labelled_shadow_system(support: Sequence[int], lambdas: Sequence[int]) -> Tuple[np.ndarray, np.ndarray, List[dict]]:
    s = len(support)
    nv = s * 9
    rows = []
    rhs = []
    labels = []
    # Tensor shadow rows.
    for k in range(8):
        target_mask = shadow_target_mask_for_slice(k)
        for u in range(9):
            row = np.zeros(nv, dtype=np.uint8)
            for t, p in enumerate(support):
                if (int(p) >> k) & 1:
                    row[t*9 + u] = 1
            rows.append(row)
            rhs.append((target_mask >> u) & 1)
            labels.append({"type": "tensor", "slice": k, "cell": u, "rhs": int((target_mask >> u) & 1)})
    # Trace rows from saturated rank-9 contractions.
    for lam in lambdas:
        if gf2_rank(lambda_to_mat(lam)) != 3:
            continue
        h = h_mask_for_lambda(lam)
        active = [t for t, p in enumerate(support) if popparity(int(p) & int(lam))]
        if len(active) != 9:
            continue
        for t in active:
            row = np.zeros(nv, dtype=np.uint8)
            for u in range(9):
                if (h >> u) & 1:
                    row[t*9 + u] ^= 1
            rows.append(row)
            rhs.append(1)
            labels.append({"type": "trace", "lambda": int(lam), "term_index": int(t), "point": int(support[t]), "h_mask": int(h), "rhs": 1})
    return np.array(rows, dtype=np.uint8), np.array(rhs, dtype=np.uint8), labels


def mask_from_tensor_coeffs(tensor_coeff: List[List[int]], p: int) -> int:
    out = 0
    for k in range(8):
        if (p >> k) & 1:
            for u in range(9):
                if tensor_coeff[k][u]:
                    out ^= 1 << u
    return out


def in_span_and_parity(target_mask: int, masks: List[int]) -> Tuple[bool, Optional[int], Optional[List[int]]]:
    """Solve sum alpha_i masks_i = target. Return parity of one representation."""
    m = len(masks)
    if m == 0:
        return target_mask == 0, 0 if target_mask == 0 else None, [] if target_mask == 0 else None
    # Equations: for each bit u, sum_i alpha_i*masks_i[u] = target[u].
    A = np.zeros((9, m), dtype=np.uint8)
    b = np.zeros(9, dtype=np.uint8)
    for u in range(9):
        b[u] = (target_mask >> u) & 1
        for i, h in enumerate(masks):
            A[u, i] = (h >> u) & 1
    sol = gf2_solve_one(A, b)
    if sol is None:
        return False, None, None
    idxs = [i for i, v in enumerate(sol.tolist()) if v]
    return True, int(sol.sum() & 1), idxs


def has_odd_zero_dependency(masks: List[int]) -> Tuple[bool, Optional[List[int]]]:
    m = len(masks)
    if m == 0:
        return False, None
    A = np.zeros((10, m), dtype=np.uint8)
    b = np.zeros(10, dtype=np.uint8)
    for u in range(9):
        for i, h in enumerate(masks):
            A[u, i] = (h >> u) & 1
    for i in range(m):
        A[9, i] = 1
    b[9] = 1
    sol = gf2_solve_one(A, b)
    if sol is None:
        return False, None
    return True, [i for i, v in enumerate(sol.tolist()) if v]


def extract_shadow_certificate(support: Sequence[int], lambdas: Sequence[int]) -> dict:
    A, b, labels = build_labelled_shadow_system(support, lambdas)
    consistent, rA, rAb, cert_rows = gf2_rref_augmented_with_combo(A, b)
    out = {
        "support": [int(x) for x in support],
        "lambda_guard": [int(x) for x in lambdas],
        "rows": int(A.shape[0]),
        "variables": int(A.shape[1]),
        "consistent": bool(consistent),
        "rank": int(rA),
        "augmented_rank": int(rAb),
    }
    if consistent:
        return out
    assert cert_rows is not None
    rowxor = np.zeros(A.shape[1], dtype=np.uint8)
    rhsxor = 0
    for ri in cert_rows:
        rowxor ^= A[ri]
        rhsxor ^= int(b[ri])
    tensor_coeff = [[0]*9 for _ in range(8)]
    trace_by_term = defaultdict(list)
    used_labels = []
    for ri in cert_rows:
        lab = dict(labels[ri])
        used_labels.append(lab)
        if lab["type"] == "tensor":
            tensor_coeff[int(lab["slice"])][int(lab["cell"])] ^= 1
        else:
            trace_by_term[int(lab["term_index"])].append(int(lab["lambda"]))
    tensor_rhs = 0
    trace_rhs = 0
    for lab in used_labels:
        if lab["type"] == "tensor":
            tensor_rhs ^= int(lab["rhs"])
        else:
            trace_rhs ^= int(lab["rhs"])
    guard = sorted({int(lab["lambda"]) for lab in used_labels if lab["type"] == "trace"})
    out.update({
        "certificate_row_indices": [int(i) for i in cert_rows],
        "certificate_row_count": len(cert_rows),
        "certificate_verification": {
            "coefficients_zero": bool(not rowxor.any()),
            "rhs_one": bool(rhsxor == 1),
        },
        "type_counts": dict(Counter(lab["type"] for lab in used_labels)),
        "tensor_rhs": int(tensor_rhs),
        "trace_rhs": int(trace_rhs),
        "total_rhs": int(rhsxor),
        "tensor_coeff_masks_by_slice": [sum((int(tensor_coeff[k][u]) << u) for u in range(9)) for k in range(8)],
        "guard_lambdas_used": guard,
        "trace_lambdas_by_term": {str(k): v for k, v in sorted(trace_by_term.items())},
        "used_labels_head": used_labels[:160],
    })
    return out


def classify_all_directions(cert: dict) -> dict:
    guard = [int(q) for q in cert.get("guard_lambdas_used", [])]
    h_by_q = {q: h_mask_for_lambda(q) for q in guard}
    tensor_masks = [int(x) for x in cert.get("tensor_coeff_masks_by_slice", [])]
    tensor_coeff = [[(tensor_masks[k] >> u) & 1 for u in range(9)] for k in range(8)]
    records = []
    counts = Counter()
    forced_val_counts = Counter()
    for p in range(1, 256):
        hit = [q for q in guard if popparity(p & q)]
        hit_masks = [h_by_q[q] for q in hit]
        odd, odd_idxs = has_odd_zero_dependency(hit_masks)
        Fp = mask_from_tensor_coeffs(tensor_coeff, p)
        if odd:
            rec = {"p": p, "class": "local_inconsistent", "hit_count": len(hit), "F_mask": Fp,
                   "odd_dependency_qs": [hit[i] for i in odd_idxs or []]}
        else:
            span, parity, rep_idxs = in_span_and_parity(Fp, hit_masks)
            if not span:
                rec = {"p": p, "class": "free", "hit_count": len(hit), "F_mask": Fp}
            else:
                rec = {"p": p, "class": "forced", "forced_value": int(parity), "hit_count": len(hit), "F_mask": Fp,
                       "forcing_qs": [hit[i] for i in rep_idxs or []]}
                forced_val_counts[int(parity)] += 1
        records.append(rec)
        counts[rec["class"]] += 1
    return {
        "guard_lambdas": guard,
        "tensor_rhs": int(cert.get("tensor_rhs", 0)),
        "class_counts": dict(counts),
        "forced_value_counts": dict(forced_val_counts),
        "records": records,
    }


def apply_classification_to_support(classification: dict, support: Sequence[int]) -> dict:
    by_p = {int(r["p"]): r for r in classification["records"]}
    cls_counts = Counter()
    forced_sum = 0
    free_points = []
    bad_points = []
    forced_points = []
    for p0 in support:
        p = int(p0)
        rec = by_p[p]
        cls_counts[rec["class"]] += 1
        if rec["class"] == "forced":
            forced_sum ^= int(rec["forced_value"])
            forced_points.append([p, int(rec["forced_value"])])
        elif rec["class"] == "free":
            free_points.append(p)
        else:
            bad_points.append(p)
    tensor_rhs = int(classification.get("tensor_rhs", 0))
    pure_applicable = (len(free_points) == 0 and len(bad_points) == 0)
    contradiction = bool(pure_applicable and ((forced_sum ^ tensor_rhs) == 1))
    return {
        "support": [int(x) for x in support],
        "support_class_counts": dict(cls_counts),
        "forced_sum": int(forced_sum),
        "tensor_rhs": tensor_rhs,
        "pure_parity_applicable": pure_applicable,
        "pure_parity_contradiction": contradiction,
        "free_points": free_points,
        "local_inconsistent_points": bad_points,
        "forced_points": forced_points,
    }


def weights_for_guard(support: Sequence[int], guard: Sequence[int]) -> Dict[str, int]:
    return {str(q): sum(popparity(int(p) & int(q)) for p in support) for q in guard}


def load_mutation_supports(limit: int = 17) -> List[Tuple[str, List[int]]]:
    path = Path("data/tight_rank_geometry/rankweight_mutation_geometry.json")
    out = []
    if not path.exists():
        return out
    data = json.loads(path.read_text())
    for rec in data.get("summaries", [])[:limit]:
        if "support" in rec:
            out.append((rec.get("label", f"sample_{len(out)}"), [int(x) for x in rec["support"]]))
    return out


def analyze_support(label: str, support: Sequence[int]) -> dict:
    tight = find_tight_rank9(support)
    A, b, _ = build_labelled_shadow_system(support, tight)
    consistent, rA, rAb, _ = gf2_rref_augmented_with_combo(A, b)
    return {"label": label, "support": [int(x) for x in support], "tight_rank9": tight,
            "tight_rank9_count": len(tight), "shadow_consistent": bool(consistent),
            "rank": int(rA), "augmented_rank": int(rAb), "rows": int(A.shape[0]), "variables": int(A.shape[1])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=OUTDIR / "shadow_certificate_analysis.json")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    l15_tight = find_tight_rank9(L15)
    # Use the two minimum subsets from analysis plus the full tight set.
    min_subsets = [
        [42,43,49,87,94,157,214,234],
        [42,43,49,87,94,157,214,241],
    ]
    certs = []
    for name, lambdas in [("L15_min8_A", min_subsets[0]), ("L15_min8_B", min_subsets[1]), ("L15_all16", l15_tight)]:
        cert = extract_shadow_certificate(L15, lambdas)
        cert["name"] = name
        cls = classify_all_directions(cert) if not cert.get("consistent") else None
        applies = []
        if cls:
            test_supports = [("L15", L15), ("trace_inconsistent_9v", TRACE_INCONSISTENT_9V), ("trace_consistent_9v", TRACE_CONSISTENT_9V)]
            test_supports.extend(load_mutation_supports())
            for lab, sup in test_supports:
                rec = apply_classification_to_support(cls, sup)
                rec["label"] = lab
                rec["guard_weights"] = weights_for_guard(sup, cls["guard_lambdas"])
                rec["guard_saturated"] = all(v == 9 for v in rec["guard_weights"].values())
                applies.append(rec)
        certs.append({"certificate": cert, "classification": cls, "applications": applies})

    support_summaries = []
    for lab, sup in [("L15", L15), ("trace_inconsistent_9v", TRACE_INCONSISTENT_9V), ("trace_consistent_9v", TRACE_CONSISTENT_9V)] + load_mutation_supports():
        support_summaries.append(analyze_support(lab, sup))

    # Recheck the GF2-vs-real-rank pitfall explicitly.
    rank_mismatch = []
    for lam in range(1, 256):
        M = lambda_to_mat(lam)
        rg = gf2_rank(M)
        rr = int(np.linalg.matrix_rank(M.astype(float)))
        if rg != rr:
            rank_mismatch.append({"lambda": lam, "gf2_rank": rg, "real_rank": rr, "matrix": M.tolist()})

    payload = {
        "schema": "s0908_shadow_certificate_analysis_v1",
        "field": "F2",
        "purpose": "Extract exact row-combination contradictions from the corrected 3x3 shadow system and translate them into guarded support relations.",
        "l15_tight_rank9": l15_tight,
        "rank_mismatch_gf2_vs_real": rank_mismatch,
        "certificates": certs,
        "support_summaries": support_summaries,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    # Print concise scientific summary.
    short = {
        "out": str(args.out),
        "rank_mismatch_gf2_vs_real": rank_mismatch,
        "certificate_brief": [
            {
                "name": c["certificate"]["name"],
                "guard": c["certificate"].get("guard_lambdas_used"),
                "row_count": c["certificate"].get("certificate_row_count"),
                "type_counts": c["certificate"].get("type_counts"),
                "tensor_rhs": c["certificate"].get("tensor_rhs"),
                "class_counts": None if c["classification"] is None else c["classification"]["class_counts"],
                "forced_value_counts": None if c["classification"] is None else c["classification"]["forced_value_counts"],
                "L15_application": next((a for a in c["applications"] if a["label"] == "L15"), None),
            }
            for c in certs
        ],
        "support_summaries": [{k: s[k] for k in ["label", "tight_rank9_count", "shadow_consistent", "rank", "augmented_rank"]} for s in support_summaries],
    }
    print(json.dumps(short, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
