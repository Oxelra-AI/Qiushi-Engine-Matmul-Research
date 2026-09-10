#!/usr/bin/env python3
r"""analysis: rebuild sound guarded family cuts from corrected trace certificates.

For each trace-inconsistent stored support, extract a GF(2) XOR certificate from
its corrected tensor+trace relaxation.  The used trace rows define a saturation
guard G, and the used tensor rows define a certificate tensor functional F.
For every possible A-direction p, classify the local affine system under G:

  inconsistent: {phi_q(X)=1 : q in G, q(p)=1} already contradicts a trace
      dependency.  Then x_p=1 forces at least one q in the witnessing dependency
      to be non-saturated.
  forced: consistent, and F(p) lies in span of available phi_q's; its value is
      fixed.
  free: consistent, but F(p) is not forced; parity using this certificate is
      not a pure support row if such a direction is selected.

The resulting support-level cuts are necessary conditions, not a complete B/C
solver.  They repair analysis's overcompressed parity interpretation.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    gf2_linear_consistency,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from trace_dependency_family import (  # noqa: E402
    OUTDIR,
    compute_F_for_p,
    dot8,
    gf2_in_span_with_decomp,
    load_candidate_supports,
    min_odd_dependency,
    trace_mask_correct,
)


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def build_phi_vectors(T_core: np.ndarray) -> Dict[int, int]:
    phi: Dict[int, int] = {}
    for q in range(1, 1 << T_core.shape[0]):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        inv = gf2_mat_inv(M)
        if inv is None:
            raise RuntimeError(f"rank-9 contraction not invertible: {q}")
        phi[int(q)] = trace_mask_correct(inv)
    return phi


def build_trace_system(T_core: np.ndarray, A_support: Sequence[int]):
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc

    def vi(s: int, b: int, c: int) -> int:
        return s * nb * nc + b * nc + c

    rows: List[int] = []
    labels: List[Tuple] = []
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    if (int(a) >> i) & 1:
                        row ^= 1 << vi(s, b, c)
                row |= (int(T_core[i, b, c]) & 1) << nvars
                rows.append(row)
                labels.append(("tensor", i, b, c))
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        I = [s for s, a in enumerate(A_support) if dot8(int(q), int(a))]
        if len(I) != 9:
            continue
        M_inv = gf2_mat_inv(M)
        if M_inv is None:
            continue
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    if int(M_inv[c, b]) & 1:
                        row ^= 1 << vi(s, b, c)
            row |= 1 << nvars
            rows.append(row)
            labels.append(("trace", int(q), int(s)))
    return rows, labels, nvars


def extract_certificate(labels: Sequence[Tuple], cert_mask: int, T_core: np.ndarray, phi: Dict[int, int]) -> dict:
    tensor_masks: Dict[Tuple[int, int], int] = {}
    tensor_rhs = 0
    trace_rhs = 0
    trace_labels = []
    used_labels = []
    for idx, lbl in enumerate(labels):
        if ((cert_mask >> idx) & 1) == 0:
            continue
        used_labels.append(tuple(lbl))
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_masks[(b, c)] = tensor_masks.get((b, c), 0) ^ (1 << i)
            tensor_rhs ^= int(T_core[i, b, c]) & 1
        elif lbl[0] == "trace":
            q, s = int(lbl[1]), int(lbl[2])
            trace_labels.append((q, s))
            trace_rhs ^= 1
    guard_qs = sorted(set(q for q, _s in trace_labels))
    assert tensor_rhs ^ trace_rhs == 1, "XOR certificate must have odd RHS"

    class_records = []
    for p in range(1, 256):
        hits = [q for q in guard_qs if dot8(q, p)]
        Fp = compute_F_for_p(p, tensor_masks)
        odd_dep = min_odd_dependency(hits, phi)
        if odd_dep is not None:
            rec = {"p": p, "class": "inconsistent", "hit_count": len(hits), "witness": odd_dep, "witness_size": len(odd_dep)}
        else:
            ok, dec = gf2_in_span_with_decomp(Fp, [phi[q] for q in hits])
            if ok:
                dec = dec or 0
                used = [hits[i] for i in range(len(hits)) if (dec >> i) & 1]
                rec = {"p": p, "class": "forced", "hit_count": len(hits), "forced_value": dec.bit_count() & 1, "forcing_qs": used}
            else:
                rec = {"p": p, "class": "free", "hit_count": len(hits)}
        class_records.append(rec)

    cnt = Counter(r["class"] for r in class_records)
    cnt.update({f"forced_{r.get('forced_value')}": 1 for r in []})
    forced_val_counts = Counter(r.get("forced_value") for r in class_records if r["class"] == "forced")
    summary = {
        "inconsistent": int(cnt.get("inconsistent", 0)),
        "forced": int(cnt.get("forced", 0)),
        "forced_0": int(forced_val_counts.get(0, 0)),
        "forced_1": int(forced_val_counts.get(1, 0)),
        "free": int(cnt.get("free", 0)),
        "total": len(class_records),
    }

    return {
        "guard_qs": guard_qs,
        "tensor_rhs_parity": int(tensor_rhs),
        "trace_rhs_parity": int(trace_rhs),
        "total_rhs_parity": int(tensor_rhs ^ trace_rhs),
        "used_row_count": len(used_labels),
        "used_label_type_counts": {k: int(v) for k, v in Counter(lbl[0] for lbl in used_labels).items()},
        "trace_row_count": len(trace_labels),
        "class_summary": summary,
        "inconsistent_directions": [r for r in class_records if r["class"] == "inconsistent"],
        "forced_1_directions": [r["p"] for r in class_records if r["class"] == "forced" and r.get("forced_value") == 1],
        "forced_0_directions": [r["p"] for r in class_records if r["class"] == "forced" and r.get("forced_value") == 0],
        "free_directions": [r["p"] for r in class_records if r["class"] == "free"],
        "class_records": class_records,
        "used_label_sample": [list(x) for x in used_labels[:80]],
    }


def evaluate_on_support(cert: dict, support: Sequence[int]) -> dict:
    by_p = {r["p"]: r for r in cert["class_records"]}
    cnt = Counter()
    forced_sum = 0
    examples = []
    for p0 in support:
        p = int(p0)
        rec = by_p[p]
        cnt[rec["class"]] += 1
        if rec["class"] == "forced":
            forced_sum ^= int(rec["forced_value"])
        elif rec["class"] == "inconsistent" and len(examples) < 5:
            examples.append({"p": p, "witness": rec.get("witness")})
    pure_parity_applicable = (cnt.get("free", 0) == 0 and cnt.get("inconsistent", 0) == 0)
    pure_parity_contradiction = bool(pure_parity_applicable and forced_sum != cert["tensor_rhs_parity"])
    local_inconsistent = cnt.get("inconsistent", 0) > 0
    return {
        "support_class_counts": {str(k): int(v) for k, v in sorted(cnt.items())},
        "forced_sum": int(forced_sum),
        "pure_parity_applicable": pure_parity_applicable,
        "pure_parity_contradiction": pure_parity_contradiction,
        "has_local_inconsistent_direction_under_guard": bool(local_inconsistent),
        "local_inconsistent_examples": examples,
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()
    phi = build_phi_vectors(T_core)
    candidates = load_candidate_supports()
    certs = []
    for idx, cand in enumerate(candidates):
        A = [int(x) for x in cand["A_cols"]]
        rows, labels, nvars = build_trace_system(T_core, A)
        ok, rank, cert_mask = gf2_linear_consistency(rows, nvars)
        if ok or cert_mask is None:
            continue
        cert = extract_certificate(labels, int(cert_mask), T_core, phi)
        self_eval = evaluate_on_support(cert, A)
        cert_rec = {
            "cert_index": len(certs),
            "source_candidate_index": idx,
            "source_name": cand.get("name"),
            "source_complete_wang_violations": cand.get("complete_wang_violations"),
            "source_support": A,
            "full_trace_system_rows": len(rows),
            "full_trace_system_rank": int(rank),
            "source_self_evaluation": self_eval,
            **cert,
        }
        certs.append(cert_rec)
        print(f"cert {len(certs)-1}: {cand.get('name')} guard={len(cert['guard_qs'])} classes={cert['class_summary']} self={self_eval}")

    # Cross-apply the pure support consequence of every certificate to every stored support.
    cross = []
    for ci, cert in enumerate(certs):
        for cj, cand in enumerate(candidates):
            ev = evaluate_on_support(cert, cand["A_cols"])
            if ev["pure_parity_contradiction"] or ev["has_local_inconsistent_direction_under_guard"]:
                cross.append({
                    "cert_index": ci,
                    "cert_name": cert["source_name"],
                    "target_index": cj,
                    "target_name": cand.get("name"),
                    "target_complete_wang_violations": cand.get("complete_wang_violations"),
                    **ev,
                })
    payload = {
        "schema": "trace_certificate_family_cuts_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "field": "F2",
        "core": "E11 quotient core",
        "meaning": "Correct classification of trace-certificate support consequences into inconsistent, forced, and free directions. Pure parity rows are conditional on the saturation guard and absence of selected free/inconsistent directions; inconsistent directions give guarded local cuts.",
        "certificate_count": len(certs),
        "certificates": certs,
        "cross_application_records": cross,
        "cross_summary": {
            "stored_support_count": len(candidates),
            "cross_records": len(cross),
            "targets_hit": len(set(r["target_name"] for r in cross)),
            "certs_with_hits": len(set(r["cert_index"] for r in cross)),
        },
    }
    out = OUTDIR / "trace_certificate_family_cuts.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "certificate_count": len(certs),
        "cross_summary": payload["cross_summary"],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
