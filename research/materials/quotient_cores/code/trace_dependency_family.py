#!/usr/bin/env python3
r"""analysis: sound family restrictions from corrected trace dependencies.

This script repairs the analysis interpretation of trace-parity information.
The 72 rank-9 corrected trace functionals phi_q live in a 9-dimensional
space, but for a selected A-direction p only functionals with q(p)=1 apply to
that term under a saturated contraction q.  For a guard set G of saturated
rank-9 contractions and a direction p, write H_p=G∩{q:q(p)=1}.

Classification under G:
  * inconsistent: phi_q, q in H_p, have an odd linear dependency.  Since
    saturation imposes phi_q(X_s)=1 for all q in H_p, the dependency gives
    0=1 for any selected term with direction p.
  * forced: the local system is consistent and the certificate tensor
    functional F(p) lies in span{phi_q:q in H_p}; its value is then fixed.
  * free: the local system is consistent but F(p) is outside the available
    span, so no pure support parity row may be imposed without an explicit
    evaluation variable.

The first case yields reusable, certificate-independent cuts.  If an odd
trace dependency H is hit by p (q(p)=1 for every q in H), then for a distinct
support with rank-9 contraction lower bounds w(q)>=9,

    x_p = 1  =>  at least one q in H has w(q) >= 10,

or equivalently

    sum_{q in H} (w(q)-9) >= x_p.

These are necessary B/C compatibility cuts; they are not tensor-rank lower
bounds by themselves and do not replace complete Wang occupation.
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"
CERT_PATH = ROOT / "workspace/data/corrected_independent-verification-record"
CAND_PATH = ROOT / "workspace/data/completion/distinct_candidate_completion_repaired.json"
NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def popcount(x: int) -> int:
    return int(x).bit_count()


def dot8(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def trace_mask_correct(M_inv: np.ndarray) -> int:
    """81-bit mask for phi(X)=tr(M_inv X), variables ordered X[b,c]."""
    mask = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c, b]) & 1:
                mask |= 1 << (b * 9 + c)
    return mask


def matrix_mask(M: np.ndarray) -> int:
    n, m = M.shape
    mask = 0
    for i in range(n):
        for j in range(m):
            if int(M[i, j]) & 1:
                mask |= 1 << (i * m + j)
    return mask


def dot_masks(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def gf2_rank(vecs: Sequence[int]) -> int:
    basis: List[int] = []
    for raw in vecs:
        v = int(raw)
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def gf2_in_span_with_decomp(target: int, generators: Sequence[int]) -> Tuple[bool, Optional[int]]:
    """Return a generator mask expressing target, if one exists.

    The returned expression is not canonical, but if all dependencies among the
    generators have even cardinality then its parity is well-defined.
    """
    basis: List[Tuple[int, int]] = []
    for i, g0 in enumerate(generators):
        v = int(g0)
        m = 1 << i
        for bv, bm in basis:
            v2 = v ^ bv
            if v2 < v:
                v, m = v2, m ^ bm
        if v:
            basis.append((v, m))
            basis.sort(reverse=True)
    v = int(target)
    m = 0
    for bv, bm in basis:
        v2 = v ^ bv
        if v2 < v:
            v, m = v2, m ^ bm
    if v == 0:
        return True, m
    return False, None


def min_odd_dependency(qs: Sequence[int], phi: Dict[int, int]) -> Optional[List[int]]:
    """Shortest odd-cardinality subset H⊆qs with xor_{q∈H} phi_q = 0.

    Dynamic programming over at most 2^rank states, with parity tracked
    explicitly.  Returns None if the affine system phi_q(X)=1 is locally
    consistent for these generators.
    """
    if not qs:
        return None
    # map (state, parity) -> (weight, mask over local qs)
    best: Dict[Tuple[int, int], Tuple[int, int]] = {(0, 0): (0, 0)}
    for i, q in enumerate(qs):
        vq = int(phi[int(q)])
        cur = dict(best)
        bit = 1 << i
        for (state, par), (wt, mask) in best.items():
            ns = state ^ vq
            np = par ^ 1
            nw = wt + 1
            nm = mask | bit
            key = (ns, np)
            old = cur.get(key)
            if old is None or nw < old[0] or (nw == old[0] and nm < old[1]):
                cur[key] = (nw, nm)
        best = cur
    ans = best.get((0, 1))
    if ans is None or ans[0] == 0:
        return None
    _wt, mask = ans
    return [int(qs[i]) for i in range(len(qs)) if (mask >> i) & 1]


def enumerate_triple_dependencies(qs: Sequence[int], phi: Dict[int, int]) -> List[List[int]]:
    """All 3-term dependencies among qs, returned as sorted q triples."""
    idx_by_phi: Dict[int, List[int]] = defaultdict(list)
    for q in qs:
        idx_by_phi[int(phi[int(q)])].append(int(q))
    triples = set()
    qlist = [int(q) for q in qs]
    for i in range(len(qlist)):
        qi = qlist[i]
        for j in range(i + 1, len(qlist)):
            qj = qlist[j]
            need = phi[qi] ^ phi[qj]
            for qk in idx_by_phi.get(need, []):
                if qk <= qj:
                    continue
                triples.add(tuple(sorted((qi, qj, qk))))
    return [list(t) for t in sorted(triples)]


def load_candidate_supports() -> List[dict]:
    supports: List[dict] = [{"name": "near_miss_primary", "A_cols": NEAR_MISS, "source": "analysis", "complete_wang_violations": 12}]
    if CAND_PATH.exists():
        data = json.loads(CAND_PATH.read_text())
        seen = {tuple(NEAR_MISS)}
        for rec in data.get("best_analyses", []):
            A = rec.get("A_cols")
            if not A:
                continue
            tup = tuple(int(x) for x in A)
            if tup in seen:
                continue
            seen.add(tup)
            supports.append({
                "name": rec.get("name", f"candidate_{len(supports)}"),
                "A_cols": list(tup),
                "source": "completion/distinct_candidate_completion_repaired.json",
                "complete_wang_violations": rec.get("complete_wang_violations"),
                "max_excess": rec.get("max_excess"),
            })
    return supports


def build_certificate_tensor_functional(T_core: np.ndarray) -> dict:
    cert = json.loads(CERT_PATH.read_text())
    labels = cert["full_greedy_row_shrink"]["labels"]
    tensor_masks: Dict[Tuple[int, int], int] = {}
    trace_labels: List[Tuple[int, int]] = []
    tensor_rhs = 0
    trace_rhs = 0
    tensor_count = 0
    for lbl in labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_masks[(b, c)] = tensor_masks.get((b, c), 0) ^ (1 << i)
            tensor_rhs ^= int(T_core[i, b, c]) & 1
            tensor_count += 1
        elif lbl[0] == "trace":
            q, s = int(lbl[1]), int(lbl[2])
            trace_labels.append((q, s))
            trace_rhs ^= 1
    return {
        "labels": labels,
        "tensor_masks": {f"{b},{c}": int(mask) for (b, c), mask in sorted(tensor_masks.items())},
        "tensor_masks_raw": tensor_masks,
        "trace_labels": trace_labels,
        "guard_qs": sorted(set(q for q, _s in trace_labels)),
        "tensor_rhs_parity": int(tensor_rhs),
        "trace_rhs_parity": int(trace_rhs),
        "total_rhs_parity": int(tensor_rhs ^ trace_rhs),
        "tensor_row_count": int(tensor_count),
        "trace_row_count": len(trace_labels),
    }


def compute_F_for_p(p: int, tensor_masks: Dict[Tuple[int, int], int]) -> int:
    mask81 = 0
    for b in range(9):
        for c in range(9):
            coord_mask = tensor_masks.get((b, c), 0)
            if popcount(int(p) & coord_mask) & 1:
                mask81 |= 1 << (b * 9 + c)
    return mask81


def classify_directions_under_guard(guard_qs: Sequence[int], tensor_masks: Dict[Tuple[int, int], int], phi: Dict[int, int]) -> Tuple[List[dict], dict]:
    records = []
    counts = Counter()
    for p in range(1, 256):
        hits = [int(q) for q in guard_qs if dot8(q, p)]
        odd_dep = min_odd_dependency(hits, phi)
        Fp = compute_F_for_p(p, tensor_masks)
        base = {
            "p": p,
            "hit_count": len(hits),
            "hit_rank": gf2_rank([phi[q] for q in hits]),
            "F_weight": popcount(Fp),
        }
        if odd_dep is not None:
            rec = {**base, "class": "inconsistent", "odd_dependency": odd_dep, "odd_dependency_size": len(odd_dep)}
            counts["inconsistent"] += 1
        else:
            ok, dec = gf2_in_span_with_decomp(Fp, [phi[q] for q in hits])
            if ok:
                val = popcount(dec or 0) & 1
                used = [hits[i] for i in range(len(hits)) if ((dec or 0) >> i) & 1]
                rec = {**base, "class": "forced", "forced_value": val, "forcing_qs": used}
                counts[f"forced_{val}"] += 1
                counts["forced"] += 1
            else:
                rec = {**base, "class": "free"}
                counts["free"] += 1
        records.append(rec)
    summary = {str(k): int(v) for k, v in sorted(counts.items())}
    summary["total"] = len(records)
    return records, summary


def support_weights(support: Sequence[int], qs: Sequence[int]) -> Dict[int, int]:
    A = [int(x) for x in support]
    return {int(q): sum(1 for p in A if dot8(q, p)) for q in qs}


def eval_support_local_dependency(support: Sequence[int], rank9_qs: Sequence[int], phi: Dict[int, int], minimal_witness_by_p: Dict[int, Optional[List[int]]]) -> dict:
    A = [int(x) for x in support]
    weights = support_weights(A, rank9_qs)
    exact_bad = []
    min_cut_bad = []
    saturated_qs = [q for q in rank9_qs if weights[q] == 9]
    for p in A:
        sat_hits = [q for q in saturated_qs if dot8(q, p)]
        odd_dep = min_odd_dependency(sat_hits, phi)
        if odd_dep is not None:
            exact_bad.append({"p": p, "witness": odd_dep, "size": len(odd_dep)})
        mw = minimal_witness_by_p.get(p)
        if mw is not None and all(weights[q] == 9 for q in mw):
            min_cut_bad.append({"p": p, "witness": mw, "size": len(mw)})
    return {
        "saturated_rank9_count": len(saturated_qs),
        "exact_local_inconsistent_terms": len(exact_bad),
        "exact_local_inconsistent_examples": exact_bad[:10],
        "minimal_cut_violations": len(min_cut_bad),
        "minimal_cut_examples": min_cut_bad[:10],
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()

    # Build corrected trace masks for rank-9 contractions.
    phi: Dict[int, int] = {}
    rank_hist = Counter()
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        rank_hist[int(rk)] += 1
        if rk == 9:
            M_inv = gf2_mat_inv(M)
            if M_inv is None:
                raise RuntimeError(f"rank-9 contraction {q} was not invertible")
            phi[q] = trace_mask_correct(M_inv)
    rank9_qs = sorted(phi)
    phi_rank = gf2_rank([phi[q] for q in rank9_qs])

    # Per-direction odd-dependency witnesses and small triple counts.
    direction_records = []
    minimal_witness_by_p: Dict[int, Optional[List[int]]] = {}
    triple_witnesses_by_p: Dict[int, List[List[int]]] = {}
    for p in range(1, 256):
        hits = [q for q in rank9_qs if dot8(q, p)]
        min_dep = min_odd_dependency(hits, phi)
        triples = enumerate_triple_dependencies(hits, phi)
        minimal_witness_by_p[p] = min_dep
        triple_witnesses_by_p[p] = triples
        direction_records.append({
            "p": p,
            "hit_count": len(hits),
            "hit_rank": gf2_rank([phi[q] for q in hits]),
            "has_odd_dependency": min_dep is not None,
            "min_odd_dependency_size": None if min_dep is None else len(min_dep),
            "min_odd_dependency": min_dep,
            "triple_dependency_count": len(triples),
            "triple_dependency_sample": triples[:5],
        })

    dep_size_hist = Counter(r["min_odd_dependency_size"] if r["min_odd_dependency_size"] is not None else "none" for r in direction_records)
    triple_count_hist = Counter(r["triple_dependency_count"] for r in direction_records)
    no_odd = [r["p"] for r in direction_records if not r["has_odd_dependency"]]

    # Cut file: one minimal cut per direction where available, plus all triples.
    minimal_cuts = []
    triple_cuts = []
    seen_triple_cuts = set()
    for p in range(1, 256):
        dep = minimal_witness_by_p[p]
        if dep is not None:
            minimal_cuts.append({
                "p": p,
                "H": dep,
                "size": len(dep),
                "inequality": "sum_{q in H}(w(q)-9) >= x_p",
            })
        for tri in triple_witnesses_by_p[p]:
            key = (p, tuple(tri))
            if key in seen_triple_cuts:
                continue
            seen_triple_cuts.add(key)
            triple_cuts.append({"p": p, "H": tri, "size": 3, "inequality": "sum_{q in H}(w(q)-9) >= x_p"})

    # Evaluate known near-misses by exact local odd-dependency status.
    candidates = load_candidate_supports()
    candidate_records = []
    for cand in candidates:
        ev = eval_support_local_dependency(cand["A_cols"], rank9_qs, phi, minimal_witness_by_p)
        candidate_records.append({
            "name": cand.get("name"),
            "complete_wang_violations": cand.get("complete_wang_violations"),
            "support": cand["A_cols"],
            **ev,
        })

    # Reclassify the primary analysis certificate guard correctly.
    cert_info = build_certificate_tensor_functional(T_core)
    cert_records, cert_summary = classify_directions_under_guard(cert_info["guard_qs"], cert_info["tensor_masks_raw"], phi)
    nm_class_counts = Counter()
    nm_forced_sum = 0
    nm_all_forced = True
    nm_has_inconsistent = False
    nm_free = False
    rec_by_p = {r["p"]: r for r in cert_records}
    nm_records = []
    for p in NEAR_MISS:
        rec = rec_by_p[p]
        nm_records.append(rec)
        nm_class_counts[rec["class"]] += 1
        if rec["class"] == "inconsistent":
            nm_has_inconsistent = True
            nm_all_forced = False
        elif rec["class"] == "forced":
            nm_forced_sum ^= int(rec["forced_value"])
        else:
            nm_free = True
            nm_all_forced = False
    parity_applicable = (not nm_has_inconsistent) and (not nm_free) and nm_all_forced
    parity_contradiction = bool(parity_applicable and (nm_forced_sum != cert_info["tensor_rhs_parity"]))

    cert_classification = {
        "source_certificate": str(CERT_PATH),
        "guard_qs": cert_info["guard_qs"],
        "tensor_row_count": cert_info["tensor_row_count"],
        "trace_row_count": cert_info["trace_row_count"],
        "tensor_rhs_parity": cert_info["tensor_rhs_parity"],
        "trace_rhs_parity": cert_info["trace_rhs_parity"],
        "total_rhs_parity": cert_info["total_rhs_parity"],
        "class_summary": cert_summary,
        "class_records": cert_records,
        "near_miss_class_counts": {str(k): int(v) for k, v in sorted(nm_class_counts.items())},
        "near_miss_selected_records": nm_records,
        "near_miss_parity_applicable": parity_applicable,
        "near_miss_forced_sum": int(nm_forced_sum),
        "near_miss_parity_contradiction": parity_contradiction,
        "interpretation": "Pure parity under this guard is valid only for supports selecting no 'free' directions and no locally inconsistent directions; locally inconsistent directions are forbidden under the guard.",
    }

    analysis = {
        "schema": "trace_dependency_family_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "meaning": "Corrected trace dependency family restrictions for distinct 19-point supports; supports complete Wang search but is not a standalone lower bound.",
        "elapsed_sec": round(time.time() - t0, 3),
        "rank_distribution_nonzero_q": {str(k): int(v) for k, v in sorted(rank_hist.items())},
        "rank9_contraction_count": len(rank9_qs),
        "trace_functional_span_rank": phi_rank,
        "direction_summary": {
            "directions": len(direction_records),
            "min_odd_dependency_size_hist": {str(k): int(v) for k, v in sorted(dep_size_hist.items(), key=lambda kv: str(kv[0]))},
            "no_odd_dependency_directions": no_odd,
            "triple_dependency_count_hist_sample": {str(k): int(v) for k, v in sorted(triple_count_hist.items())[:30]},
            "directions_with_triples": sum(1 for r in direction_records if r["triple_dependency_count"] > 0),
            "total_triple_cuts": len(triple_cuts),
            "minimal_cut_count": len(minimal_cuts),
        },
        "direction_records": direction_records,
        "candidate_evaluation_summary": {
            "candidate_count": len(candidate_records),
            "exact_local_inconsistent_supports": sum(1 for r in candidate_records if r["exact_local_inconsistent_terms"] > 0),
            "minimal_cut_rejected_supports": sum(1 for r in candidate_records if r["minimal_cut_violations"] > 0),
        },
        "candidate_evaluations": candidate_records,
        "primary_certificate_classification": cert_classification,
    }

    cut_payload = {
        "schema": "trace_dependency_cut_family_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "assumptions": [
            "distinct support variables x_p in {0,1}",
            "rank-9 contraction lower bounds w(q)=sum_{p:q(p)=1} x_p >= 9 are included",
        ],
        "sound_cut": "for each odd dependency H hit by p, sum_{q in H}(w(q)-9) >= x_p",
        "rank9_qs": rank9_qs,
        "minimal_cuts": minimal_cuts,
        "triple_cuts": triple_cuts,
    }

    analysis_path = OUTDIR / "trace_dependency_cut_analysis.json"
    cut_path = OUTDIR / "trace_dependency_cuts.json"
    analysis_path.write_text(json.dumps(analysis, indent=2, sort_keys=True) + "\n")
    cut_path.write_text(json.dumps(cut_payload, indent=2, sort_keys=True) + "\n")

    print(json.dumps({
        "analysis": str(analysis_path),
        "cuts": str(cut_path),
        "rank9": len(rank9_qs),
        "phi_rank": phi_rank,
        "min_odd_dependency_size_hist": analysis["direction_summary"]["min_odd_dependency_size_hist"],
        "no_odd_dependency_directions": no_odd,
        "minimal_cuts": len(minimal_cuts),
        "triple_cuts": len(triple_cuts),
        "candidate_summary": analysis["candidate_evaluation_summary"],
        "primary_cert_class_summary": cert_summary,
        "near_miss_cert_classes": cert_classification["near_miss_class_counts"],
        "near_miss_parity_applicable": parity_applicable,
        "near_miss_parity_contradiction": parity_contradiction,
        "elapsed_sec": analysis["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
