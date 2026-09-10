#!/usr/bin/env python3
r"""analysis: enumerate size-5 odd trace-dependency cuts.

For each core A-direction p, let H_p be the rank-9 contractions q with q(p)=1.
A 5-subset D of H_p with xor_{q in D} phi_q=0 gives the sound cut
    sum_{q in D} (w(q)-9) >= x_p.
This script enumerates all such size-5 cuts, measures them on stored supports,
and stores both a compact pickle of the cuts and a JSON summary.
"""
from __future__ import annotations

import itertools
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from trace_dependency_family import (  # noqa: E402
    OUTDIR,
    build_e11_core_tensor,
    contraction_matrix,
    dot8,
    eval_support_local_dependency,
    gf2_rank,
    load_candidate_supports,
    mat_rank_f2,
    min_odd_dependency,
    trace_mask_correct,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402


def enumerate_size5_for_hits(hits: Sequence[int], phi: Dict[int, int]) -> List[Tuple[int, int, int, int, int]]:
    """All sorted five-tuples from hits whose phi xor is zero."""
    hits = sorted(int(q) for q in hits)
    # Build pair xor groups.
    pairs_by_xor: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    n = len(hits)
    for i in range(n):
        qi = hits[i]
        for j in range(i + 1, n):
            qj = hits[j]
            pairs_by_xor[phi[qi] ^ phi[qj]].append((qi, qj))
    cuts = set()
    # A zero 5-subset is a disjoint pair plus triple with equal xor.
    for a in range(n):
        qa = hits[a]
        for b in range(a + 1, n):
            qb = hits[b]
            ab = {qa, qb}
            for c in range(b + 1, n):
                qc = hits[c]
                need = phi[qa] ^ phi[qb] ^ phi[qc]
                for qd, qe in pairs_by_xor.get(need, []):
                    if qd in ab or qe in ab or qd == qc or qe == qc:
                        continue
                    tup = tuple(sorted((qa, qb, qc, qd, qe)))
                    if len(set(tup)) == 5:
                        cuts.add(tup)
    return sorted(cuts)


def support_weights(support: Sequence[int], rank9_qs: Sequence[int]) -> Dict[int, int]:
    return {int(q): sum(1 for p in support if dot8(q, int(p))) for q in rank9_qs}


def eval_candidate_size5(cand: dict, cuts_by_p: Dict[int, List[Tuple[int, ...]]], rank9_qs: Sequence[int]) -> dict:
    A = [int(x) for x in cand["A_cols"]]
    weights = support_weights(A, rank9_qs)
    sat = {q for q, w in weights.items() if w == 9}
    violations = []
    for p in A:
        for H in cuts_by_p.get(p, []):
            if all(q in sat for q in H):
                violations.append({"p": p, "H": list(H)})
                break
    return {
        "name": cand.get("name"),
        "complete_wang_violations": cand.get("complete_wang_violations"),
        "saturated_rank9_count": len(sat),
        "size5_cut_violations": len(violations),
        "size5_cut_examples": violations[:10],
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()

    phi: Dict[int, int] = {}
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            M_inv = gf2_mat_inv(M)
            if M_inv is None:
                raise RuntimeError(q)
            phi[q] = trace_mask_correct(M_inv)
    rank9_qs = sorted(phi)

    cuts_by_p: Dict[int, List[Tuple[int, ...]]] = {}
    summary_records = []
    total_cuts = 0
    for p in range(1, 256):
        hits = [q for q in rank9_qs if dot8(q, p)]
        min_dep = min_odd_dependency(hits, phi)
        if min_dep is None or len(min_dep) != 5:
            cuts = []
        else:
            cuts = enumerate_size5_for_hits(hits, phi)
        cuts_by_p[p] = cuts
        total_cuts += len(cuts)
        summary_records.append({
            "p": p,
            "hit_count": len(hits),
            "hit_rank": gf2_rank([phi[q] for q in hits]),
            "size5_cut_count": len(cuts),
            "sample": [list(x) for x in cuts[:5]],
        })
        if p % 32 == 0:
            print(f"p={p:3d} cumulative_size5={total_cuts}")

    count_hist = Counter(r["size5_cut_count"] for r in summary_records)
    nonzero = [r for r in summary_records if r["size5_cut_count"]]
    print(f"Total size-5 cuts: {total_cuts}; directions with cuts: {len(nonzero)}")

    # Evaluate stored candidates.
    candidates = load_candidate_supports()
    cand_evals = [eval_candidate_size5(c, cuts_by_p, rank9_qs) for c in candidates]

    # Compare against exact local odd-dependency status from analysis family script.
    exact_evals = []
    for c in candidates:
        exact_evals.append({
            "name": c.get("name"),
            **eval_support_local_dependency(c["A_cols"], rank9_qs, phi, {p: None for p in range(1, 256)}),
        })

    payload = {
        "schema": "trace_dependency_size5_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "rank9_qs": rank9_qs,
        "total_size5_cuts": total_cuts,
        "directions_with_size5_cuts": len(nonzero),
        "size5_count_hist": {str(k): int(v) for k, v in sorted(count_hist.items())},
        "per_direction_summary": summary_records,
        "candidate_evaluations": cand_evals,
        "candidate_summary": {
            "candidate_count": len(cand_evals),
            "size5_rejected": sum(1 for r in cand_evals if r["size5_cut_violations"] > 0),
            "total_candidate_cut_violations": sum(r["size5_cut_violations"] for r in cand_evals),
        },
    }
    json_path = OUTDIR / "trace_dependency_size5_summary.json"
    pkl_path = OUTDIR / "trace_dependency_size5_cuts.pkl"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    with pkl_path.open("wb") as f:
        pickle.dump({"rank9_qs": rank9_qs, "cuts_by_p": cuts_by_p}, f, protocol=pickle.HIGHEST_PROTOCOL)

    print(json.dumps({
        "json": str(json_path),
        "pickle": str(pkl_path),
        "total_size5_cuts": total_cuts,
        "directions_with_size5_cuts": len(nonzero),
        "candidate_summary": payload["candidate_summary"],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
