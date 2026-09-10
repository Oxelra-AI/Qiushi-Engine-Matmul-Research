#!/usr/bin/env python3
"""Audit the dim-2 Wang-orbit reduction suggested in analysis.

The purpose is to verify, directly from Wang's recorded dim-2 orbit data and
our local occupation-closure overlay, which two-dimensional A-subspaces can be
spanned by two independent matrix-rank >=2 directions.  These are exactly the
subspaces with at least two nonzero elements of matrix rank >=2.

If a hypothetical length-20 full decomposition exists, the A-slot flattening
bound gives sum_t (rank(a_t)-1) >= 7.  After choosing one rank>=2 A-factor p,
at least three other rank>=2 A-factors remain.  If one repeats p, quotient by
<p> leaves <=18 terms, contradicting Wang LB(<p>)=19.  Otherwise choose an
independent remaining rank>=2 factor a; quotient by W=<p,a> leaves <=18 terms.
Thus only relevant dim-2 orbit representatives with current lower bound <19
remain as quotient-rank targets.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

PROFILE = Path("data/wang_f2_lb20/cert_profile.json")
NODE_ORIG = Path("data/wang_analysis/node_local/dim2_raise_original.json")
CASCADE = Path("data/wang_analysis/cascade/dim3_raises_to_dim2.json")
OUT = Path("data/wang_analysis/dim2_reduction_audit.json")
NOTE = Path("notes/dim2_reduction_audit.md")


def bits_to_rows(x: int) -> list[int]:
    rows = [0, 0, 0]
    for idx in range(9):
        if (int(x) >> idx) & 1:
            i, j = divmod(idx, 3)
            rows[i] |= 1 << j
    return rows


def rank3(x: int) -> int:
    basis = [0, 0, 0]
    r = 0
    for row in bits_to_rows(x):
        y = row
        while y:
            p = y.bit_length() - 1
            if basis[p]:
                y ^= basis[p]
            else:
                basis[p] = y
                r += 1
                break
    return r


def nonzero_span(basis: Sequence[int]) -> list[int]:
    out = []
    for m in range(1, 1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        out.append(v)
    return sorted(out)


def mat_str(x: int) -> str:
    rows = []
    for i in range(3):
        rows.append("".join("1" if (x >> (3*i+j)) & 1 else "." for j in range(3)))
    return "/".join(rows)


def load_overlay() -> dict[int, int]:
    overlay: dict[int, int] = {}
    if CASCADE.exists():
        d = json.loads(CASCADE.read_text())
        for k, v in d.get("all_raises_after_tests", {}).items():
            overlay[int(k)] = int(v)
    return overlay


def load_node_status() -> dict[int, dict]:
    status = {}
    for path in [NODE_ORIG, CASCADE]:
        if not path.exists():
            continue
        d = json.loads(path.read_text())
        if "results" in d and isinstance(d["results"], list):
            records = d["results"]
        elif "results" in d and isinstance(d["results"], dict):
            records = []
            for vv in d["results"].values():
                if isinstance(vv, list):
                    records.extend(vv)
        else:
            records = []
        for rec in records:
            if int(rec.get("dim", -1)) == 2:
                idx = int(rec.get("cert_index", rec.get("position", -1)))
                status[idx] = rec
    return status


def main() -> None:
    profile = json.loads(PROFILE.read_text())
    dim2 = profile["dimension_2_orbits"]
    overlay = load_overlay()
    node_status = load_node_status()
    records = []
    for rec in dim2:
        idx = int(rec["index"])
        basis = [int(x) for x in rec["constraint_values"]]
        nz = nonzero_span(basis)
        ranks = [rank3(x) for x in nz]
        hist = dict(sorted(Counter(ranks).items()))
        rank_ge2_count = sum(1 for r in ranks if r >= 2)
        relevant = rank_ge2_count >= 2
        old_lb = int(rec["rank_lower_bound"])
        current_lb = int(overlay.get(idx, old_lb))
        status_rec = node_status.get(idx, {})
        out = {
            "index": idx,
            "basis": basis,
            "basis_hex": [hex(x) for x in basis],
            "nonzero_elements": nz,
            "nonzero_hex": [hex(x) for x in nz],
            "nonzero_matrices": [mat_str(x) for x in nz],
            "rank_pattern": ranks,
            "rank_hist": hist,
            "rank_ge2_count": rank_ge2_count,
            "relevant_two_high_rank_generators": relevant,
            "old_lb": old_lb,
            "current_overlay_lb": current_lb,
            "proof_type": rec.get("proof_type"),
            "backtracking_proof_size": rec.get("backtracking_proof_size"),
            "occupation_raise_status": status_rec.get("solve", {}).get("status"),
            "occupation_feasible_at_old_lb": status_rec.get("solve", {}).get("feasible"),
            "occupation_support_size_tested": status_rec.get("support_size_tested"),
        }
        records.append(out)
    relevant = [r for r in records if r["relevant_two_high_rank_generators"]]
    unresolved = [r for r in relevant if r["current_overlay_lb"] < 19]
    summary = {
        "schema": "dim2_reduction_audit_v1",
        "total_dim2_orbits": len(records),
        "relevant_indices": [r["index"] for r in relevant],
        "irrelevant_indices": [r["index"] for r in records if not r["relevant_two_high_rank_generators"]],
        "current_lb_by_index": {str(r["index"]): r["current_overlay_lb"] for r in records},
        "unresolved_relevant_indices_current_lb_lt_19": [r["index"] for r in unresolved],
        "records": records,
        "logic": {
            "flattening_increment_sum": "sum_t(rank(a_t)-1) >= 7 for any length-20 full decomposition",
            "consequence": "after one rank>=2 pivot is chosen, either another term has the same A-direction and the one-dimensional quotient has length<=18, or an independent rank>=2 direction gives a two-dimensional quotient with length<=18",
            "needed_for_R_ge_21": "all relevant dim-2 orbits must have quotient rank lower bound at least 19; current occupation overlay leaves exactly the unresolved relevant indices listed above",
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")

    lines = []
    lines.append("# analysis dim-2 reduction audit\n")
    lines.append("The audit recomputed 3x3 matrix ranks for every nonzero element of each recorded dim-2 Wang orbit representative, using `cert_profile.json` and the local occupation overlay from `dim3_raises_to_dim2.json`.\n")
    lines.append(f"Relevant dim-2 orbits (at least two nonzero rank>=2 elements): {summary['relevant_indices']}.\n")
    lines.append(f"Irrelevant for the two-high-rank-generator reduction: {summary['irrelevant_indices']}.\n")
    lines.append(f"Relevant orbits still below lower bound 19 after the local occupation overlay: {summary['unresolved_relevant_indices_current_lb_lt_19']}.\n")
    lines.append("\n| index | basis | ranks of nonzero elements | old LB | overlay LB | relevant | occupation status |\n")
    lines.append("|---:|---|---|---:|---:|---|---|\n")
    for r in records:
        lines.append(f"| {r['index']} | {r['basis_hex']} | {r['rank_pattern']} | {r['old_lb']} | {r['current_overlay_lb']} | {r['relevant_two_high_rank_generators']} | {r['occupation_raise_status']} |\n")
    lines.append("\nMathematical use: if a length-20 full decomposition existed, the full A-slot flattening gives sum(rank(a_t)-1)>=7. Thus there are at least four rank>=2 A-factors. Pick one as p. If another term has the same A-direction p, quotienting by <p> removes at least two terms and leaves length <=18, contradicting the recorded one-dimensional Wang lower bound 19. Otherwise choose an independent rank>=2 A-factor a; quotienting by W=<p,a> removes two terms and leaves length <=18. Therefore the remaining lower-bound work is exactly to establish lower bound 19 for the relevant dim-2 quotient orbits not already raised by the occupation overlay.\n")
    NOTE.parent.mkdir(parents=True, exist_ok=True)
    NOTE.write_text("".join(lines))
    print(json.dumps({
        "out": str(OUT),
        "note": str(NOTE),
        "relevant": summary["relevant_indices"],
        "irrelevant": summary["irrelevant_indices"],
        "unresolved": summary["unresolved_relevant_indices_current_lb_lt_19"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
