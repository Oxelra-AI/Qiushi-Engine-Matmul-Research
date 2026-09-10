#!/usr/bin/env python3
"""LUT-free factor-rank-sum lower bounds from slot-splitting flattenings.

Central lemma (elementary, field-independent).  Let T in F^{9x9x9} be given in
the convention  T[3i+j, 3j+k, 3i+k] = 1  for T_{<3,3,3>}.  Define the A-split
flattening

    Phi_A(T)[(i,b),(j,c)] = T[3i+j, b, c],        Phi_A(T) in F^{27 x 27},

with row index (i,b) in 3 x 9 and column index (j,c) in 3 x 9.  Phi_A is linear
and for a single term a (x) b (x) c (a a 3x3 matrix through the same bit order)

    Phi_A(a (x) b (x) c) = a (x) (b c^T)     (Kronecker product),

whose rank is rank(a) * 1 = rank(a).  Rank subadditivity therefore gives, for
every exact decomposition T = sum_t a_t (x) b_t (x) c_t,

    sum_t rank(a_t) >= rank Phi_A(T).

For T_{<3,3,3>} the matrix Phi_A(T) is a permutation matrix of size 27, so

    sum_t rank(a_t) >= 27,

and the same holds for the B and C slots by the analogous flattenings.  For an
8x9x9 quotient tensor Q (A-slot no longer a matrix space) the B and C splits
still apply and give bounds  sum_t rank(b_t) >= rank Phi_B(Q)  with
Phi_B(Q) in F^{24 x 27}.

The script verifies all flattening ranks, the analogous n^3 statement for
<n,n,n>, and checks the inequalities against every exactly verified
decomposition available in this investigation.

Outputs: workspace/data/flattening_bounds/flattening_rank_sum_bounds.json
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from quotient_line_caps_and_controls import (  # type: ignore
    bits_to_mat,
    build_t333,
    gf2_rank_mat,
    quotient_project,
    quotient_tensor,
    recon_full,
    recon_quotient,
    vec,
)

OUTDIR = SESSION / "workspace/data/flattening_bounds"


# ---------------------------------------------------------------- linear algebra
def gf2_rank(M: np.ndarray) -> int:
    A = (np.asarray(M, dtype=np.uint8) & 1).copy()
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


# ------------------------------------------------------------------ flattenings
def phi_slot(T: np.ndarray, slot: int, n: int = 3) -> np.ndarray:
    """Split `slot` of a 3-way tensor whose slot dimension is n*n.

    Row index = (first factor of the split slot, one full other slot).
    Column index = (second factor of the split slot, remaining full slot).
    The other two slots are taken in cyclic order after `slot`.
    """
    T = np.asarray(T, dtype=np.uint8) & 1
    d = [T.shape[0], T.shape[1], T.shape[2]]
    assert d[slot] == n * n, (slot, d)
    s1, s2 = (slot + 1) % 3, (slot + 2) % 3
    rows = n * d[s1]
    cols = n * d[s2]
    M = np.zeros((rows, cols), dtype=np.uint8)
    it = np.nditer(T, flags=["multi_index"])
    for val in it:
        if not int(val):
            continue
        idx = it.multi_index
        x = idx[slot]
        i, j = divmod(x, n)
        # For the C/output slot in the convention T[3*i+j,3*j+k,3*i+k],
        # the cyclic trace symmetry uses the transposed split (k,i).  Since
        # rank(C)=rank(C^T), this gives the valid C-rank-sum flattening;
        # the unreversed split only has rank 3 and answers a weaker grouping.
        if slot == 2:
            i, j = j, i
        M[i * d[s1] + idx[s1], j * d[s2] + idx[s2]] ^= 1
    return M


def matmul_tensor(n: int) -> np.ndarray:
    T = np.zeros((n * n, n * n, n * n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                T[n * i + j, n * j + k, n * i + k] ^= 1
    return T


# -------------------------------------------------------------- scheme checking
def factor_rank_hist(masks: Sequence[int]) -> Dict[int, int]:
    h = {1: 0, 2: 0, 3: 0, 0: 0}
    for m in masks:
        h[gf2_rank_mat(bits_to_mat(int(m)))] += 1
    return {k: v for k, v in sorted(h.items())}


def rank_sum(masks: Sequence[int]) -> int:
    return int(sum(gf2_rank_mat(bits_to_mat(int(m))) for m in masks))


def check_full_scheme(terms: List[Tuple[int, int, int]], label: str) -> Dict:
    T = build_t333()
    rec = recon_full(terms)
    diff = int(np.count_nonzero((T ^ rec) & 1))
    a = [t[0] for t in terms]
    b = [t[1] for t in terms]
    c = [t[2] for t in terms]
    return {
        "label": label,
        "terms": len(terms),
        "exact_over_F2": diff == 0,
        "tensor_diff": diff,
        "rank_sum_A": rank_sum(a),
        "rank_sum_B": rank_sum(b),
        "rank_sum_C": rank_sum(c),
        "rank_hist_A": factor_rank_hist(a),
        "rank_hist_B": factor_rank_hist(b),
        "rank_hist_C": factor_rank_hist(c),
        "product_rank_sum": int(
            sum(
                gf2_rank_mat(bits_to_mat(t[0]))
                * gf2_rank_mat(bits_to_mat(t[1]))
                * gf2_rank_mat(bits_to_mat(t[2]))
                for t in terms
            )
        ),
    }


def check_quotient_scheme(qterms: List[Tuple[int, int, int]], pivot: int, label: str) -> Dict:
    """qterms are (quotient_a, b, c) with quotient_a already projected."""
    Q = quotient_tensor(pivot)
    rec = np.zeros_like(Q)
    for qa, b, c in qterms:
        if qa == 0:
            continue
        rec ^= (
            vec(qa, 8).reshape(8, 1, 1) * vec(b, 9).reshape(1, 9, 1) * vec(c, 9).reshape(1, 1, 9)
        ).astype(np.uint8)
    diff = int(np.count_nonzero((Q ^ rec) & 1))
    b = [t[1] for t in qterms]
    c = [t[2] for t in qterms]
    return {
        "label": label,
        "pivot": pivot,
        "terms": len(qterms),
        "exact_over_F2": diff == 0,
        "tensor_diff": diff,
        "rank_sum_B": rank_sum(b),
        "rank_sum_C": rank_sum(c),
        "rank_hist_B": factor_rank_hist(b),
        "rank_hist_C": factor_rank_hist(c),
        "product_rank_sum_BC": int(
            sum(gf2_rank_mat(bits_to_mat(t[1])) * gf2_rank_mat(bits_to_mat(t[2])) for t in qterms)
        ),
    }


# ---------------------------------------------------------- multi-slot splitting
def phi_two_slot_BC(Q: np.ndarray) -> np.ndarray:
    """Split B and C of an (dA, 9, 9) tensor.

    5-way tensor with dims (dA, 3, 3, 3, 3).  Flatten rows = (A, B-row),
    cols = (B-col, C-row, C-col).  For a term qa (x) b (x) c the rank of this
    matrix is at most rank(b) * rank(c).
    """
    Q = np.asarray(Q, dtype=np.uint8) & 1
    dA = Q.shape[0]
    M = np.zeros((dA * 3, 3 * 9), dtype=np.uint8)
    for al in range(dA):
        for bi in range(9):
            j, k = divmod(bi, 3)
            for ci in range(9):
                if Q[al, bi, ci]:
                    M[al * 3 + j, k * 9 + ci] ^= 1
    return M


def phi_three_slot_full(T: np.ndarray) -> np.ndarray:
    """Split all three slots of a 9x9x9 tensor.

    6-way tensor (i,j | j',k | i'',k'').  Flatten rows = (A-row, B-row, C-col),
    cols = (A-col, B-col, C-row).  For a term the rank is at most
    rank(a)*rank(b)*rank(c).
    """
    T = np.asarray(T, dtype=np.uint8) & 1
    M = np.zeros((27, 27), dtype=np.uint8)
    for ai in range(9):
        i, j = divmod(ai, 3)
        for bi in range(9):
            jp, k = divmod(bi, 3)
            for ci in range(9):
                ip, kp = divmod(ci, 3)
                if T[ai, bi, ci]:
                    M[(i * 3 + jp) * 3 + kp, (j * 3 + k) * 3 + ip] ^= 1
    return M


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    out: Dict = {}

    # 1. Full tensor slot flattening ranks.
    T = build_t333()
    slot_ranks = {}
    for slot, name in ((0, "A"), (1, "B"), (2, "C")):
        M = phi_slot(T, slot)
        r = gf2_rank(M)
        is_perm = bool(
            M.shape[0] == M.shape[1]
            and np.all(M.sum(axis=1) == 1)
            and np.all(M.sum(axis=0) == 1)
        )
        slot_ranks[name] = {"shape": list(M.shape), "rank_F2": r, "is_permutation": is_perm}
    out["t333_slot_flattening"] = slot_ranks

    # 2. Generalization to <n,n,n>: rank should be n^3.
    gen = {}
    for n in (2, 3, 4):
        Tn = matmul_tensor(n)
        M = phi_slot(Tn, 0, n=n)
        gen[str(n)] = {
            "shape": list(M.shape),
            "rank_F2": gf2_rank(M),
            "n_cubed": n ** 3,
        }
    out["matmul_A_split_rank_by_n"] = gen

    # 3. Three-slot split of the full tensor: sum_t ra*rb*rc >= rank.
    M3 = phi_three_slot_full(T)
    out["t333_three_slot_split"] = {"shape": list(M3.shape), "rank_F2": gf2_rank(M3)}

    # 4. Quotient tensors: B/C split bounds and BC two-slot split.
    quot = {}
    for name, pivot in (("rank1", 1), ("rank2", 17), ("rank3", 273)):
        Q = quotient_tensor(pivot)
        entry = {
            "pivot": pivot,
            "pivot_matrix_rank": gf2_rank_mat(bits_to_mat(pivot)),
            "nnz": int(np.count_nonzero(Q)),
            "slice_ranks": [gf2_rank(Q[s]) for s in range(8)],
        }
        for slot, sname in ((1, "B"), (2, "C")):
            M = phi_slot(Q, slot)
            entry[f"phi_{sname}_shape"] = list(M.shape)
            entry[f"phi_{sname}_rank"] = gf2_rank(M)
        Mbc = phi_two_slot_BC(Q)
        entry["phi_BC_shape"] = list(Mbc.shape)
        entry["phi_BC_rank"] = gf2_rank(Mbc)
        quot[name] = entry
    out["quotient_flattening"] = quot

    # 5. Positive controls: verified full rank-23 scheme and quotient controls.
    controls: List[Dict] = []
    from extract_known_supports import parse_rank23_txt  # type: ignore

    r23_path = Path(
        "data/flip_cpd_inspect/src/"
        "khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt"
    )
    if r23_path.exists():
        terms = [tuple(map(int, t)) for t in parse_rank23_txt(r23_path)]
        controls.append(check_full_scheme(terms, "flipcpd_gg333_rank23_text"))

    v_path = Path(
        "data/fixed_A_rankone/validation_full_cn122_rank23.json"
    )
    if v_path.exists():
        js = json.loads(v_path.read_text())
        tt = None
        for key in ("terms", "scheme", "decomposition"):
            if key in js:
                tt = js[key]
                break
        if tt is not None:
            if isinstance(tt[0], dict):
                terms2 = [(int(t['a_mask']), int(t['b_mask']), int(t['c_mask'])) for t in tt]
            else:
                terms2 = [tuple(map(int, t)) for t in tt]
            controls.append(check_full_scheme(terms2, "research_record_validation_cn122_rank23"))
    out["full_scheme_controls"] = controls

    qcontrols: List[Dict] = []
    ctrl_path = (
        SESSION
        / "workspace/data/wang_native/three_orbit_controls/rank2_quotient_rank22_control.json"
    )
    if ctrl_path.exists():
        js = json.loads(ctrl_path.read_text())
        best = js.get("controls_from_rank23", js).get("rank2", js).get("best_control", None)
        if best is None and "best_control" in js:
            best = js["best_control"]
        if best and "quotient_terms_full" in best:
            qt = [tuple(map(int, t)) for t in best["quotient_terms_full"]]
            qcontrols.append(check_quotient_scheme(qt, 17, "rank2_quotient_rank22_control"))
    proj_path = (
        SESSION
        / "workspace/data/wang_native/three_orbit_controls/"
        "projected_rank23_quotient_controls_summary.json"
    )
    if proj_path.exists():
        js = json.loads(proj_path.read_text())
        for name, pivot in (("rank1", 1), ("rank2", 17), ("rank3", 273)):
            rec = js.get("summary", js).get(name)
            if isinstance(rec, dict) and "quotient_terms_full" in rec:
                qt = [tuple(map(int, t)) for t in rec["quotient_terms_full"]]
                qcontrols.append(
                    check_quotient_scheme(qt, pivot, f"projected_rank23_{name}_quotient")
                )
    out["quotient_scheme_controls"] = qcontrols

    # 6. Immediate combinatorial consequences at the target lengths.
    def excess_needed(bound: int, n: int) -> Dict:
        return {
            "bound": bound,
            "n": n,
            "min_total_excess": max(0, bound - n),
            "min_terms_rank_ge2": max(0, -(-(bound - n) // 2)) if bound > n else 0,
        }

    out["consequences"] = {
        "full_n20_A": excess_needed(slot_ranks["A"]["rank_F2"], 20),
        "full_n21_A": excess_needed(slot_ranks["A"]["rank_F2"], 21),
        "full_n22_A": excess_needed(slot_ranks["A"]["rank_F2"], 22),
        "full_n23_A": excess_needed(slot_ranks["A"]["rank_F2"], 23),
        "quotient_n19_B": {
            k: excess_needed(quot[k]["phi_B_rank"], 19) for k in ("rank1", "rank2", "rank3")
        },
        "quotient_n19_C": {
            k: excess_needed(quot[k]["phi_C_rank"], 19) for k in ("rank1", "rank2", "rank3")
        },
    }

    path = OUTDIR / "flattening_rank_sum_bounds.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps(out, indent=2, sort_keys=True)[:6000])
    print("saved", path)


if __name__ == "__main__":
    main()
