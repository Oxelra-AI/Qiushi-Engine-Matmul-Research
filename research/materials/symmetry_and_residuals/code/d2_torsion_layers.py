#!/usr/bin/env python3
r"""
analysis: d=2 torsion-layer block analysis for finite-order aligned symmetries.

Purpose
-------
analysis's proposed multiplicative transfer incorrectly used general direct-sum
additivity.  This script does the finite d=2 layer directly.  For bit exponents
P,Q,R in (Z/2)^3 (one bit per row/eigenline of each 3-dimensional factor), the
multiplicative aligned blocks of T_<3,3,3> are

    (a,b,c) |-> (P_a-Q_b mod 2, Q_b-R_c mod 2).

A termwise fixed decomposition under such an involution must assign each rank-one
summand to one of these four blocks.  Therefore its length is at least the sum of
ordinary rank lower bounds for the four merged block tensors.  The hard point is
that each merged block must be bounded as a merged tensor; one may not add the
finer additive sub-block ranks without a special theorem.

This script enumerates all 2^9 bit patterns, groups their support partitions up
to independent S_3 permutations of the three index sets, and computes direct
lower bounds for each merged block using:
  * three ordinary flattenings;
  * Koszul/exterior flattenings over a large prime as rational certificates;
  * complete rectangular matrix-multiplication subtensors with explicitly named
    small-format inputs.

It reports histograms for several declared input tables so the ledger does not
mix the analysis weaker table with the CHL-improved table.
"""
from __future__ import annotations

import itertools
import json
import math
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

Triple = Tuple[int, int, int]
TRIPLES: List[Triple] = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
PERMS3 = list(itertools.permutations(range(3)))
PRIME = 1000003


def rank_mod(M: np.ndarray, p: int = PRIME) -> int:
    A = np.array(M % p, dtype=np.int64, copy=True)
    m, n = A.shape
    r = 0
    for c in range(n):
        if r >= m:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        fac = A[:, c].copy()
        fac[r] = 0
        rows = np.nonzero(fac)[0]
        if len(rows):
            A[rows] = (A[rows] - fac[rows, None] * A[r]) % p
        r += 1
    return int(r)


def compress_support(support: Sequence[Triple]):
    """Return local support triples in U=(a,b), V=(b,c), W=(a,c) factor bases."""
    Uids = sorted(set((a, b) for a, b, c in support))
    Vids = sorted(set((b, c) for a, b, c in support))
    Wids = sorted(set((a, c) for a, b, c in support))
    ui = {x: i for i, x in enumerate(Uids)}
    vi = {x: i for i, x in enumerate(Vids)}
    wi = {x: i for i, x in enumerate(Wids)}
    local = [(ui[(a, b)], vi[(b, c)], wi[(a, c)]) for a, b, c in support]
    dims = (len(Uids), len(Vids), len(Wids))
    return local, dims, (Uids, Vids, Wids)


def flattening_ranks_local(local: Sequence[Tuple[int, int, int]], dims: Tuple[int, int, int]) -> Tuple[int, int, int]:
    da, db, dc = dims
    MU = np.zeros((da, db * dc), dtype=np.int64)
    MV = np.zeros((db, da * dc), dtype=np.int64)
    MW = np.zeros((dc, da * db), dtype=np.int64)
    for i, j, k in local:
        MU[i, j * dc + k] += 1
        MV[j, i * dc + k] += 1
        MW[k, i * db + j] += 1
    return rank_mod(MU), rank_mod(MV), rank_mod(MW)


def wedge_sign_insert(I: Tuple[int, ...], x: int) -> Tuple[Tuple[int, ...], int]:
    cnt = sum(1 for i in I if i < x)
    sign = -1 if cnt % 2 else 1
    J = tuple(sorted((x,) + tuple(I)))
    return J, sign


def koszul_records_local(local: Sequence[Tuple[int, int, int]], dims: Tuple[int, int, int]):
    records = []
    for mode in range(3):
        other = [m for m in range(3) if m != mode]
        da = dims[mode]
        db = dims[other[0]]
        dc = dims[other[1]]
        if da <= 1:
            continue
        for p_wedge in range(da):
            denom = math.comb(da - 1, p_wedge)
            if denom == 0:
                continue
            wedges_p = list(itertools.combinations(range(da), p_wedge))
            wedges_q = list(itertools.combinations(range(da), p_wedge + 1))
            if not wedges_q:
                continue
            wi = {w: i for i, w in enumerate(wedges_p)}
            wq = {w: i for i, w in enumerate(wedges_q)}
            M = np.zeros((len(wedges_q) * dc, db * len(wedges_p)), dtype=np.int64)
            for t in local:
                a = t[mode]
                b = t[other[0]]
                c = t[other[1]]
                for I in wedges_p:
                    if a in I:
                        continue
                    J, sgn = wedge_sign_insert(I, a)
                    row = wq[J] * dc + c
                    col = b * len(wedges_p) + wi[I]
                    M[row, col] += sgn
            rr = rank_mod(M)
            lb = (rr + denom - 1) // denom
            records.append({
                "mode": mode,
                "p": p_wedge,
                "matrix_shape": [int(M.shape[0]), int(M.shape[1])],
                "rank_mod_prime": int(rr),
                "denominator": int(denom),
                "lower_bound_ceil": int(lb),
            })
    return records


def complete_rectangular_subtensor_lbs(support: Sequence[Triple], lb_table: Dict[Tuple[int, int, int], int]):
    supp = set(support)
    recs = []
    for A_mask in range(1, 1 << 3):
        A = [i for i in range(3) if (A_mask >> i) & 1]
        for B_mask in range(1, 1 << 3):
            B = [i for i in range(3) if (B_mask >> i) & 1]
            for C_mask in range(1, 1 << 3):
                C = [i for i in range(3) if (C_mask >> i) & 1]
                prod = {(a, b, c) for a in A for b in B for c in C}
                if prod and prod.issubset(supp):
                    dims_sorted = tuple(sorted((len(A), len(B), len(C))))
                    val = lb_table.get(dims_sorted)
                    if val is not None:
                        recs.append({
                            "A": A,
                            "B": B,
                            "C": C,
                            "dims": [len(A), len(B), len(C)],
                            "sorted_dims": list(dims_sorted),
                            "lb": int(val),
                        })
    recs.sort(key=lambda r: (r["lb"], r["dims"]), reverse=True)
    return recs


BASE_SMALL = {
    (1, 1, 1): 1,
    (1, 1, 2): 2,
    (1, 1, 3): 3,
    (1, 2, 2): 4,
    (1, 2, 3): 6,
    (1, 3, 3): 9,
}
LB_TABLES = {
    # analysis v3 inputs: only (2,3,3)->14 external; (2,2,3)->8, (2,2,2)->6 from internal exterior flattenings.
    "v3_declared_(14,8,6)": BASE_SMALL | {(2, 2, 2): 6, (2, 2, 3): 8, (2, 3, 3): 14},
    # CHL Theorems 1.4 and 1.5 give border-rank exact values 10 and 14, hence ordinary-rank lower bounds.
    "chl_declared_(14,10,6)": BASE_SMALL | {(2, 2, 2): 6, (2, 2, 3): 10, (2, 3, 3): 14},
    # Optional stronger classical input R(M_222)=7; kept separate so it is not silently mixed into old histograms.
    "chl_plus_strassen222_(14,10,7)": BASE_SMALL | {(2, 2, 2): 7, (2, 2, 3): 10, (2, 3, 3): 14},
}


def direct_sum_components(support: Sequence[Triple]) -> List[List[Triple]]:
    """Connected components of the support hypergraph in the actual tensor factors.

    Vertices are U=(a,b), V=(b,c), W=(a,c).  Different connected components have
    disjoint U-, V-, and W-coordinate sets, so the tensor is a direct sum of the
    corresponding component tensors.
    """
    support = sorted(support)
    vertices = []
    for a, b, c in support:
        vertices.extend([("U", a, b), ("V", b, c), ("W", a, c)])
    parent = {v: v for v in vertices}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[ry] = rx

    for a, b, c in support:
        u, v, w = ("U", a, b), ("V", b, c), ("W", a, c)
        union(u, v)
        union(u, w)
    comps = defaultdict(list)
    for t in support:
        a, b, c = t
        comps[find(("U", a, b))].append(t)
    return [sorted(v) for v in comps.values()]


def analyze_block_base(support: Sequence[Triple], lb_table: Dict[Tuple[int, int, int], int]) -> Dict:
    """Lower bounds that treat the block as one tensor, with no direct-sum additivity."""
    support = sorted(support)
    local, dims, ids = compress_support(support)
    fr = flattening_ranks_local(local, dims)
    flat_lb = max(fr)
    kos = koszul_records_local(local, dims)
    best_kos = max([r["lower_bound_ceil"] for r in kos], default=0)
    best_kos_rec = max(kos, key=lambda r: r["lower_bound_ceil"], default=None)
    rects = complete_rectangular_subtensor_lbs(support, lb_table)
    best_rect = rects[0]["lb"] if rects else 0
    lb = max(flat_lb, best_kos, best_rect)
    if lb == best_rect and best_rect >= max(flat_lb, best_kos):
        source = "rectangular_subtensor_small_format_table"
    elif lb == best_kos and best_kos >= flat_lb:
        source = "koszul_exterior_flattening_mod_prime_certificate"
    else:
        source = "ordinary_flattening_mod_prime_certificate"
    return {
        "support": [list(t) for t in support],
        "support_size": len(support),
        "factor_dims_UVW": list(dims),
        "factor_basis_U": [list(x) for x in ids[0]],
        "factor_basis_V": [list(x) for x in ids[1]],
        "factor_basis_W": [list(x) for x in ids[2]],
        "flattening_ranks_mod_prime": list(fr),
        "flattening_lb": int(flat_lb),
        "best_koszul_lb": int(best_kos),
        "best_koszul_record": best_kos_rec,
        "best_rectangular_subtensor_lb": int(best_rect),
        "best_rectangular_subtensor": rects[0] if rects else None,
        "direct_no_additivity_lb": int(lb),
        "direct_no_additivity_source": source,
    }


def analyze_block(support: Sequence[Triple], lb_table: Dict[Tuple[int, int, int], int]) -> Dict:
    """Analyze one multiplicative block.

    The returned certified_lb may use Ja'Ja'--Takche direct-sum additivity only
    after the support hypergraph has split into actual direct-sum components and
    all but at most one component have a tensor factor of dimension at most 2.
    This is deliberately much narrower than the false general direct-sum claim.
    """
    support = sorted(support)
    rec = analyze_block_base(support, lb_table)
    lb = rec["direct_no_additivity_lb"]
    source = rec["direct_no_additivity_source"]

    comps = direct_sum_components(support)
    comp_records = []
    if len(comps) > 1:
        for comp in comps:
            crecord = analyze_block_base(comp, lb_table)
            crecord["min_factor_dim_UVW"] = min(crecord["factor_dims_UVW"])
            comp_records.append(crecord)
        large_components = [c for c in comp_records if c["min_factor_dim_UVW"] > 2]
        jt_applicable = len(large_components) <= 1
        jt_lb = sum(c["direct_no_additivity_lb"] for c in comp_records) if jt_applicable else None
        if jt_lb is not None and jt_lb > lb:
            lb = jt_lb
            source = "component_direct_sum_additivity_JaJa_Takche_dimension_le2"
        rec["direct_sum_components"] = comp_records
        rec["direct_sum_component_count"] = len(comps)
        rec["direct_sum_additivity_JT86_applicable"] = jt_applicable
        rec["direct_sum_additivity_lb"] = jt_lb
    else:
        rec["direct_sum_components"] = []
        rec["direct_sum_component_count"] = 1
        rec["direct_sum_additivity_JT86_applicable"] = False
        rec["direct_sum_additivity_lb"] = None

    rec["certified_lb"] = int(lb)
    rec["certified_lb_source"] = source
    return rec


def partition_from_bits(P: Tuple[int, int, int], Q: Tuple[int, int, int], R: Tuple[int, int, int]):
    blocks = defaultdict(list)
    for a, b, c in TRIPLES:
        label = ((P[a] - Q[b]) % 2, (Q[b] - R[c]) % 2)
        blocks[label].append((a, b, c))
    return tuple(sorted((tuple(sorted(v)) for v in blocks.values() if v), key=lambda B: (len(B), B)))


def is_central_bits(P, Q, R) -> bool:
    return len(set(P)) == 1 and len(set(Q)) == 1 and len(set(R)) == 1


def canonical_partition(partition: Tuple[Tuple[Triple, ...], ...]):
    best = None
    for pa in PERMS3:
        for pb in PERMS3:
            for pc in PERMS3:
                mapped_blocks = []
                for B in partition:
                    mapped = tuple(sorted((pa[a], pb[b], pc[c]) for a, b, c in B))
                    mapped_blocks.append(mapped)
                cand = tuple(sorted(mapped_blocks, key=lambda B: (len(B), B)))
                if best is None or cand < best:
                    best = cand
    return best


def partition_shape(partition):
    return sorted([len(B) for B in partition], reverse=True)


def analyze_pattern(P, Q, R, partition, lb_tables):
    out = {
        "P_bits": list(P),
        "Q_bits": list(Q),
        "R_bits": list(R),
        "central_bits": is_central_bits(P, Q, R),
        "block_sizes": partition_shape(partition),
        "num_blocks": len(partition),
        "labels_note": "Blocks are sorted supports; original labels are (P_a-Q_b mod2, Q_b-R_c mod2).",
        "by_input_table": {},
    }
    for name, table in lb_tables.items():
        blocks = [analyze_block(B, table) for B in partition]
        blocks.sort(key=lambda r: (-r["certified_lb"], -r["support_size"], r["support"]))
        out["by_input_table"][name] = {
            "certified_block_lb_sum": int(sum(b["certified_lb"] for b in blocks)),
            "flattening_lb_sum": int(sum(b["flattening_lb"] for b in blocks)),
            "koszul_lb_sum": int(sum(b["best_koszul_lb"] for b in blocks)),
            "rectangular_subtensor_lb_sum": int(sum(b["best_rectangular_subtensor_lb"] for b in blocks)),
            "blocks": blocks,
        }
    return out


def main():
    t0 = time.time()
    patterns = []
    canonical = {}
    raw_hist = Counter()
    raw_noncentral_hist = Counter()
    raw_central_count = 0
    raw_noncentral_count = 0

    for P in itertools.product([0, 1], repeat=3):
        for Q in itertools.product([0, 1], repeat=3):
            for R in itertools.product([0, 1], repeat=3):
                part = partition_from_bits(P, Q, R)
                raw_hist[tuple(partition_shape(part))] += 1
                if is_central_bits(P, Q, R):
                    raw_central_count += 1
                    continue
                raw_noncentral_count += 1
                raw_noncentral_hist[tuple(partition_shape(part))] += 1
                can = canonical_partition(part)
                if can not in canonical:
                    canonical[can] = {"representative_bits": (P, Q, R), "raw_count": 0, "partition": part}
                canonical[can]["raw_count"] += 1

    reps = []
    hist_by_table = {name: Counter() for name in LB_TABLES}
    low_by_table = {name: [] for name in LB_TABLES}
    for can, rec in canonical.items():
        P, Q, R = rec["representative_bits"]
        pat = analyze_pattern(P, Q, R, rec["partition"], LB_TABLES)
        pat["raw_count_in_512_noncentral_patterns"] = rec["raw_count"]
        pat["canonical_support_partition"] = [[list(t) for t in B] for B in can]
        reps.append(pat)
        for name in LB_TABLES:
            s = pat["by_input_table"][name]["certified_block_lb_sum"]
            hist_by_table[name][s] += rec["raw_count"]
            if s <= 22:
                low_by_table[name].append(pat)

    reps.sort(key=lambda r: (
        min(v["certified_block_lb_sum"] for v in r["by_input_table"].values()),
        r["block_sizes"],
        r["P_bits"], r["Q_bits"], r["R_bits"],
    ))

    min_by_table = {}
    for name in LB_TABLES:
        vals = [r["by_input_table"][name]["certified_block_lb_sum"] for r in reps]
        min_by_table[name] = min(vals) if vals else None

    result = {
        "purpose": "Direct d=2 torsion-layer block-rank analysis for finite-order termwise aligned De Groote symmetries of T333.",
        "field_scope": "Characteristic zero lower-bound certificates: flattening/Koszul ranks are computed modulo a large prime as rational nonzero-minor certificates; small rectangular entries are declared theorem inputs.",
        "important_correction": "This computation does not assume general rank additivity for index-disjoint supports.  It bounds each merged mod-2 multiplicative block directly.",
        "prime_for_linear_algebra_certificates": PRIME,
        "raw_bit_patterns_total": 512,
        "raw_central_bit_patterns": raw_central_count,
        "raw_noncentral_bit_patterns": raw_noncentral_count,
        "raw_partition_shape_histogram_all": {str(k): int(v) for k, v in sorted(raw_hist.items())},
        "raw_partition_shape_histogram_noncentral": {str(k): int(v) for k, v in sorted(raw_noncentral_hist.items())},
        "canonical_noncentral_partition_count_up_to_S3_cubed": len(reps),
        "declared_input_tables": {name: {str(k): int(v) for k, v in sorted(tab.items())} for name, tab in LB_TABLES.items()},
        "certified_sum_histograms_by_input_table_raw_counts": {
            name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in hist_by_table.items()
        },
        "minimum_certified_sum_by_input_table": min_by_table,
        "patterns_with_sum_le22_by_input_table": {
            name: len(vals) for name, vals in low_by_table.items()
        },
        "low_patterns_full_records": {
            name: vals[:20] for name, vals in low_by_table.items()
        },
        "canonical_representatives_sorted": reps,
        "interpretation": (
            "For a termwise aligned involution, rank r is at least the sum over the nonempty multiplicative blocks of R(T_block), "
            "because summands are eigenvectors and hence are assigned to one block.  The listed sums use direct lower bounds on the merged blocks, "
            "not additivity across finer additive blocks.  If all sums are >=23 under a declared input table, that table excludes noncentral d=2 termwise aligned rank-22 decompositions."
        ),
        "elapsed_sec": time.time() - t0,
    }
    workspace = Path(__file__).resolve().parents[1]
    out = workspace / "data/d2_torsion_layers/d2_torsion_layer_analysis.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "raw_noncentral": raw_noncentral_count,
        "canonical_noncentral": len(reps),
        "shape_hist_noncentral": {str(k): int(v) for k, v in sorted(raw_noncentral_hist.items())},
        "min_by_table": min_by_table,
        "hist_by_table": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in hist_by_table.items()},
        "patterns_le22": {name: len(vals) for name, vals in low_by_table.items()},
        "out": str(out),
        "elapsed_sec": time.time()-t0,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
