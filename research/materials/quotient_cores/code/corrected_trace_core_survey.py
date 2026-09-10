#!/usr/bin/env python3
r"""
analysis: corrected trace-saturation survey for the three F2 codimension-one cores.

This script repairs the analysis/related analysis-analysis trace replay convention and measures
whether the corrected saturated-contraction trace equations have useful leverage
beyond the E11 near-miss where the old single-q certificate was reported.

Mathematical convention.  If a saturated invertible contraction

    M(q) = sum_{s in I_q} b_s c_s^T

has |I_q|=9, then for every participating rank-one matrix X_s=b_s c_s^T,

    tr(M(q)^{-1} X_s) = c_s^T M(q)^{-1} b_s = 1.

For variables X_s[b,c] this is the linear coefficient M^{-1}[c,b], not
M^{-1}[b,c].  The latter was the analysis/analysis wrong entrywise pairing.

The script:
  * reconstructs the three GL3xGL3 quotient cores over F2 from T_333;
  * checks them against existing .npy core files;
  * validates corrected trace equations on sampled verified rank-21 controls;
  * replays the E11 near-miss with both wrong and corrected coefficients;
  * runs a small deletion-near-miss pilot in the E11, E12+E21, and H3 cores.

Outputs are evidence for route selection, not lower bounds.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

import numpy as np

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace_core_survey"

CORES = {
    "E11": {
        "mask": 1,
        "label": "rank-1 quotient E11",
        "core_file": Path("data/e11_flip_workspace/data/tensors/e11core.npy"),
        "pool_file": Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy"),
    },
    "E12_E21": {
        "mask": 10,
        "label": "rank-2 quotient E12+E21",
        "core_file": Path("data/e12e21_flip_workspace/data/tensors/e12e21core.npy"),
        "pool_file": Path("data/e12e21_flip_workspace/data/schemes_modp/e12e21core/mod2-rank21a.npy"),
    },
    "H3": {
        "mask": 84,
        "label": "rank-3 quotient E13+E22+E31",
        "core_file": Path("data/e13e22e31_flip_workspace/data/tensors/e13e22e31core.npy"),
        "pool_file": Path("data/e13e22e31_flip_workspace/data/schemes_modp/e13e22e31core/mod2-rank21a.npy"),
    },
}

E11_NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def build_matmul_tensor_f2(n0: int = 3, n1: int = 3, n2: int = 3) -> np.ndarray:
    na, nb, nc = n0 * n1, n1 * n2, n0 * n2
    T = np.zeros((na, nb, nc), dtype=np.uint8)
    for i in range(n0):
        for j in range(n1):
            for k in range(n2):
                a = n1 * i + j
                b = n2 * j + k
                c = n2 * i + k
                T[a, b, c] = 1
    return T


def quotient_core_from_mask(mask: int) -> tuple[np.ndarray, dict]:
    """Apply the F2 linear constraint mask to the A-mode and delete the pivot slice."""
    T = build_matmul_tensor_f2()
    pivot = int(mask).bit_length() - 1  # Wang/RREF convention: highest set bit is pivot
    free_bits = int(mask) ^ (1 << pivot)
    folded = T.copy()
    for i in range(T.shape[0]):
        if (free_bits >> i) & 1:
            folded[i] ^= T[pivot]
    folded[pivot] = 0
    keep = [i for i in range(T.shape[0]) if i != pivot]
    return folded[keep].astype(np.uint8), {"mask": int(mask), "pivot": int(pivot), "free_bits": [i for i in range(9) if (free_bits >> i) & 1], "kept_full_A_indices": keep}


def mask_to_bits(mask: int, n: int) -> list[int]:
    return [i for i in range(n) if (int(mask) >> i) & 1]


def mat_rank_f2(M: np.ndarray) -> int:
    M = np.asarray(M, dtype=np.uint8) & 1
    m, n = M.shape
    rows = []
    for i in range(m):
        x = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                x |= 1 << j
        rows.append(x)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if (rows[i] >> c) & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(m):
            if i != r and ((rows[i] >> c) & 1):
                rows[i] ^= rows[r]
        r += 1
        if r == m:
            break
    return r


def gf2_mat_inv(M: np.ndarray) -> Optional[np.ndarray]:
    M = np.asarray(M, dtype=np.uint8) & 1
    n = M.shape[0]
    assert M.shape == (n, n)
    aug = []
    for i in range(n):
        row = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                row |= 1 << j
        row |= 1 << (n + i)
        aug.append(row)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if (aug[r] >> col) & 1:
                piv = r
                break
        if piv is None:
            return None
        aug[col], aug[piv] = aug[piv], aug[col]
        for r in range(n):
            if r != col and ((aug[r] >> col) & 1):
                aug[r] ^= aug[col]
    inv = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            if (aug[i] >> (n + j)) & 1:
                inv[i, j] = 1
    return inv


def contraction_matrix(T_core: np.ndarray, q: int) -> np.ndarray:
    M = np.zeros((T_core.shape[1], T_core.shape[2]), dtype=np.uint8)
    for a in range(T_core.shape[0]):
        if (int(q) >> a) & 1:
            M ^= T_core[a]
    return M


def contractions(T_core: np.ndarray) -> dict[int, dict]:
    out = {}
    for q in range(1, 1 << T_core.shape[0]):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        out[q] = {"rank": rk, "M": M, "M_inv": gf2_mat_inv(M) if rk == 9 else None}
    return out


def reconstruct_from_terms(terms: Sequence[int], shape: tuple[int, int, int]) -> np.ndarray:
    T = np.zeros(shape, dtype=np.uint8)
    assert len(terms) % 3 == 0
    for i in range(0, len(terms), 3):
        a, b, c = int(terms[i]), int(terms[i + 1]), int(terms[i + 2])
        for ia in mask_to_bits(a, shape[0]):
            for ib in mask_to_bits(b, shape[1]):
                for ic in mask_to_bits(c, shape[2]):
                    T[ia, ib, ic] ^= 1
    return T


def term_lists(row: np.ndarray) -> tuple[list[int], list[int], list[int]]:
    vals = [int(x) for x in row.tolist()]
    return vals[0::3], vals[1::3], vals[2::3]


def trace_value(Minv: np.ndarray, bmask: int, cmask: int) -> int:
    """c^T Minv b over F2."""
    v = 0
    for c in range(9):
        if not ((int(cmask) >> c) & 1):
            continue
        for b in range(9):
            if ((int(bmask) >> b) & 1) and (int(Minv[c, b]) & 1):
                v ^= 1
    return v & 1


def gf2_linear_consistency(rows_aug: Sequence[int], nvars: int) -> tuple[bool, int, Optional[int]]:
    coeff_mask = (1 << nvars) - 1
    basis: dict[int, int] = {}
    combs: dict[int, int] = {}
    for i, row0 in enumerate(rows_aug):
        row = int(row0)
        comb = 1 << i
        while True:
            coeff = row & coeff_mask
            if coeff == 0:
                if (row >> nvars) & 1:
                    return False, len(basis), comb
                break
            piv = coeff.bit_length() - 1
            if piv in basis:
                row ^= basis[piv]
                comb ^= combs[piv]
            else:
                basis[piv] = row
                combs[piv] = comb
                break
    return True, len(basis), None


def build_labeled_rows(
    T_core: np.ndarray,
    A_terms: Sequence[int],
    cdata: dict[int, dict],
    q_subset: Optional[Iterable[int]] = None,
    coefficient: str = "correct",
) -> tuple[list[int], list[tuple], int, list[int]]:
    """Tensor rows plus saturated trace rows for a fixed A-term list."""
    na, nb, nc = T_core.shape
    nterms = len(A_terms)
    nvars = nterms * nb * nc
    q_allowed = None if q_subset is None else {int(q) for q in q_subset}

    def vidx(s: int, b: int, c: int) -> int:
        return s * (nb * nc) + b * nc + c

    rows: list[int] = []
    labels: list[tuple] = []
    for a in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, acol in enumerate(A_terms):
                    if (int(acol) >> a) & 1:
                        row ^= 1 << vidx(s, b, c)
                if int(T_core[a, b, c]) & 1:
                    row |= 1 << nvars
                rows.append(row)
                labels.append(("tensor", a, b, c))

    sat_qs: list[int] = []
    for q, info in sorted(cdata.items()):
        if q_allowed is not None and q not in q_allowed:
            continue
        if info["rank"] != 9:
            continue
        I = [s for s, acol in enumerate(A_terms) if ((int(acol) & q).bit_count() & 1)]
        if len(I) != 9:
            continue
        sat_qs.append(q)
        Minv = info["M_inv"]
        assert Minv is not None
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    coeff = int(Minv[c, b]) if coefficient == "correct" else int(Minv[b, c])
                    if coeff & 1:
                        row ^= 1 << vidx(s, b, c)
            row |= 1 << nvars
            rows.append(row)
            labels.append(("trace", q, s, coefficient))
    return rows, labels, nvars, sat_qs


def consistency_summary(rows: Sequence[int], labels: Sequence[tuple], nvars: int) -> dict:
    con, rank, cert = gf2_linear_consistency(rows, nvars)
    out = {"consistent": bool(con), "rank": int(rank), "rows": len(rows), "nvars": int(nvars)}
    if cert is not None:
        used = [i for i in range(len(rows)) if (cert >> i) & 1]
        q_counts = Counter(labels[i][1] for i in used if labels[i][0] == "trace")
        out["certificate"] = {
            "row_count": len(used),
            "tensor_rows": sum(1 for i in used if labels[i][0] == "tensor"),
            "trace_rows": sum(1 for i in used if labels[i][0] == "trace"),
            "trace_qs": sorted(int(q) for q in q_counts),
            "trace_rows_by_q": {str(k): int(v) for k, v in sorted(q_counts.items())},
        }
        x = 0
        for i in used:
            x ^= int(rows[i])
        out["certificate"]["coefficients_zero"] = bool((x & ((1 << nvars) - 1)) == 0)
        out["certificate"]["rhs_one"] = bool((x >> nvars) & 1)
    return out


def validate_rank21_controls(name: str, T_core: np.ndarray, cdata: dict[int, dict], pool: np.ndarray, pool_limit: int) -> dict:
    records = []
    totals = Counter()
    rank_hist = Counter()
    for idx, row in enumerate(pool[:pool_limit]):
        A, B, C = term_lists(row)
        recT = reconstruct_from_terms(row, T_core.shape)
        verified = bool(np.array_equal(recT, T_core))
        totals["verified"] += int(verified)
        totals["schemes"] += 1
        rank_hist[len(set(A))] += 1
        sat_qs = []
        trace_fail = 0
        trace_tests = 0
        for q, info in sorted(cdata.items()):
            if info["rank"] != 9:
                continue
            I = [s for s, a in enumerate(A) if ((a & q).bit_count() & 1)]
            if len(I) != 9:
                continue
            sat_qs.append(q)
            Minv = info["M_inv"]
            for s in I:
                trace_tests += 1
                if trace_value(Minv, B[s], C[s]) != 1:
                    trace_fail += 1
        totals["sat_q_total"] += len(sat_qs)
        totals["trace_tests"] += trace_tests
        totals["trace_fail"] += trace_fail
        if len(records) < 8:
            rows, labels, nvars, sat2 = build_labeled_rows(T_core, A, cdata, coefficient="correct")
            sys = consistency_summary(rows, labels, nvars)
            records.append({
                "scheme_index": idx,
                "verified": verified,
                "term_count": len(A),
                "unique_A": len(set(A)),
                "A_multiplicity_hist": dict(sorted(Counter(Counter(A).values()).items())),
                "saturated_rank9_qs": sat_qs,
                "correct_trace_direct_failures": trace_fail,
                "correct_trace_system_consistent": sys["consistent"],
                "correct_trace_system_rank": sys["rank"],
            })
    return {
        "pool_rows_sampled": int(min(pool_limit, len(pool))),
        "pool_rows_available": int(len(pool)),
        "verified_sampled_schemes": int(totals["verified"]),
        "unique_A_histogram": {str(k): int(v) for k, v in sorted(rank_hist.items())},
        "saturated_rank9_q_total_over_sample": int(totals["sat_q_total"]),
        "correct_trace_direct_tests": int(totals["trace_tests"]),
        "correct_trace_direct_failures": int(totals["trace_fail"]),
        "records_head": records,
    }


def deletion_pilot(T_core: np.ndarray, cdata: dict[int, dict], pool: np.ndarray, pool_limit: int, max_supports: int) -> dict:
    seen: set[tuple[int, ...]] = set()
    totals = Counter()
    sat_hist = Counter()
    examples = []
    trace_inconsistent_examples = []
    t0 = time.time()
    for scheme_index, row in enumerate(pool[:pool_limit]):
        A, _B, _C = term_lists(row)
        for i, j in itertools.combinations(range(len(A)), 2):
            rem = [A[t] for t in range(len(A)) if t not in (i, j)]
            key = tuple(sorted(rem))
            if key in seen:
                continue
            seen.add(key)
            totals["supports_tested"] += 1
            distinct = len(set(rem)) == len(rem)
            totals["distinct_supports_tested"] += int(distinct)
            rows0, labels0, nvars, _ = build_labeled_rows(T_core, rem, cdata, q_subset=[], coefficient="correct")
            s0 = consistency_summary(rows0, labels0, nvars)
            if s0["consistent"]:
                totals["tensor_consistent"] += 1
                totals["tensor_consistent_distinct"] += int(distinct)
                rows, labels, nvars, sat_qs = build_labeled_rows(T_core, rem, cdata, coefficient="correct")
                sat_hist[len(sat_qs)] += 1
                s1 = consistency_summary(rows, labels, nvars)
                if not s1["consistent"]:
                    totals["correct_trace_inconsistent"] += 1
                    totals["correct_trace_inconsistent_distinct"] += int(distinct)
                    if len(trace_inconsistent_examples) < 10:
                        trace_inconsistent_examples.append({
                            "scheme_index": scheme_index,
                            "deleted_positions": [i, j],
                            "A_multiset": key,
                            "distinct": distinct,
                            "saturated_rank9_qs": sat_qs,
                            "tensor_only": s0,
                            "correct_trace": s1,
                        })
                elif len(examples) < 10:
                    examples.append({
                        "scheme_index": scheme_index,
                        "deleted_positions": [i, j],
                        "A_multiset": key,
                        "distinct": distinct,
                        "saturated_rank9_qs": sat_qs,
                        "tensor_only_rank": s0["rank"],
                        "correct_trace_rank": s1["rank"],
                    })
            else:
                totals["tensor_inconsistent"] += 1
            if totals["supports_tested"] >= max_supports:
                return {
                    "pool_rows_scanned_until_stop": scheme_index + 1,
                    "max_supports": max_supports,
                    "totals": {k: int(v) for k, v in sorted(totals.items())},
                    "saturated_q_count_hist_for_tensor_consistent": {str(k): int(v) for k, v in sorted(sat_hist.items())},
                    "consistent_after_correct_trace_examples_head": examples,
                    "trace_inconsistent_examples_head": trace_inconsistent_examples,
                    "elapsed_sec": round(time.time() - t0, 3),
                }
    return {
        "pool_rows_scanned_until_stop": int(min(pool_limit, len(pool))),
        "max_supports": max_supports,
        "totals": {k: int(v) for k, v in sorted(totals.items())},
        "saturated_q_count_hist_for_tensor_consistent": {str(k): int(v) for k, v in sorted(sat_hist.items())},
        "consistent_after_correct_trace_examples_head": examples,
        "trace_inconsistent_examples_head": trace_inconsistent_examples,
        "elapsed_sec": round(time.time() - t0, 3),
    }


def replay_e11_near_miss(T_core: np.ndarray, cdata: dict[int, dict]) -> dict:
    rows0, labels0, nvars, _ = build_labeled_rows(T_core, E11_NEAR_MISS, cdata, q_subset=[], coefficient="correct")
    rows_q49_corr, labels_q49_corr, _, sat_q49_corr = build_labeled_rows(T_core, E11_NEAR_MISS, cdata, q_subset=[49], coefficient="correct")
    rows_q49_wrong, labels_q49_wrong, _, sat_q49_wrong = build_labeled_rows(T_core, E11_NEAR_MISS, cdata, q_subset=[49], coefficient="wrong")
    rows_all_corr, labels_all_corr, _, sat_all_corr = build_labeled_rows(T_core, E11_NEAR_MISS, cdata, coefficient="correct")
    rows_all_wrong, labels_all_wrong, _, sat_all_wrong = build_labeled_rows(T_core, E11_NEAR_MISS, cdata, coefficient="wrong")
    return {
        "support": E11_NEAR_MISS,
        "tensor_only": consistency_summary(rows0, labels0, nvars),
        "q49_rank": cdata[49]["rank"],
        "q49_I_indices": [s for s, a in enumerate(E11_NEAR_MISS) if ((a & 49).bit_count() & 1)],
        "correct_q49_saturated_qs": sat_q49_corr,
        "correct_q49": consistency_summary(rows_q49_corr, labels_q49_corr, nvars),
        "wrong_q49_saturated_qs": sat_q49_wrong,
        "wrong_q49": consistency_summary(rows_q49_wrong, labels_q49_wrong, nvars),
        "correct_all_saturated_qs": sat_all_corr,
        "correct_all_saturated": consistency_summary(rows_all_corr, labels_all_corr, nvars),
        "wrong_all_saturated_qs": sat_all_wrong,
        "wrong_all_saturated": consistency_summary(rows_all_wrong, labels_all_wrong, nvars),
        "meaning": "The old single-q49 contradiction uses the wrong coefficient. With the corrected coefficient q49 alone is consistent; the sampled near-miss is still rejected by the joint corrected saturated trace equations.",
    }


def load_core_file_auto(path: Path, shape: tuple[int, int, int]) -> tuple[np.ndarray, dict]:
    """Load either a dense tensor .npy or a COO array with rows [a,b,c,value]."""
    arr = np.load(path, allow_pickle=True)
    meta = {"raw_shape": list(arr.shape), "raw_dtype": str(arr.dtype)}
    if arr.shape == shape:
        meta["format"] = "dense"
        return (arr.astype(np.uint8) & 1), meta
    if arr.ndim == 2 and arr.shape[1] == 4:
        T = np.zeros(shape, dtype=np.uint8)
        for a, b, c, v in arr.tolist():
            if int(v) & 1:
                T[int(a), int(b), int(c)] ^= 1
        meta["format"] = "coo_abcv"
        meta["coo_rows"] = int(arr.shape[0])
        return T, meta
    raise ValueError(f"unrecognized core file format for {path}: shape {arr.shape}")


def core_survey(name: str, cfg: dict, pool_limit: int, max_deletions: int) -> dict:
    T_core, meta = quotient_core_from_mask(cfg["mask"])
    existing, existing_meta = load_core_file_auto(cfg["core_file"], T_core.shape)
    pool = np.load(cfg["pool_file"], allow_pickle=True)
    cdata = contractions(T_core)
    rank_hist = Counter(info["rank"] for info in cdata.values())
    rec = {
        "name": name,
        "label": cfg["label"],
        "mask": int(cfg["mask"]),
        "quotient_meta": meta,
        "core_shape": list(T_core.shape),
        "existing_core_file": str(cfg["core_file"]),
        "existing_core_file_meta": existing_meta,
        "existing_core_matches_reconstruction": bool(np.array_equal(T_core, existing)),
        "contraction_rank_histogram": {str(k): int(v) for k, v in sorted(rank_hist.items())},
        "rank9_contractions": [int(q) for q, info in sorted(cdata.items()) if info["rank"] == 9],
        "rank21_pool_file": str(cfg["pool_file"]),
        "rank21_controls": validate_rank21_controls(name, T_core, cdata, pool, pool_limit),
        "deletion_nearmiss_pilot": deletion_pilot(T_core, cdata, pool, pool_limit, max_deletions),
    }
    if name == "E11":
        rec["A01_near_miss_corrected_replay"] = replay_e11_near_miss(T_core, cdata)
    return rec


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pool-limit", type=int, default=24, help="rank-21 pool rows per core for controls/deletion pilot")
    ap.add_argument("--max-deletions", type=int, default=3500, help="unique deletion A-multisets tested per core")
    ap.add_argument("--out", type=Path, default=OUTDIR / "corrected_trace_core_survey.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    records = {}
    for name, cfg in CORES.items():
        print(f"=== {name} ===", flush=True)
        records[name] = core_survey(name, cfg, args.pool_limit, args.max_deletions)
        dp = records[name]["deletion_nearmiss_pilot"]["totals"]
        print(json.dumps({"rank_hist": records[name]["contraction_rank_histogram"], "deletion_totals": dp}, sort_keys=True), flush=True)
    result = {
        "schema": "corrected_trace_core_survey_v1",
        "field": "F2",
        "coefficient_convention": "correct trace row coefficient is M_inv[c,b] on X[b,c], giving tr(M_inv X)=c^T M_inv b; M_inv[b,c] was the old wrong entrywise pairing",
        "purpose": "Route-selection evidence for finite-field codimension-one quotient cores; no lower bound follows from this pilot.",
        "parameters": {"pool_limit": args.pool_limit, "max_deletions": args.max_deletions},
        "cores": records,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    brief = {
        "out": str(args.out),
        "elapsed_sec": result["elapsed_sec"],
        "E11_near_miss_correct_q49_consistent": records["E11"]["A01_near_miss_corrected_replay"]["correct_q49"]["consistent"],
        "E11_near_miss_correct_all_consistent": records["E11"]["A01_near_miss_corrected_replay"]["correct_all_saturated"]["consistent"],
        "deletion_totals_by_core": {k: v["deletion_nearmiss_pilot"]["totals"] for k, v in records.items()},
    }
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
