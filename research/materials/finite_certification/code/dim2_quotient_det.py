#!/usr/bin/env python3
"""General dim-2 A-quotient tools for the analysis lower-bound route.

For a two-dimensional A-subspace W in F2^9, build the quotient tensor
T333/W in F2^(7) x F2^9 x F2^9 using the same RREF/complement convention as
node_local_occupation_closure.py.  Then, for a fixed quotient A-multiset,
run the relaxed tight-trace filter or a fixed-A Brent SAT encoding augmented
with tight-contraction inverse-determination constraints.

The script is intentionally independent of the older one-pivot quotient code:
analysis needs the three dim-2 orbit representatives 481, 482, 483.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from full_fixed_a_completion_tight import CNF, mat_rank, parse_solver_solution  # type: ignore
from full_fixed_a_completion_det import add_inverse_det_B_to_C, add_inverse_det_C_to_B  # type: ignore
from quotient_tight_trace_filter import generalized_inverse, consistent  # type: ignore

PROFILE = Path("data/wang_f2_lb20/cert_profile.json")
CASCADE = Path("data/wang_analysis/cascade/dim3_raises_to_dim2.json")
FULL_WITNESS = Path("data/full_fixed_a_controls/pivot17_rank23/pivot17_rank23_witness.json")


def rref_basis(rows: Iterable[int], nbits: int = 9) -> tuple[int, ...]:
    basis: list[int] = []
    for x0 in rows:
        x = int(x0)
        if x == 0:
            continue
        for rb in basis:
            p = rb.bit_length() - 1
            if (x >> p) & 1:
                x ^= rb
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, rb in enumerate(basis):
            if (rb >> p) & 1:
                basis[i] = rb ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)


def reduce_mod(v0: int, W: Sequence[int]) -> int:
    v = int(v0)
    for rb in W:
        p = int(rb).bit_length() - 1
        if p >= 0 and ((v >> p) & 1):
            v ^= int(rb)
    return v


def free_bits(W: Sequence[int], nbits: int = 9) -> list[int]:
    piv = {int(rb).bit_length() - 1 for rb in W if int(rb)}
    return [i for i in range(nbits) if i not in piv]


def project_mod(v: int, W: Sequence[int]) -> int:
    W = rref_basis(W, 9)
    rem = reduce_mod(v, W)
    fb = free_bits(W, 9)
    q = 0
    for i, bit in enumerate(fb):
        if (rem >> bit) & 1:
            q |= 1 << i
    return q


def lift_q(q: int, W: Sequence[int]) -> int:
    fb = free_bits(rref_basis(W, 9), 9)
    v = 0
    for i, bit in enumerate(fb):
        if (int(q) >> i) & 1:
            v |= 1 << bit
    return v


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def quotient_tensor_W(W_basis: Sequence[int]) -> np.ndarray:
    W = rref_basis(W_basis, 9)
    k = 9 - len(W)
    T = build_t333()
    Q = np.zeros((k, 9, 9), dtype=np.uint8)
    for s in range(9):
        q = project_mod(1 << s, W)
        if q:
            for qb in range(k):
                if (q >> qb) & 1:
                    Q[qb] ^= T[s]
    return Q


def orbit_basis(index: int) -> list[int]:
    prof = json.loads(PROFILE.read_text())
    for rec in prof["dimension_2_orbits"]:
        if int(rec["index"]) == int(index):
            return [int(x) for x in rec["constraint_values"]]
    raise KeyError(f"no dim-2 orbit index {index}")


def support_from_cascade(index: int) -> list[int]:
    d = json.loads(CASCADE.read_text())
    records = d.get("results", {}).get("dim2", [])
    for rec in records:
        if int(rec.get("cert_index", -1)) == int(index):
            head = rec.get("solve", {}).get("solution_head")
            if not head:
                raise ValueError(f"orbit {index} has no solution_head in cascade")
            out: list[int] = []
            for q, mult in head:
                out.extend([int(q)] * int(mult))
            if len(out) != int(rec.get("support_size_tested", len(out))):
                raise ValueError(f"support size mismatch for {index}: got {len(out)}")
            return out
    raise KeyError(f"no dim2 record {index} in {CASCADE}")


def parse_support_arg(s: str | None, index: int | None = None) -> list[int]:
    if s is None or s == "cascade":
        if index is None:
            raise ValueError("--support cascade requires --orbit-index")
        return support_from_cascade(index)
    p = Path(s)
    if p.exists():
        d = json.loads(p.read_text())
        if isinstance(d, list):
            return [int(x) for x in d]
        for key in ["support", "A", "A_multiset", "q_multiset", "q_A_multiset", "quotient_a_multiset", "final_multiset"]:
            if key in d:
                return [int(x) for x in d[key]]
        raise ValueError(f"no support-like key in {p}")
    return [int(x) for x in s.replace(";", ",").replace(" ", ",").split(",") if x.strip()]


def lambda_matrix(Q: np.ndarray, lam: int) -> np.ndarray:
    M = np.zeros((9, 9), dtype=np.uint8)
    for s in range(Q.shape[0]):
        if (int(lam) >> s) & 1:
            M ^= Q[s]
    return M


def build_tensor_rows(Q: np.ndarray, support: Sequence[int]) -> tuple[list[int], list[int]]:
    rows: list[int] = []
    rhs: list[int] = []
    for s in range(Q.shape[0]):
        active = [t for t, u in enumerate(support) if (int(u) >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                local = 9 * b + c
                for t in active:
                    x |= 1 << (81 * t + local)
                rows.append(x)
                rhs.append(int(Q[s, b, c]))
    return rows, rhs


def trace_coeff_row(G: np.ndarray, term: int, nterms: int) -> int:
    x = 0
    base = 81 * term
    for row in range(9):
        for col in range(9):
            if int(G[col, row]) & 1:
                x |= 1 << (base + 9 * row + col)
    return x


def tight_lambda_data(Q: np.ndarray, support: Sequence[int]) -> list[dict]:
    k = Q.shape[0]
    out = []
    for lam in range(1, 1 << k):
        active = [t for t, u in enumerate(support) if ((int(lam) & int(u)).bit_count() & 1)]
        M = lambda_matrix(Q, lam)
        r = mat_rank(M)
        if r > 0 and len(active) == r:
            G, r2, _P, _R, _D = generalized_inverse(M)
            assert r2 == r
            out.append({"lambda": int(lam), "rank": int(r), "active_terms": active, "G": G, "M": M})
    return out


def trace_analyze(W_basis: Sequence[int], support: Sequence[int]) -> dict:
    t0 = time.time()
    Q = quotient_tensor_W(W_basis)
    nvars = 81 * len(support)
    base_rows, base_rhs = build_tensor_rows(Q, support)
    base_ok, base_rank, base_aug = consistent(base_rows, base_rhs, nvars)
    tight = tight_lambda_data(Q, support)
    rows = list(base_rows); rhs = list(base_rhs)
    for rec in tight:
        for t in rec["active_terms"]:
            rows.append(trace_coeff_row(rec["G"], int(t), len(support)))
            rhs.append(1)
    full_ok, full_rank, full_aug = consistent(rows, rhs, nvars)
    hist = Counter(int(r["rank"]) for r in tight)
    return {
        "schema": "dim2_quotient_trace_v1",
        "W_basis": [int(x) for x in W_basis],
        "W_rref": [int(x) for x in rref_basis(W_basis, 9)],
        "quotient_dim": int(Q.shape[0]),
        "quotient_tensor_nnz": int(Q.sum()),
        "support": [int(x) for x in support],
        "support_size": len(support),
        "variables_X": nvars,
        "tensor_equations": len(base_rows),
        "tensor_consistent": bool(base_ok),
        "tensor_rank_aug": [int(base_rank), int(base_aug)],
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted((int(k), int(v)) for k, v in hist.items())),
        "trace_equations": len(rows) - len(base_rows),
        "full_trace_consistent": bool(full_ok),
        "full_rank_aug": [int(full_rank), int(full_aug)],
        "tight_lambdas_head": [{"lambda": int(r["lambda"]), "rank": int(r["rank"]), "active_terms": [int(t) for t in r["active_terms"]]} for r in tight[:80]],
        "elapsed_sec": time.time() - t0,
    }


def verify_quotient(A: Sequence[int], B: Sequence[int], C: Sequence[int], Q: np.ndarray) -> int:
    R = np.zeros_like(Q)
    for a, b, c in zip(A, B, C):
        for s in range(Q.shape[0]):
            if not ((int(a) >> s) & 1):
                continue
            for i in range(9):
                if not ((int(b) >> i) & 1):
                    continue
                for j in range(9):
                    if (int(c) >> j) & 1:
                        R[s, i, j] ^= 1
    return int(np.count_nonzero(R ^ Q))


def encode_det(W_basis: Sequence[int], A: Sequence[int], cnf_path: Path, mode: str) -> dict:
    Q = quotient_tensor_W(W_basis)
    r = len(A)
    F = CNF()
    V = [[F.new_var() for _ in range(9)] for _ in range(r)]
    C = [[F.new_var() for _ in range(9)] for _ in range(r)]
    P = [[[F.new_var() for _ in range(9)] for _ in range(9)] for _ in range(r)]
    for t in range(r):
        for b in range(9):
            for c in range(9):
                F.add_and2(P[t][b][c], V[t][b], C[t][c])
    xor_terms = 0
    for s in range(Q.shape[0]):
        active = [t for t, a in enumerate(A) if (int(a) >> s) & 1]
        for b in range(9):
            for c in range(9):
                xs = [P[t][b][c] for t in active]
                xor_terms += len(xs)
                F.add_xor_eq(xs, int(Q[s, b, c]))
    tight = []
    for lam in range(1, 1 << Q.shape[0]):
        active = [t for t, a in enumerate(A) if ((int(lam) & int(a)).bit_count() & 1)]
        M = lambda_matrix(Q, lam)
        rr = mat_rank(M)
        if rr > 0 and len(active) == rr:
            tight.append({"lambda": int(lam), "rank": int(rr), "active_terms": active, "M": M})
    extras = {}
    if mode in ("b2c", "both"):
        extras.update(add_inverse_det_B_to_C(F, V, C, tight))
    if mode in ("c2b", "both"):
        extras.update(add_inverse_det_C_to_B(F, V, C, tight))
    hist = Counter(int(x["rank"]) for x in tight)
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    F.write(cnf_path, comments=[
        f"dim2 quotient fixed-A determinant CNF rank={r} mode={mode}",
        "W_basis=" + ",".join(map(str, W_basis)),
        "A_multiset=" + ",".join(map(str, A))[:1000],
        "tight_rank_hist=" + json.dumps(dict(sorted((int(k), int(v)) for k, v in hist.items())), sort_keys=True),
    ])
    return {
        "rank": r,
        "quotient_dim": int(Q.shape[0]),
        "quotient_tensor_nnz": int(Q.sum()),
        "cnf_vars": int(F.nv),
        "cnf_clauses": int(len(F.clauses)),
        "base_vc_vars": int(2 * r * 9),
        "product_vars": int(r * 81),
        "xor_terms_total": int(xor_terms),
        "cnf_path": str(cnf_path),
        "mode": mode,
        "tight_lambda_count": len(tight),
        "tight_rank_hist": dict(sorted((int(k), int(v)) for k, v in hist.items())),
        **extras,
    }


def run_solver(cnf: Path, solver: str, timeout: int):
    cmd = [solver, str(cnf)]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 20)
    return proc, time.time() - t0, cmd


def det_solve(W_basis: Sequence[int], support: Sequence[int], outdir: Path, name: str, timeout: int, solver: str, mode: str) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    cnf = outdir / f"{name}.cnf"
    info = encode_det(W_basis, support, cnf, mode)
    proc, elapsed, cmd = run_solver(cnf, solver, timeout)
    sat = None
    if proc.returncode == 10:
        sat = True
    elif proc.returncode == 20:
        sat = False
    rec = {
        "schema": "dim2_quotient_fixed_a_det_v1",
        "W_basis": [int(x) for x in W_basis],
        "W_rref": [int(x) for x in rref_basis(W_basis, 9)],
        "A_multiset": [int(x) for x in support],
        "A_size": len(support),
        "encoding": info,
        "solver": solver,
        "solver_command": cmd,
        "returncode": int(proc.returncode),
        "sat": sat,
        "elapsed_sec": elapsed,
        "stdout_tail": "\n".join(proc.stdout.splitlines()[-80:]),
        "stderr_tail": "\n".join(proc.stderr.splitlines()[-80:]),
    }
    if sat is True:
        sol = parse_solver_solution(proc.stdout, len(support))
        if sol is not None:
            B, C = sol
            Q = quotient_tensor_W(W_basis)
            diff = verify_quotient(support, B, C, Q)
            rec["verification_diff"] = int(diff)
            rec["B_masks"] = [int(x) for x in B]
            rec["C_masks"] = [int(x) for x in C]
            if diff == 0:
                wit = outdir / f"{name}_witness.json"
                wit.write_text(json.dumps({"terms": [[int(a), int(b), int(c)] for a, b, c in zip(support, B, C)], "rank": len(support), "verified": True, "W_basis": [int(x) for x in W_basis]}, indent=2, sort_keys=True) + "\n")
                rec["witness_path"] = str(wit)
    out = outdir / f"{name}_result.json"
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return rec


def project_full_witness(W_basis: Sequence[int]) -> dict:
    Q = quotient_tensor_W(W_basis)
    w = json.loads(FULL_WITNESS.read_text())
    qterms = []
    zero = 0
    for a, b, c in w["terms"]:
        q = project_mod(int(a), W_basis)
        if q == 0:
            zero += 1
        else:
            qterms.append((q, int(b), int(c)))
    R = np.zeros_like(Q)
    for q, b, c in qterms:
        for s in range(Q.shape[0]):
            if not ((q >> s) & 1):
                continue
            for i in range(9):
                if not ((b >> i) & 1):
                    continue
                for j in range(9):
                    if (c >> j) & 1:
                        R[s, i, j] ^= 1
    return {
        "schema": "dim2_quotient_projection_control_v1",
        "W_basis": [int(x) for x in W_basis],
        "W_rref": [int(x) for x in rref_basis(W_basis, 9)],
        "source_witness": str(FULL_WITNESS),
        "projected_nonzero_terms": len(qterms),
        "projected_zero_terms": zero,
        "verification_diff": int(np.count_nonzero(R ^ Q)),
        "q_A_hist": dict(sorted((str(k), int(v)) for k, v in Counter(q for q, _b, _c in qterms).items())),
        "q_A_multiset": [int(q) for q, _b, _c in qterms],
        "q_terms": [[int(q), int(b), int(c)] for q, b, c in qterms],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-index", type=int, required=True)
    ap.add_argument("--action", choices=["trace", "det", "control"], required=True)
    ap.add_argument("--support", default="cascade")
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--outdir", type=Path, default=None)
    ap.add_argument("--name", default=None)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--solver", default="cadical", choices=["cadical", "kissat", "cryptominisat5"])
    ap.add_argument("--mode", default="b2c", choices=["b2c", "c2b", "both"])
    args = ap.parse_args()
    W = orbit_basis(args.orbit_index)
    if args.action == "control":
        rec = project_full_witness(W)
        out = args.out or Path(f"data/dim2_quotients/orbit{args.orbit_index}/projection_control.json")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"out": str(out), "verification_diff": rec["verification_diff"], "projected_nonzero_terms": rec["projected_nonzero_terms"], "projected_zero_terms": rec["projected_zero_terms"]}, indent=2, sort_keys=True))
    elif args.action == "trace":
        supp = parse_support_arg(args.support, args.orbit_index)
        rec = trace_analyze(W, supp)
        rec["orbit_index"] = int(args.orbit_index)
        out = args.out or Path(f"data/dim2_quotients/orbit{args.orbit_index}/cascade_support_trace.json")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"out": str(out), "orbit_index": args.orbit_index, "support_size": len(supp), "tensor_consistent": rec["tensor_consistent"], "tight_lambda_count": rec["tight_lambda_count"], "tight_rank_hist": rec["tight_rank_hist"], "full_trace_consistent": rec["full_trace_consistent"], "full_rank_aug": rec["full_rank_aug"], "elapsed_sec": rec["elapsed_sec"]}, indent=2, sort_keys=True))
    else:
        supp = parse_support_arg(args.support, args.orbit_index)
        outdir = args.outdir or Path(f"data/dim2_quotients/orbit{args.orbit_index}/det")
        name = args.name or "cascade_support_det"
        rec = det_solve(W, supp, outdir, name, args.timeout, args.solver, args.mode)
        print(json.dumps({"out": str(outdir / f'{name}_result.json'), "orbit_index": args.orbit_index, "sat": rec["sat"], "returncode": rec["returncode"], "elapsed_sec": rec["elapsed_sec"], "solver": args.solver, "vars": rec["encoding"]["cnf_vars"], "clauses": rec["encoding"]["cnf_clauses"], "tight_lambda_count": rec["encoding"]["tight_lambda_count"], "tight_rank_hist": rec["encoding"]["tight_rank_hist"], "verification_diff": rec.get("verification_diff")}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
