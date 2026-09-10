#!/usr/bin/env python3
"""analysis: tau-restricted flip walk from the standard 27-term seed.

This script implements the transpose involution
    tau(A,B,C) = (A^T, C^T, B^T)
for the 3x3 matrix multiplication tensor over F_3 and performs exact flip-graph
walks starting from the standard/naive 27-term decomposition.  The scientific
purpose is calibration: unlike Laderman, the standard seed has many duplicate
component factors, so a tau-orbit flip implementation should move immediately
and should at least find tau-invariant rank-23 schemes if this restricted graph
is a useful search object.

The script is deliberately auditable Python rather than optimized C++: every
accepted move is checked for exact tensor equality to T_333 and exact tau
invariance of the stored factor triples.  No miss rate is interpreted as a
mathematical exclusion.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
from collections import Counter, defaultdict
import numpy as np

P = 3
SESSION = Path(__file__).resolve().parents[1]
OUT = SESSION / "data" / "tau_naive_walk"
OUT.mkdir(parents=True, exist_ok=True)

NEXT = {0: 1, 1: 2, 2: 0}
PREV = {0: 2, 1: 0, 2: 1}
SIGMA = {0: 0, 1: 2, 2: 1}  # tau maps A to A, B<->C


def eij(i: int, j: int) -> np.ndarray:
    M = np.zeros((3, 3), dtype=np.int8)
    M[i, j] = 1
    return M.reshape(9) % P


def matT(v: np.ndarray) -> np.ndarray:
    return np.asarray(v, dtype=np.int8).reshape(3, 3).T.reshape(9) % P


def standard_scheme() -> list[tuple[np.ndarray, np.ndarray, np.ndarray]]:
    # t_{i,j,k}=E_ij \otimes E_jk \otimes E_ki.
    terms = []
    for i in range(3):
        for j in range(3):
            for k in range(3):
                terms.append((eij(i, j), eij(j, k), eij(k, i)))
    return terms


def tau_term(t):
    a, b, c = t
    return (matT(a), matT(c), matT(b))


def term_key_exact(t) -> tuple:
    return tuple(int(x) for comp in t for x in (comp % P))


def is_zero_vec(v) -> bool:
    return not bool(np.any(np.asarray(v) % P))


def is_zero_term(t) -> bool:
    return is_zero_vec(t[0]) or is_zero_vec(t[1]) or is_zero_vec(t[2])


def rank_count(scheme) -> int:
    return sum(0 if is_zero_term(t) else 1 for t in scheme)


def term_tensor(t) -> np.ndarray:
    a, b, c = t
    return np.einsum("i,j,k->ijk", a % P, b % P, c % P, optimize=True).reshape(-1) % P


T333 = np.zeros((9, 9, 9), dtype=np.int8)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T333[3 * i + j, 3 * j + k, 3 * k + i] = 1
T333_VEC = T333.reshape(-1) % P


def scheme_tensor(scheme) -> np.ndarray:
    acc = np.zeros(729, dtype=np.int16)
    for t in scheme:
        if not is_zero_term(t):
            acc += term_tensor(t).astype(np.int16)
    return (acc % P).astype(np.int8)


def exact_tau_perm(scheme):
    """Return a label permutation if tau maps every stored nonzero triple exactly."""
    buckets: dict[tuple, list[int]] = defaultdict(list)
    for i, t in enumerate(scheme):
        if not is_zero_term(t):
            buckets[term_key_exact(t)].append(i)
    perm = [None] * len(scheme)
    used = set()
    for i, t in enumerate(scheme):
        if is_zero_term(t):
            continue
        key = term_key_exact(tau_term(t))
        cand = None
        for j in buckets.get(key, []):
            if j not in used:
                cand = j
                break
        if cand is None:
            return None
        used.add(cand)
        perm[i] = cand
    return perm


def tau_invariant_exact(scheme) -> bool:
    return exact_tau_perm(scheme) is not None


def copy_scheme(scheme):
    return [(a.copy(), b.copy(), c.copy()) for a, b, c in scheme]


def set_comp(scheme, idx: int, comp: int, new_val) -> None:
    new_val = np.asarray(new_val, dtype=np.int8) % P
    if is_zero_vec(new_val):
        z = np.zeros(9, dtype=np.int8)
        scheme[idx] = (z.copy(), z.copy(), z.copy())
    else:
        a, b, c = scheme[idx]
        lst = [a.copy(), b.copy(), c.copy()]
        lst[comp] = new_val.copy()
        scheme[idx] = tuple(lst)


def apply_flip_inplace(scheme, typ: int, i: int, j: int) -> bool:
    """flip-cpd flip for an ordered pair sharing component typ."""
    if i == j or is_zero_term(scheme[i]) or is_zero_term(scheme[j]):
        return False
    if not np.array_equal(scheme[i][typ] % P, scheme[j][typ] % P):
        return False
    tn, tp = NEXT[typ], PREV[typ]
    n1 = scheme[i][tn].copy()
    n2 = scheme[j][tn].copy()
    p1 = scheme[i][tp].copy()
    p2 = scheme[j][tp].copy()
    set_comp(scheme, i, tn, (n1 - n2) % P)
    set_comp(scheme, j, tp, (p1 + p2) % P)
    return True


def duplicate_pairs(scheme):
    pairs = []
    for typ in range(3):
        buckets: dict[tuple, list[int]] = defaultdict(list)
        for i, t in enumerate(scheme):
            if not is_zero_term(t):
                buckets[tuple(int(x) for x in (t[typ] % P))].append(i)
        for inds in buckets.values():
            if len(inds) >= 2:
                for i in inds:
                    for j in inds:
                        if i != j:
                            pairs.append((typ, i, j))
    return pairs


def orbit_type(perm, i: int, j: int) -> str:
    ti, tj = perm[i], perm[j]
    if ti is None or tj is None:
        return "zero"
    i_fixed = (ti == i)
    j_fixed = (tj == j)
    if i_fixed and j_fixed:
        return "fixed-fixed"
    if i_fixed or j_fixed:
        return "fixed-free"
    if len({i, j, ti, tj}) == 4:
        return "free-free-4"
    return "free-free-overlap"


def paired_tau_flip(scheme, typ: int, i: int, j: int, *, require_free_free=False):
    perm = exact_tau_perm(scheme)
    if perm is None:
        return None, "not_tau_invariant_before"
    cls = orbit_type(perm, i, j)
    if require_free_free and cls != "free-free-4":
        return None, "filtered_" + cls
    ti, tj = perm[i], perm[j]
    typ2 = SIGMA[typ]
    new = copy_scheme(scheme)
    if not apply_flip_inplace(new, typ, i, j):
        return None, "primary_invalid"
    # If the tau-image flip acts on a term zeroed by the primary flip, the naive
    # sequential composition is not a clean orbit flip.  We still try and accept
    # only if exact tensor and tau checks pass; reason counts tell us how often
    # these overlaps appear.
    if not apply_flip_inplace(new, typ2, ti, tj):
        return None, "image_invalid"
    if not np.array_equal(scheme_tensor(new), T333_VEC):
        return None, "tensor_changed"
    if not tau_invariant_exact(new):
        return None, "tau_lost"
    return new, "accepted_" + cls


def all_accepted_moves(scheme, *, require_free_free=False, max_test=None, rng=None):
    pairs = duplicate_pairs(scheme)
    if rng is not None:
        rng.shuffle(pairs)
    if max_test is not None:
        pairs = pairs[:max_test]
    moves = []
    reasons = Counter()
    for typ, i, j in pairs:
        new, reason = paired_tau_flip(scheme, typ, i, j, require_free_free=require_free_free)
        reasons[reason] += 1
        if new is not None:
            moves.append((typ, i, j, rank_count(new), new, reason.replace("accepted_", "")))
    return moves, reasons, len(pairs)


def fingerprint(scheme) -> tuple:
    # Exact factor-triple multiset fingerprint; sufficient for visited pruning in this auditable script.
    return tuple(sorted(term_key_exact(t) for t in scheme if not is_zero_term(t)))


def summarize_seed(scheme):
    perm = exact_tau_perm(scheme)
    fixed = [i for i, j in enumerate(perm) if j == i]
    free = []
    seen = set(fixed)
    for i, j in enumerate(perm):
        if j is None or i in seen:
            continue
        free.append((i, j))
        seen.add(i); seen.add(j)
    bucket_hist = {}
    for typ in range(3):
        buckets = defaultdict(list)
        for i, t in enumerate(scheme):
            buckets[tuple(int(x) for x in t[typ])].append(i + 1)
        sizes = Counter(len(v) for v in buckets.values())
        bucket_hist[str(typ)] = {str(k): int(v) for k, v in sorted(sizes.items())}
    return {
        "rank": rank_count(scheme),
        "tensor_matches_T333_F3": bool(np.array_equal(scheme_tensor(scheme), T333_VEC)),
        "tau_invariant_exact": perm is not None,
        "fixed_count": len(fixed),
        "free_orbit_count": len(free),
        "fixed_indices_1based": [i + 1 for i in fixed],
        "free_orbits_1based": [[i + 1, j + 1] for i, j in free],
        "duplicate_bucket_size_hist_by_component": bucket_hist,
        "duplicate_ordered_pair_count": len(duplicate_pairs(scheme)),
    }


def one_step_calibration(seed, rng):
    out = {}
    for mode, require in [("free_free_only", True), ("all_overlap_checked", False)]:
        moves, reasons, tested = all_accepted_moves(seed, require_free_free=require, rng=rng)
        rh = Counter(r for _, _, _, r, _, _ in moves)
        cls = Counter(c for *_, c in moves)
        out[mode] = {
            "tested_duplicate_pairs": tested,
            "accepted_move_count": len(moves),
            "reason_counts": dict(reasons),
            "accepted_orbit_class_counts": dict(cls),
            "rank_hist_after_one_step": {str(k): int(v) for k, v in sorted(rh.items())},
            "min_rank_after_one_step": min(rh.keys()) if rh else rank_count(seed),
        }
    return out


def save_scheme_json(path: Path, scheme, meta):
    serial = []
    for a, b, c in scheme:
        if is_zero_term((a, b, c)):
            continue
        serial.append({
            "A": [int(x) for x in a % P],
            "B": [int(x) for x in b % P],
            "C": [int(x) for x in c % P],
        })
    data = dict(meta)
    data.update({
        "field": "F3",
        "rank": rank_count(scheme),
        "term_count_nonzero": len(serial),
        "tensor_matches_T333_F3": bool(np.array_equal(scheme_tensor(scheme), T333_VEC)),
        "tau_invariant_exact": bool(tau_invariant_exact(scheme)),
        "terms": serial,
    })
    path.write_text(json.dumps(data, indent=2) + "\n")


def random_walks(seed, *, restarts, steps, mode_name, require_free_free, max_pairs_per_node, rng_seed):
    rng = random.Random(rng_seed)
    best = {"rank": rank_count(seed), "scheme": copy_scheme(seed), "restart": None, "ARTIFACT": 0, "path": []}
    rank_hits: dict[str, list[str]] = defaultdict(list)
    restart_summaries = []
    global_reason = Counter()
    first_rank23_saved = None
    first_rank22_saved = None
    total_accepted = 0
    total_nodes_with_no_moves = 0
    t0 = time.time()

    for r in range(restarts):
        scheme = copy_scheme(seed)
        path = []
        local_hist = Counter({rank_count(scheme): 1})
        local_best = rank_count(scheme)
        no_moves = False
        for s in range(steps):
            moves, reasons, tested = all_accepted_moves(
                scheme,
                require_free_free=require_free_free,
                max_test=max_pairs_per_node,
                rng=rng,
            )
            global_reason.update(reasons)
            if not moves:
                no_moves = True
                total_nodes_with_no_moves += 1
                break
            # Bias toward reductions if present, otherwise random accepted orbit flip.
            min_rank = min(m[3] for m in moves)
            if min_rank < rank_count(scheme):
                candidates = [m for m in moves if m[3] == min_rank]
            else:
                candidates = moves
            typ, i, j, rr, new, cls = rng.choice(candidates)
            scheme = new
            total_accepted += 1
            path.append({"type": typ, "i": i + 1, "j": j + 1, "rank": rr, "class": cls})
            local_hist[rr] += 1
            if rr < local_best:
                local_best = rr
            if rr < best["rank"]:
                best = {"rank": rr, "scheme": copy_scheme(scheme), "restart": r, "ARTIFACT": s + 1, "path": path[-30:]}
            if rr <= 23 and first_rank23_saved is None:
                pth = OUT / f"{mode_name}_first_rank{rr}_restart{r}_step{s+1}.json"
                save_scheme_json(pth, scheme, {"mode": mode_name, "restart": r, "ARTIFACT": s + 1, "last_path_tail": path[-30:]})
                first_rank23_saved = str(pth.relative_to(SESSION))
            if rr <= 22 and first_rank22_saved is None:
                pth = OUT / f"{mode_name}_first_rank{rr}_restart{r}_step{s+1}.json"
                save_scheme_json(pth, scheme, {"mode": mode_name, "restart": r, "ARTIFACT": s + 1, "last_path_tail": path[-50:]})
                first_rank22_saved = str(pth.relative_to(SESSION))
                break
        restart_summaries.append({
            "restart": r,
            "steps_done": len(path),
            "best_rank": local_best,
            "final_rank": rank_count(scheme),
            "no_moves": no_moves,
            "rank_hist": {str(k): int(v) for k, v in sorted(local_hist.items())},
        })
        if first_rank22_saved is not None:
            break

    best_path = OUT / f"{mode_name}_best_rank{best['rank']}.json"
    save_scheme_json(best_path, best["scheme"], {"mode": mode_name, "restart": best["restart"], "ARTIFACT": best["ARTIFACT"], "last_path_tail": best["path"]})
    summary = {
        "mode": mode_name,
        "field": "F3",
        "require_free_free": require_free_free,
        "restarts_requested": restarts,
        "steps_per_restart": steps,
        "max_pairs_per_node": max_pairs_per_node,
        "restarts_completed": len(restart_summaries),
        "total_accepted_moves": total_accepted,
        "nodes_with_no_accepted_moves": total_nodes_with_no_moves,
        "best_rank": best["rank"],
        "best_scheme_path": str(best_path.relative_to(SESSION)),
        "first_rank_le_23_path": first_rank23_saved,
        "first_rank_le_22_path": first_rank22_saved,
        "global_reason_counts": dict(global_reason),
        "restart_summaries_first20": restart_summaries[:20],
        "restart_summaries_last5": restart_summaries[-5:],
        "elapsed_sec": time.time() - t0,
        "interpretation": "Exact tau-preserving random walk calibration. Rank hits are verified decompositions over F3; absence of a rank-22 hit is heuristic only.",
    }
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--restarts", type=int, default=200)
    ap.add_argument("--steps", type=int, default=200)
    ap.add_argument("--max-pairs", type=int, default=240, help="maximum shuffled duplicate-pair tests per node")
    ap.add_argument("--seed", type=int, default=20260907)
    ap.add_argument("--free-free-restarts", type=int, default=80)
    ap.add_argument("--free-free-steps", type=int, default=120)
    args = ap.parse_args()

    seed_scheme = standard_scheme()
    rng = random.Random(args.seed)
    out = {
        "source": "standard 27-term seed t_{ijk}=E_ij⊗E_jk⊗E_ki over F3",
        "tau": "tau(A,B,C)=(A^T,C^T,B^T), maps (i,j,k) to (j,i,k)",
        "seed_summary": summarize_seed(seed_scheme),
        "one_step_calibration": one_step_calibration(seed_scheme, rng),
        "mp_paper_lookup": {
            "paper": "Moosbauer--Poole, Flip Graphs with Symmetry and New Matrix Multiplication Schemes",
            "read_lines": "object.md lines 104, 198, 263, 294",
            "finding": "Their implemented groups are C3 and C3 x Z2 where Z2 reverses rows/columns inside each factor and commutes with C3; this is not the transpose-type tau swapping factors B and C. For n=3 they report matching rank 23 with C3 and diagonal partitions, not a single tau-Z2 rank-22/23 table.",
        },
    }
    out["walk_free_free_only"] = random_walks(
        seed_scheme,
        restarts=args.free_free_restarts,
        steps=args.free_free_steps,
        mode_name="free_free_only",
        require_free_free=True,
        max_pairs_per_node=args.max_pairs,
        rng_seed=args.seed + 1,
    )
    out["walk_all_overlap_checked"] = random_walks(
        seed_scheme,
        restarts=args.restarts,
        steps=args.steps,
        mode_name="all_overlap_checked",
        require_free_free=False,
        max_pairs_per_node=args.max_pairs,
        rng_seed=args.seed + 2,
    )

    path = OUT / "tau_naive_walk_summary.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({
        "seed": out["seed_summary"],
        "one_step": out["one_step_calibration"],
        "free_free": out["walk_free_free_only"],
        "all_overlap": out["walk_all_overlap_checked"],
        "saved": str(path),
    }, indent=2)[:20000])
    print("SAVED", path)

if __name__ == "__main__":
    main()
