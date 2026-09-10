#!/usr/bin/env python3
"""analysis: map the J65 DRAT input core back to restricted and full Wang rows.

`drat-trim -c` reports the input clauses used in the verified analysis J-face
UNSAT proof.  The analysis CNF eliminated all points outside J, so the core file
alone does not identify which full 255-point Wang rows were responsible.  This
script regenerates the J-face CNF clause stream with source labels, matches the
core clauses as a multiset, and records the restricted constraints and
representative full E11 Wang rows whose encodings contributed at least one input
clause to the core.

This is an explanatory extraction, not by itself a new theorem: a later script
must re-encode the lifted full-variable formula and verify UNSAT for any stronger
cut.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, Sequence

import numpy as np
from pysat.card import CardEnc, EncType

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402

GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
CORE_CNF_DEFAULT = ROOT / "workspace/data/jface_core/J65_input_core.cnf"
ORIGINAL_CNF = ROOT / "workspace/data/global_J_face/cnf/J65_complete_wang.cnf"
OUTDIR = ROOT / "workspace/data/jface_core"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def norm_clause(clause: Sequence[int]) -> tuple[int, ...]:
    return tuple(sorted(int(x) for x in clause if int(x) != 0))


def parse_dimacs(path: Path) -> tuple[Counter, dict]:
    counts = Counter()
    header = None
    nclauses_seen = 0
    empty = 0
    max_abs = 0
    with path.open("r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                header = {"format": parts[1], "variables": int(parts[2]), "clauses": int(parts[3])}
                continue
            lits = [int(x) for x in line.split()]
            cur = []
            for lit in lits:
                if lit == 0:
                    break
                cur.append(lit)
                max_abs = max(max_abs, abs(lit))
            key = norm_clause(cur)
            if not key:
                empty += 1
            counts[key] += 1
            nclauses_seen += 1
    return counts, {"header": header, "clauses_seen": nclauses_seen, "empty_clause_count": empty, "max_abs_lit": max_abs, "sha256": sha256(path), "path": str(path)}


def load_J(tol: float = 1e-10):
    data = json.loads(GLOBAL_PATH.read_text())
    x = np.array(data["global_lp"]["x_full"], dtype=float)
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return x, J, outside, data


def restrict_mask_to_J(point_bitset: int, full_to_local_bit: Dict[int, int], J_full_mask: int) -> int:
    bs = int(point_bitset) & J_full_mask
    out = 0
    while bs:
        bit = bs & -bs
        p = bit.bit_length()
        out |= 1 << full_to_local_bit[p]
        bs ^= bit
    return out


def local_points_from_mask(mask: int, J: Sequence[int]) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(int(J[bit.bit_length() - 1]))
        bs ^= bit
    return pts


def full_points_from_mask(mask: int) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def gen_card_clauses(lits: Sequence[int], relation: str, bound: int, top: int):
    lits = list(map(int, lits))
    if relation == "atmost":
        if bound < 0:
            return top, [[]], 0
        if len(lits) <= bound:
            return top, [], 0
        if bound == 0:
            return top, [[-lit] for lit in lits], 0
        enc = CardEnc.atmost(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "atleast":
        if bound <= 0:
            return top, [], 0
        if len(lits) < bound:
            return top, [[]], 0
        if len(lits) == bound:
            return top, [[lit] for lit in lits], 0
        enc = CardEnc.atleast(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "equals":
        if bound < 0 or bound > len(lits):
            return top, [[]], 0
        enc = CardEnc.equals(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    else:
        raise ValueError(relation)
    return max(int(top), int(enc.nv)), enc.clauses, max(0, int(enc.nv) - int(top))


def build_restricted_constraints(J: Sequence[int]):
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    full_to_local_bit = {p: i for i, p in enumerate(J)}
    J_full_mask = 0
    for p in J:
        J_full_mask |= 1 << (int(p) - 1)
    constraints_by_mask: Dict[int, int] = {}
    source_count_by_mask = Counter()
    min_source_count_by_mask = Counter()
    strongest_source_by_mask: Dict[int, dict] = {}
    min_sources_by_mask: Dict[int, list] = defaultdict(list)
    raw_relevant = 0
    skipped_pop_le_cap = 0
    zero_intersection = 0
    for idx, rec in enumerate(records):
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        mask = restrict_mask_to_J(int(rec["point_bitset"]), full_to_local_bit, J_full_mask)
        pop = mask.bit_count()
        if pop == 0:
            zero_intersection += 1
            continue
        if pop <= cap:
            skipped_pop_le_cap += 1
            continue
        raw_relevant += 1
        source_count_by_mask[mask] += 1
        src = {
            "row_index": int(idx),
            "key8": int(rec["key8"]),
            "dim8": int(rec["dim8"]),
            "L": L,
            "cap": int(cap),
            "restricted_size": int(pop),
            "full_size": int(int(rec["point_bitset"]).bit_count()),
            "full_point_bitset": int(rec["point_bitset"]),
        }
        if (mask not in constraints_by_mask) or (cap < constraints_by_mask[mask]):
            constraints_by_mask[mask] = int(cap)
            strongest_source_by_mask[mask] = src
            min_sources_by_mask[mask] = [src]
        elif cap == constraints_by_mask[mask]:
            # Keep only a bounded example list; count separately.
            if len(min_sources_by_mask[mask]) < 8:
                min_sources_by_mask[mask].append(src)
        # Count min sources after the final min is known below.
    # Recount minimum-cap sources exactly for each mask without retaining every source object.
    for idx, rec in enumerate(records):
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        mask = restrict_mask_to_J(int(rec["point_bitset"]), full_to_local_bit, J_full_mask)
        if mask in constraints_by_mask and cap == constraints_by_mask[mask] and mask.bit_count() > cap:
            min_source_count_by_mask[mask] += 1
    constraints = [(mask, cap) for mask, cap in constraints_by_mask.items()]
    constraints.sort(key=lambda mc: (mc[1], mc[0].bit_count(), mc[0]))
    return records, complete_meta, lut_meta, constraints, strongest_source_by_mask, source_count_by_mask, min_source_count_by_mask, min_sources_by_mask, {
        "raw_relevant": raw_relevant,
        "zero_intersection": zero_intersection,
        "skipped_pop_le_cap": skipped_pop_le_cap,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=CORE_CNF_DEFAULT)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    args = ap.parse_args()
    t0 = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    core_counts, core_meta = parse_dimacs(args.core)
    core_total = sum(core_counts.values())
    xfrac, J, outside, global_data = load_J()
    records, complete_meta, lut_meta, constraints, strongest_source_by_mask, source_count_by_mask, min_source_count_by_mask, min_sources_by_mask, filter_counts = build_restricted_constraints(J)

    remaining = Counter(core_counts)
    top = len(J)
    clause_index = 0
    generated_clause_count = 0
    matched_clause_count = 0
    exact19_core_clause_count = 0
    exact19_total_clause_count = 0
    exact19_aux = 0
    used_by_constraint_index: dict[int, dict] = {}
    generated_by_constraint_index = {}
    # Exact-19 block.
    top, clauses, naux = gen_card_clauses(list(range(1, len(J) + 1)), "equals", 19, top)
    exact19_aux += naux
    exact19_total_clause_count += len(clauses)
    for cl in clauses:
        clause_index += 1
        generated_clause_count += 1
        k = norm_clause(cl)
        if remaining.get(k, 0) > 0:
            remaining[k] -= 1
            matched_clause_count += 1
            exact19_core_clause_count += 1
    row_clause_total = 0
    row_clause_core = 0
    row_aux_total = 0
    cap_hist = Counter()
    size_hist = Counter()
    for ci, (mask, cap) in enumerate(constraints):
        lits = []
        bs = int(mask)
        while bs:
            bit = bs & -bs
            lits.append(bit.bit_length())  # local variable is local bit + 1
            bs ^= bit
        old_top = top
        top, clauses, naux = gen_card_clauses(lits, "atmost", int(cap), top)
        cap_hist[int(cap)] += 1
        size_hist[len(lits)] += 1
        row_clause_total += len(clauses)
        row_aux_total += naux
        ccore = 0
        for cl in clauses:
            clause_index += 1
            generated_clause_count += 1
            k = norm_clause(cl)
            if remaining.get(k, 0) > 0:
                remaining[k] -= 1
                matched_clause_count += 1
                row_clause_core += 1
                ccore += 1
        if ccore:
            src = strongest_source_by_mask[mask]
            used_by_constraint_index[ci] = {
                "constraint_index": int(ci),
                "core_clause_count": int(ccore),
                "total_clause_count": int(len(clauses)),
                "aux_vars": int(top - old_top),
                "cap": int(cap),
                "restricted_size": int(mask.bit_count()),
                "restricted_mask_hex": hex(int(mask)),
                "restricted_points_full_labels": local_points_from_mask(mask, J),
                "source_count_same_restriction_all_caps": int(source_count_by_mask[mask]),
                "source_count_min_cap": int(min_source_count_by_mask[mask]),
                "representative_full_source": src,
                "representative_full_points": full_points_from_mask(src["full_point_bitset"]),
                "min_source_examples": [
                    {k: v for k, v in src2.items() if k != "full_point_bitset"}
                    for src2 in min_sources_by_mask[mask]
                ],
            }
        generated_by_constraint_index[ci] = len(clauses)
    unmatched = +remaining
    summary = {
        "schema": "j65_input_core_clause_analysis_v1",
        "meaning": "Generated-clause/source mapping for the DRAT input core of the analysis J65 face proof. A used restricted constraint means at least one clause from its sequential at-most encoding appears in the drat-trim input core.",
        "core_cnf": core_meta,
        "original_cnf_path": str(ORIGINAL_CNF),
        "original_cnf_sha256": sha256(ORIGINAL_CNF),
        "global_fractional_solution_file": str(GLOBAL_PATH),
        "J_size": len(J),
        "outside_size": len(outside),
        "filter_counts_recomputed": filter_counts,
        "complete_meta": complete_meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "regenerated_encoding": {
            "final_top_variable": int(top),
            "generated_clause_count": int(generated_clause_count),
            "exact19_total_clause_count": int(exact19_total_clause_count),
            "exact19_aux_vars": int(exact19_aux),
            "row_clause_total": int(row_clause_total),
            "row_aux_total": int(row_aux_total),
            "unique_restricted_constraints": int(len(constraints)),
            "cap_hist_all_unique_restricted": {str(k): int(v) for k, v in sorted(cap_hist.items())},
            "restricted_size_hist_all_unique_restricted": {str(k): int(v) for k, v in sorted(size_hist.items())},
        },
        "matching": {
            "core_clause_total": int(core_total),
            "matched_clause_count": int(matched_clause_count),
            "unmatched_clause_count": int(sum(unmatched.values())),
            "unmatched_distinct_clause_count": int(len(unmatched)),
            "exact19_core_clause_count": int(exact19_core_clause_count),
            "row_core_clause_count": int(row_clause_core),
            "used_restricted_constraint_count": int(len(used_by_constraint_index)),
        },
        "used_constraint_histograms": {
            "by_cap": {str(k): int(v) for k, v in sorted(Counter(r["cap"] for r in used_by_constraint_index.values()).items())},
            "by_restricted_size": {str(k): int(v) for k, v in sorted(Counter(r["restricted_size"] for r in used_by_constraint_index.values()).items())},
            "by_full_dim8": {str(k): int(v) for k, v in sorted(Counter(r["representative_full_source"]["dim8"] for r in used_by_constraint_index.values()).items())},
            "by_full_L": {str(k): int(v) for k, v in sorted(Counter(r["representative_full_source"]["L"] for r in used_by_constraint_index.values()).items())},
        },
        "J_points": J,
        "outside_points": outside,
        "used_constraints_pickle": str(args.outdir / "J65_core_used_constraints.pkl"),
        "used_constraints_jsonl": str(args.outdir / "J65_core_used_constraints.jsonl"),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    # Write large used constraints in stable order.
    used_list = [used_by_constraint_index[i] for i in sorted(used_by_constraint_index)]
    with (args.outdir / "J65_core_used_constraints.pkl").open("wb") as f:
        pickle.dump({
            "J": J,
            "outside": outside,
            "used_constraints": used_list,
            "summary": summary,
        }, f, protocol=pickle.HIGHEST_PROTOCOL)
    with (args.outdir / "J65_core_used_constraints.jsonl").open("w") as f:
        for rec in used_list:
            slim = dict(rec)
            # Keep full points in JSONL for direct inspection; omit huge bitset only.
            slim["representative_full_source"] = {k: v for k, v in slim["representative_full_source"].items() if k != "full_point_bitset"}
            f.write(json.dumps(slim, sort_keys=True) + "\n")
    (args.outdir / "J65_core_clause_analysis.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "analysis": str(args.outdir / "J65_core_clause_analysis.json"),
        "used_constraints": len(used_list),
        "core_clauses": core_total,
        "matched": matched_clause_count,
        "unmatched": int(sum(unmatched.values())),
        "exact19_core_clause_count": exact19_core_clause_count,
        "row_core_clause_count": row_clause_core,
        "used_hist_by_L": summary["used_constraint_histograms"]["by_full_L"],
        "used_hist_by_dim8": summary["used_constraint_histograms"]["by_full_dim8"],
        "elapsed_sec": summary["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
