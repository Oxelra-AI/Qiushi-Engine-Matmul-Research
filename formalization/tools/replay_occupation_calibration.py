"""Replay the report's positive controls against every hash-bound public LUT row.

This is a computational check, not a Lean theorem about frozenWangTable.L0.
No solver, original DRAT proof, recorded success flag, or truncated live-row
system is used. The public independent quotient-row implementation is reused.
"""

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import pickle
import sys


class PrimitiveUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        raise pickle.UnpicklingError("only primitive table data is accepted")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_module(path):
    spec = importlib.util.spec_from_file_location("calibration_semantics", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def decode_support(support):
    counts = [0] * 127
    seen = set()
    for q, weight in support:
        require(type(q) is int and 1 <= q <= 127, "invalid quotient direction")
        require(type(weight) is int and weight > 0, "invalid multiplicity")
        require(q not in seen, "duplicate support entry")
        seen.add(q)
        counts[q - 1] = weight
    return counts


def tensor_mismatches(terms):
    require(len(terms) == 23, "control must have 23 terms")
    require(all(len(t) == 3 and all(type(x) is int and 0 <= x < 512 for x in t)
                for t in terms), "invalid tensor coefficient code")
    mismatches = []
    for a in range(9):
        for b in range(9):
            for c in range(9):
                expected = int(b // 3 == a % 3 and c // 3 == a // 3 and c % 3 == b % 3)
                actual = sum(((u >> a) & 1) * ((v >> b) & 1) * ((w >> c) & 1)
                             for u, v, w in terms) % 2
                if actual != expected:
                    mismatches.append([a, b, c])
    return mismatches


def replay(repo, lut_file):
    proof = repo / "proof"
    manifest = json.loads((proof / "manifest.json").read_text())
    receipts = {row["path"]: row["sha256"] for row in manifest["files"]}
    paths = {
        "summary": "assets/occupation/data/dim2_independent/independent_semantics_summary.json",
        "orbit491": "assets/occupation/data/dim2_independent/orbit491_target19_long.json",
        "lut": "assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl",
    }
    hashes = {}
    for name, relative in paths.items():
        path = lut_file if name == "lut" else proof / relative
        hashes[relative] = digest(path)
        require(hashes[relative] == receipts[relative], f"manifest hash mismatch: {relative}")
    with lut_file.open("rb") as stream:
        data = PrimitiveUnpickler(stream).load()
        require(not stream.read(1), "trailing bytes after frozen LUT")
    lut = data["lut"] if "lut" in data else data
    require(isinstance(lut, dict) and len(lut) == 8283458, "incomplete frozen LUT")

    summary = json.loads((proof / paths["summary"]).read_text())
    later = json.loads((proof / paths["orbit491"]).read_text())
    control_relative = "research/materials/quotient_cores/results/pivot_fixed/pivot17_rank23_transformed_control.json"
    control = repo / control_relative
    hashes[control_relative] = digest(control)
    control_byte_match = hashes[control_relative] == summary["rank23_control_sha256"]
    terms = json.loads(control.read_text())["terms"]
    require(not tensor_mismatches(terms), "rank-23 control fails the canonical tensor identity")

    script_relative = "assets/occupation/scripts/dim2_independent_semantics.py"
    script = proof / script_relative
    hashes[script_relative] = digest(script)
    require(hashes[script_relative] == receipts[script_relative], "row-builder hash mismatch")
    sem = load_module(script)
    sem.all_subspaces = lru_cache(maxsize=None)(sem.all_subspaces)
    require(len(sem.all_subspaces(7)) == 29212, "quotient subspace enumeration incomplete")
    require([r["cert_index"] for r in summary["results"]] == list(range(484, 492)),
            "unexpected orbit list")

    results = []
    for record in summary["results"]:
        index = record["cert_index"]
        W = record["W_basis_from_orbit"]
        free = sem.free_bits(sem.rref_ind(W))
        require(free == record["row_records"]["18"]["meta"]["free_bits"], "coordinate mismatch")
        rows18, meta = sem.independent_rows(W, lut, 18)
        require(len(rows18) == 29210 and meta["missing_lut_rows"] == 0,
                f"orbit {index}: incomplete row set")
        require(meta["row_digest"] == record["row_records"]["18"]["meta"]["row_digest"],
                f"orbit {index}: full-row digest mismatch")
        rows19 = [(mask, cap + 1) for mask, cap in rows18]
        witness = later["solve"] if index == 491 else record["target_ladder"]["19"]
        if index == 491:
            require(later["W_basis"] == W and later["target"] == 19, "wrong later witness")
        counts19 = decode_support(witness["solution_head"])
        require(sum(counts19) == 19, f"orbit {index}: incomplete target-19 witness")
        require(sum(x != 0 for x in counts19) == witness["nonzero_count"], "truncated witness")
        scan19 = sem.scan_counts(counts19, rows19)
        require(scan19["violations"] == 0, f"orbit {index}: target-19 row violation")
        require(sem.canonical_rows_digest(sorted(rows19, key=lambda mc: (mc[1], mc[0].bit_count(), mc[0])))
                == record["row_records"]["19"]["meta"]["row_digest"], "target-19 digest mismatch")

        projection = sem.project_rank23_control(W, free, control)
        length = projection["projected_length"]
        projected_rows = [(mask, cap + length - 18) for mask, cap in rows18]
        scan23 = sem.scan_counts(projection["counts"], projected_rows)
        require(scan23["violations"] == 0, f"orbit {index}: projected-control row violation")
        require(projection["counts"] == decode_support(
            record["projected_rank23_positive_control"]["projected_control"]["support_head"]),
            "projection differs from recorded complete support")

        singleton_caps = [None] * 127
        for mask, cap in rows18:
            if mask.bit_count() == 1:
                q = mask.bit_length() - 1
                require(singleton_caps[q] is None, "duplicate singleton row")
                singleton_caps[q] = cap
        require(all(x is not None for x in singleton_caps), "missing singleton row")
        hist = dict(sorted(Counter(singleton_caps).items()))
        expected = {0: 95, 1: 31, 2: 1} if index == 489 else None
        if expected is not None:
            require(hist == expected, "orbit 489 cap distribution differs")
        else:
            require(set(hist) == {0, 1}, f"orbit {index}: non-Boolean target-18 cap")
        cert_relative = f"assets/occupation/data/dim2_cnf_cert_all/orbit_{index}/orbit_{index}_target_18_certificate.json"
        cert_path = proof / cert_relative
        hashes[cert_relative] = digest(cert_path)
        require(hashes[cert_relative] == receipts[cert_relative], "cap-certificate hash mismatch")
        cert = json.loads(cert_path.read_text())
        require({str(k): v for k, v in hist.items()} == cert["singleton_upper_bound_hist"],
                "cap histogram differs from public certificate")
        item = {
            "orbit": index, "W_basis": W, "free_bits": free, "full_rows": len(rows18),
            "target18_row_digest": meta["row_digest"],
            "target19_support": witness["solution_head"], "target19_scan": scan19,
            "projected_length": length, "projected_killed_terms": projection["killed_terms"],
            "projected_rank23_scan": scan23, "target18_singleton_cap_histogram": hist,
            "target18_cap2_directions": [q + 1 for q, cap in enumerate(singleton_caps) if cap == 2],
        }
        results.append(item)
        print(f"orbit {index}: all {len(rows18)} rows pass both controls; singleton caps {hist}", flush=True)

    return {
        "status": "pass", "scope": "full public frozen-LUT computational replay, not Lean L0 equality",
        "lean_theorem": False, "input_sha256": hashes,
        "control_binding": {
            "historical_sha256": summary["rank23_control_sha256"],
            "available_sha256": hashes[control_relative],
            "historical_bytes_match": control_byte_match,
            "validated_semantics": "all 729 tensor coefficients and exact agreement with all eight recorded projected supports",
        },
        "tensor_coordinates_checked": 729, "lut_entries": len(lut),
        "rows_per_control_family": sum(r["full_rows"] for r in results), "results": results,
        "formal_blocker": "FrozenWangBindings proves selected-row lower bounds only; positive calibration requires full-row upper bounds or exact L0 bindings.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--lut", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # Importing the public row builder must not create files in the parent.
    sys.dont_write_bytecode = True
    result = replay(args.repo.resolve(), args.lut.resolve())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
