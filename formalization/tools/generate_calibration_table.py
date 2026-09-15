"""Export all 29210 public quotient rows for kernel calibration checks.

The labels are hash-bound literal LUT values, not assertions about Lean L0.
Rows have the common order (quotient dimension, lexicographic RREF basis).
"""

import argparse
import json
from pathlib import Path
import sys

from replay_occupation_calibration import PrimitiveUnpickler, digest, load_module, require


def generate(repo, lut_path, out, chunk_size, json_output=None):
    proof = repo / "proof"
    receipts = {r["path"]: r["sha256"] for r in
                json.loads((proof / "manifest.json").read_text())["files"]}
    require(digest(lut_path) == receipts[
        "assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl"], "LUT hash mismatch")
    summary_path = proof / "assets/occupation/data/dim2_independent/independent_semantics_summary.json"
    require(digest(summary_path) == receipts[str(summary_path.relative_to(proof))], "summary hash")
    script_path = proof / "assets/occupation/scripts/dim2_independent_semantics.py"
    require(digest(script_path) == receipts[str(script_path.relative_to(proof))], "builder hash")
    sem = load_module(script_path)
    with lut_path.open("rb") as stream:
        data = PrimitiveUnpickler(stream).load()
        require(not stream.read(1), "trailing LUT bytes")
    lut = data["lut"] if "lut" in data else data
    records = json.loads(summary_path.read_text())["results"]
    require([r["cert_index"] for r in records] == list(range(484, 492)), "orbit order")
    bases = [sem.rref_ind(r["W_basis_from_orbit"]) for r in records]
    frees = [sem.free_bits(b) for b in bases]
    spaces = [b for b in sem.all_subspaces(7) if 0 < len(b) < 7]
    require(len(spaces) == 29210, "row count")
    rows = []
    public_rows = [[] for _ in range(8)]
    for basis in spaces:
        mask = sem.qbasis_mask(basis)
        labels = []
        for i, (W, free) in enumerate(zip(bases, frees)):
            U = sem.rref_ind((*W, *(sem.lift_q_ind(q, free) for q in basis)))
            label = lut[sem.pack_ind(U)]
            require(type(label) is int and 0 <= label < 32, "label encoding overflow")
            labels.append(label)
            public_rows[i].append((mask, 18 - label))
        rows.append((mask, sum(label << (5 * i) for i, label in enumerate(labels))))
    for record, orbit_rows in zip(records, public_rows):
        ordered = sorted(orbit_rows, key=lambda mc: (mc[1], mc[0].bit_count(), mc[0]))
        require(sem.canonical_rows_digest(ordered) ==
                record["row_records"]["18"]["meta"]["row_digest"], "full row digest mismatch")
    if json_output is not None:
        json_output.write_text(json.dumps(sorted(rows)) + "\n")
    for chunk, start in enumerate(range(0, len(rows), chunk_size)):
        part = rows[start:start + chunk_size]
        name = f"tableChunk{chunk:03}"
        lines = ["import QiushiCalibrationFormula", "", "namespace QiushiMatmul.Calibration", "",
                 f"-- Generated public rows {start} through {start + len(part) - 1}.",
                 f"def {name} : List TableRow := ["]
        lines += [f"  ⟨{mask}, {labels}⟩" + ("," if k + 1 < len(part) else "]")
                  for k, (mask, labels) in enumerate(part)]
        lines += ["", "set_option maxRecDepth 200000 in",
                  "set_option maxHeartbeats 24000000 in",
                  f"theorem {name}_check : {name}.all TableRow.check = true := by",
                  "  decide +kernel", "",
                  f"theorem {name}_length : {name}.length = {len(part)} := by decide +kernel", "",
                  "end QiushiMatmul.Calibration", ""]
        path = out / f"QiushiCalibrationTable{chunk:03}.lean"
        content = "\n".join(lines)
        if not path.exists() or path.read_text() != content:
            path.write_text(content)
    count = (len(rows) + chunk_size - 1) // chunk_size
    lines = [f"import QiushiCalibrationTable{i:03}" for i in range(count)]
    lines += ["", "namespace QiushiMatmul.Calibration", "",
              "set_option maxRecDepth 200000", "set_option maxHeartbeats 24000000", "",
              f"def tableChunks : Fin {count} → List TableRow := ![" +
              ", ".join(f"tableChunk{i:03}" for i in range(count)) + "]", "",
              "theorem tableChunks_check (i) : (tableChunks i).all TableRow.check = true := by",
              "  fin_cases i"]
    lines += [f"  · exact tableChunk{i:03}_check" for i in range(count)]
    lines += ["", "def table : List TableRow := (List.ofFn tableChunks).flatten", "",
              "set_option maxRecDepth 200000 in", "set_option maxHeartbeats 24000000 in",
              "theorem table_length : table.length = 29210 := by decide +kernel", "",
              "theorem table_controls (row : TableRow) (hr : row ∈ table) : row.ControlsHold := by",
              "  obtain ⟨rs, hrs, hrow⟩ := List.mem_flatten.mp hr",
              "  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrs",
              "  exact controlsHold_of_all_check _ (tableChunks_check i) row hrow", "",
              "/-- Numeric-mask order used by the independent geometric catalogue. -/",
              "def orderedTable : List TableRow := table.mergeSort (fun a b => decide (a.mask ≤ b.mask))", "",
              "theorem orderedTable_length : orderedTable.length = 29210 := by",
              "  simpa only [orderedTable, List.length_mergeSort] using table_length", "",
              "theorem orderedTable_controls (row : TableRow) (hr : row ∈ orderedTable) : row.ControlsHold :=",
              "  table_controls row (List.mem_mergeSort.mp hr)", "",
              "def tableRow (j : Fin 29210) : TableRow :=",
              "  orderedTable.get ⟨j.val, by rw [orderedTable_length]; exact j.isLt⟩", "",
              "theorem tableRow_controls (j : Fin 29210) : (tableRow j).ControlsHold :=",
              "  orderedTable_controls _ (List.get_mem _ _)", "",
              "end QiushiMatmul.Calibration", ""]
    (out / "QiushiCalibrationTable.lean").write_text("\n".join(lines))
    # A reviewable index for the independent semantic row instantiation.
    (out / "calibration_quotient_bases.json").write_text(json.dumps(spaces) + "\n")
    print(f"generated {len(rows)} rows in {(len(rows) + chunk_size - 1) // chunk_size} chunks", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--lut", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--chunk-size", type=int, default=256)
    parser.add_argument("--json", type=Path, help="optional sorted numeric row export")
    args = parser.parse_args()
    require(args.chunk_size > 0, "positive chunk size required")
    sys.dont_write_bytecode = True
    generate(args.repo.resolve(), args.lut.resolve(), args.output.resolve(), args.chunk_size, args.json)
