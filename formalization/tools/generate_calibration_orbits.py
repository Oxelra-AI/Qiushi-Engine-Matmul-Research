"""Emit kernel checks for supplied row transports; no transport search is performed."""

import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nat_list(values):
    require(all(type(n) is int and n >= 0 for n in values), "expected natural numbers")
    return "[" + ", ".join(map(str, values)) + "]"


def generate(args):
    bases = json.loads(args.bases.read_text())
    table = json.loads(args.table.read_text())
    require(len(bases) == len(table) == 29210, "expected every quotient row")
    require(all(0 < len(bs) < 7 and all(0 < b < 128 for b in bs) for bs in bases),
            "invalid quotient basis")
    require(all(table[j][0] < table[j + 1][0] for j in range(29209)), "mask order")
    records = {}
    complete = False
    for line in args.transports.read_text().splitlines():
        r = json.loads(line)
        if "query" in r:
            q = r["query"]
            require(type(q) is int and 0 <= q < 233680 and q not in records, "query key")
            require(type(r["target"]) is int and 0 <= r["target"] < 496, "target")
            require(all(type(g) is int and 0 <= g < 4 for g in r["word"]), "generator")
            records[q] = r
        if r.get("complete") is True and r.get("queries") == 233680:
            complete = True
    require(len(records) == 233680, "missing query transports")
    # The terminal record is supplementary provenance, not a proof premise.
    count = (29210 + args.chunk_size - 1) // args.chunk_size
    args.output.mkdir(parents=True, exist_ok=True)
    selected = [] if args.aggregate_only else (range(count) if args.only is None else [args.only])
    for chunk in selected:
        require(0 <= chunk < count, "chunk index")
        start = chunk * args.chunk_size
        stop = min(start + args.chunk_size, 29210)
        name = f"orbitRecords{chunk:03}"
        lines = ["import QiushiCalibrationOrbitRecords", "",
                 "namespace QiushiMatmul.Calibration", "",
                 "set_option maxRecDepth 200000", "set_option maxHeartbeats 64000000", "",
                 f"-- Sorted-mask rows {start} through {stop - 1}, all eight planes.",
                 f"def {name} : List OrbitRecord := ["]
        for j in range(start, stop):
            ts = []
            for i in range(8):
                r = records[i * 29210 + j]
                ts.append("⟨" + str(r["target"]) + ", " + nat_list(r["word"]) + ", " +
                          nat_list(r["forward"]) + ", " + nat_list(r["backward"]) + "⟩")
            mask, labels = table[j]
            lines.append(f"  ⟨{nat_list(bases[j])}, ⟨{mask}, {labels}⟩, ![" +
                         ", ".join(ts) + "]⟩" + ("," if j + 1 < stop else "]"))
        lines += ["", "set_option maxRecDepth 200000 in",
                  "set_option maxHeartbeats 64000000 in",
                  f"theorem {name}_check : {name}.all (fun r => decide r.Valid) = true := by",
                  "  decide +kernel", "",
                  f"theorem {name}_length : {name}.length = {stop - start} := by decide +kernel",
                  "", "end QiushiMatmul.Calibration", ""]
        (args.output / f"QiushiCalibrationOrbitChunk{chunk:03}.lean").write_text("\n".join(lines))
    lines = [f"import QiushiCalibrationOrbitChunk{i:03}" for i in range(count)]
    lines += ["import QiushiCalibrationTable", "import QiushiCalibrationSort", "",
              "namespace QiushiMatmul.Calibration", "",
              "set_option maxRecDepth 200000", "set_option maxHeartbeats 64000000", "",
              f"def orbitRecordChunks : Fin {count} → List OrbitRecord := ![" +
              ", ".join(f"orbitRecords{i:03}" for i in range(count)) + "]", "",
              "theorem orbitRecordChunks_check (i) :",
              "    (orbitRecordChunks i).all (fun r => decide r.Valid) = true := by",
              "  fin_cases i"]
    lines += [f"  · exact orbitRecords{i:03}_check" for i in range(count)]
    lines += ["", "def allOrbitRecords : List OrbitRecord := (List.ofFn orbitRecordChunks).flatten", "",
              "theorem allOrbitRecords_length : allOrbitRecords.length = 29210 := by decide +kernel", "",
              "theorem allOrbitRecords_valid (r : OrbitRecord) (hr : r ∈ allOrbitRecords) : r.Valid := by",
              "  obtain ⟨rs, hrs, hrow⟩ := List.mem_flatten.mp hr",
              "  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrs",
              "  exact orbitRecords_valid _ (orbitRecordChunks_check i) r hrow", "",
              "/-- Every packed label is bound to the already checked public table. -/",
              "theorem allOrbitRecords_table : allOrbitRecords.map OrbitRecord.row = orderedTable := by",
              "  unfold orderedTable",
              "  rw [← sortFuel_eq _ table.length table (le_refl _)]",
              "  decide +kernel", "",
              "def orbitRecordAt (j : Fin 29210) : OrbitRecord :=",
              "  allOrbitRecords.get ⟨j.val, by rw [allOrbitRecords_length]; exact j.isLt⟩", "",
              "theorem orbitRecordAt_valid (j : Fin 29210) : (orbitRecordAt j).Valid :=",
              "  allOrbitRecords_valid _ (List.get_mem _ _)", "",
              "theorem orbitRecordAt_row (j : Fin 29210) : (orbitRecordAt j).row = tableRow j := by",
              "  have h := congrArg (fun xs : List TableRow => xs[j.val]?) allOrbitRecords_table",
              "  have hl : j.val < allOrbitRecords.length := by rw [allOrbitRecords_length]; exact j.isLt",
              "  have hr : j.val < orderedTable.length := by rw [orderedTable_length]; exact j.isLt",
              "  simp only [List.getElem?_map, List.getElem?_eq_getElem hl,",
              "    List.getElem?_eq_getElem hr, Option.map_some, Option.some.injEq] at h",
              "  exact h", "", "end QiushiMatmul.Calibration", ""]
    (args.output / "QiushiCalibrationOrbitTable.lean").write_text("\n".join(lines))
    print(f"generated {len(selected)} of {count} chunks; complete marker={complete}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transports", type=Path, required=True)
    parser.add_argument("--bases", type=Path, required=True)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--chunk-size", type=int, default=256)
    parser.add_argument("--only", type=int)
    parser.add_argument("--aggregate-only", action="store_true")
    args = parser.parse_args()
    require(args.chunk_size > 0, "positive chunk size required")
    generate(args)
