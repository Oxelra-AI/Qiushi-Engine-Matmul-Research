#!/usr/bin/env python3
"""Generate a shared seven-bit row catalogue and kernel-checkable certificates.

Enumerate RREF pivot patterns directly, then use the existing certificate
generator's rref/span routines to validate each candidate. No orbit search,
numeric labels, lookup-table pickle, or positive witness is consumed.
"""

import argparse
from collections import Counter
import hashlib
import importlib.util
from itertools import combinations
import json
from pathlib import Path


def enumerate_rows(certificate):
    rows = []
    for dim in range(1, 7):
        for pivots in combinations(range(7), dim):
            slots = [(i, bit) for i, pivot in enumerate(pivots)
                     for bit in range(pivot) if bit not in pivots]
            for pattern in range(1 << len(slots)):
                basis = [1 << pivot for pivot in pivots]
                for k, (i, bit) in enumerate(slots):
                    basis[i] |= ((pattern >> k) & 1) << bit
                basis = tuple(reversed(basis))
                assert certificate.rref(basis) == basis
                span = certificate.span(basis)
                assert len(span) == 1 << dim and all(q < 128 for q in span)
                mask = sum(1 << (q - 1) for q in span if q)
                rows.append({"basis": basis, "mask": mask,
                             "present": min(span - {0}) - 1,
                             "absent": next(q - 1 for q in range(1, 128) if q not in span)})
    rows.sort(key=lambda r: r["mask"])
    assert len(rows) == 29210 and len({r["mask"] for r in rows}) == 29210
    assert Counter(len(r["basis"]) for r in rows) == {
        1: 127, 2: 2667, 3: 11811, 4: 11811, 5: 2667, 6: 127}
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate-generator", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--chunk-size", type=int, default=512)
    args = parser.parse_args()
    if not 1 <= args.chunk_size <= 1024:
        parser.error("chunk-size must be between 1 and 1024")
    spec = importlib.util.spec_from_file_location("certificate", args.certificate_generator)
    certificate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(certificate)
    rows = enumerate_rows(certificate)
    args.output.mkdir(parents=True, exist_ok=True)
    chunks = [rows[i:i + args.chunk_size] for i in range(0, len(rows), args.chunk_size)]
    names = []
    for n, chunk in enumerate(chunks):
        name = f"QiushiCalibrationRowsChunk{n:03d}"
        names.append(name)
        literal = ",\n  ".join(
            "⟨[" + ", ".join(map(str, r["basis"])) +
            f"], {r['mask']}, {r['present']}, {r['absent']}⟩" for r in chunk)
        source = f'''import QiushiCalibrationRowsCatalogue

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

def data{n:03d} : List RowData := [
  {literal}]

theorem valid{n:03d} : ∀ d ∈ data{n:03d}, d.Valid := by decide
theorem length{n:03d} : data{n:03d}.length = {len(chunk)} := by decide

end QiushiMatmul.CalibrationRows
'''
        (args.output / (name + ".lean")).write_text(source)
    imports = "\n".join("import " + name for name in names)
    order = f'''{imports}

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
'''
    for n, chunk in enumerate(chunks):
        first, last = chunk[0]["mask"], chunk[-1]["mask"]
        order += f'''
theorem maskSorted{n:03d} : (data{n:03d}.map RowData.mask).IsChain (· < ·) := by decide
theorem maskHead{n:03d} : (data{n:03d}.map RowData.mask).head? = some {first} := by decide
theorem maskLast{n:03d} : (data{n:03d}.map RowData.mask).getLast? = some {last} := by decide
'''
    for n in reversed(range(len(chunks))):
        first = chunks[n][0]["mask"]
        if n == len(chunks) - 1:
            order += f'''
def maskSuffix{n:03d} : List Nat := data{n:03d}.map RowData.mask
theorem suffixSorted{n:03d} : maskSuffix{n:03d}.IsChain (· < ·) := maskSorted{n:03d}
theorem suffixHead{n:03d} : maskSuffix{n:03d}.head? = some {first} := maskHead{n:03d}
'''
        else:
            last, next_first = chunks[n][-1]["mask"], chunks[n + 1][0]["mask"]
            order += f'''
def maskSuffix{n:03d} : List Nat := data{n:03d}.map RowData.mask ++ maskSuffix{n + 1:03d}
theorem suffixSorted{n:03d} : maskSuffix{n:03d}.IsChain (· < ·) := by
  apply (maskSorted{n:03d}).append suffixSorted{n + 1:03d}
  rw [maskLast{n:03d}, suffixHead{n + 1:03d}]
  intro a ha b hb
  have hA : a = {last} := by simpa [eq_comm] using ha
  have hB : b = {next_first} := by simpa [eq_comm] using hb
  rw [hA, hB]
  decide
theorem suffixHead{n:03d} : maskSuffix{n:03d}.head? = some {first} := by
  change (data{n:03d}.map RowData.mask ++ maskSuffix{n + 1:03d}).head? = _
  rw [List.head?_append, maskHead{n:03d}]
  rfl
'''
    order += "\nend QiushiMatmul.CalibrationRows\n"
    (args.output / "QiushiCalibrationRowsOrder.lean").write_text(order)
    data_expr = f"data{len(chunks) - 1:03d}"
    for n in reversed(range(len(chunks) - 1)):
        data_expr = f"data{n:03d} ++ ({data_expr})"
    length_proof = f"length{len(chunks) - 1:03d}"
    valid_proof = f"valid{len(chunks) - 1:03d}"
    map_proof = f"(rfl : data{len(chunks) - 1:03d}.map RowData.mask = maskSuffix{len(chunks) - 1:03d})"
    for n in reversed(range(len(chunks) - 1)):
        length_proof = f"append_length_eq length{n:03d} ({length_proof})"
        valid_proof = f"append_valid valid{n:03d} ({valid_proof})"
        map_proof = (f"append_mask_map (rfl : data{n:03d}.map RowData.mask = "
                     f"data{n:03d}.map RowData.mask) ({map_proof})")
    source = f'''import QiushiCalibrationRowsOrder

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

/-- Ascending numeric mask order, independent of every orbit's L0 labels. -/
def allData : List RowData := {data_expr}

private theorem append_length_eq {{a b : List RowData}} {{n m : Nat}}
    (ha : a.length = n) (hb : b.length = m) : (a ++ b).length = n + m :=
  List.length_append.trans (congrArg₂ Nat.add ha hb)

private theorem append_valid {{a b : List RowData}}
    (ha : ∀ d ∈ a, d.Valid) (hb : ∀ d ∈ b, d.Valid) : ∀ d ∈ a ++ b, d.Valid := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact ha d h
  · exact hb d h

private theorem append_mask_map {{a b : List RowData}} {{c d : List Nat}}
    (ha : a.map RowData.mask = c) (hb : b.map RowData.mask = d) :
    (a ++ b).map RowData.mask = c ++ d :=
  (List.map_append ..).trans (congrArg₂ List.append ha hb)

theorem allData_length : allData.length = 29210 :=
  {length_proof}

theorem allData_valid : ∀ d ∈ allData, d.Valid :=
  {valid_proof}

theorem allData_masks : allData.map RowData.mask = maskSuffix000 :=
  {map_proof}

theorem allData_sorted : (allData.map RowData.mask).IsChain (· < ·) :=
  allData_masks.symm ▸ suffixSorted000

def standardRows : Fin 29210 → Row standardCoordinates :=
  catalogueRows allData allData_length allData_valid

theorem standardRows_distinct : Function.Injective
    (fun i j => (standardRows i).mask.testBit j.val : Fin 29210 → Fin 127 → Bool) :=
  catalogueRows_distinct allData allData_length allData_valid allData_sorted

theorem standardRows_complete (U : Submodule F2 Mat3)
    (hWU : spanCodes [256, 128] < U) (hU : U < ⊤) :
    ∃! i, (standardRows i).space = U :=
  catalogueRows_complete allData allData_length allData_valid allData_sorted U hWU hU

end QiushiMatmul.CalibrationRows
'''
    (args.output / "QiushiCalibrationRowsData.lean").write_text(source)
    receipt = {"row_count": len(rows), "order": "ascending numeric mask",
               "chunk_size": args.chunk_size, "chunk_modules": names,
               "certificate_generator_sha256": hashlib.sha256(
                   args.certificate_generator.read_bytes()).hexdigest(),
               "rows": rows}
    (args.output / "QiushiCalibrationRowsCatalogue.json").write_text(
        json.dumps(receipt, separators=(",", ":")) + "\n")
    print(f"Generated {len(rows)} rows in {len(chunks)} chunks.")


if __name__ == "__main__":
    main()
