#!/usr/bin/env python3
"""Generate eight finite quotient charts from the public semantic summary.

Only plane bases and free-bit order are consumed, never labels or witnesses.
All quotient separation and coverage claims are checked in Lean.
"""

import argparse
import hashlib
import json
from pathlib import Path


def bit_sum(variable, source_bits, target_bits):
    return " +\n    ".join(f"(if {variable}.testBit {s} then {1 << t} else 0)"
                           for s, t in zip(source_bits, target_bits))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    raw = args.summary.read_bytes()
    records = json.loads(raw)["results"]
    assert sorted(r["cert_index"] for r in records) == list(range(484, 492))
    args.output.mkdir(parents=True, exist_ok=True)
    for record in records:
        index = record["cert_index"]
        basis = record["W_basis_from_orbit"]
        free = record["row_records"]["18"]["meta"]["free_bits"]
        pivots = [b.bit_length() - 1 for b in basis]
        assert len(basis) == 2 and len(set(pivots)) == 2
        assert free == [b for b in range(9) if b not in pivots]
        reduction = "n.val"
        for b, pivot in zip(basis, pivots):
            reduction = f"Nat.xor ({reduction}) (if n.val.testBit {pivot} then {b} else 0)"
        source = f'''import QiushiCalibrationRows
import QiushiPlane{index}GenData

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def lift{index} (q : Fin 128) : Fin 512 :=
  ⟨({bit_sum("q.val", range(7), free)}) % 512, Nat.mod_lt _ (by decide)⟩

def label{index} (n : Fin 512) : Fin 128 :=
  let r := {reduction}
  ⟨({bit_sum("r", free, range(7))}) % 128, Nat.mod_lt _ (by decide)⟩

theorem separate{index} : ∀ a b : Fin 128,
    xorCode (lift{index} a) (lift{index} b) ∈ spanEnum {basis} ↔ a = b := by
  decide

theorem cover{index} : ∀ c : Fin 512,
    xorCode c (lift{index} (label{index} c)) ∈ spanEnum {basis} := by
  decide

def coordinates{index} : Coordinates plane{index}GenConfig.planeBasis where
  lift := lift{index}
  label := label{index}
  zero := by decide
  separate := separate{index}
  cover := cover{index}

theorem label{index}_correct (c : Fin 512) :
    coordinates{index}.quotientEquiv (label{index} c) =
      plane{index}GenConfig.W.mkQ (codeMat c.val) :=
  coordinates{index}.label_correct c

end QiushiMatmul.CalibrationRows
'''
        (args.output / f"QiushiCalibrationRowsPlane{index}.lean").write_text(source)
        images = [1 << bit for bit in free] + [basis[1], basis[0]]
        image_vector = "![" + ", ".join(map(str, images)) + "]"
        transport = f'''import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane{index}

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images{index} : Fin 9 → Nat := {image_vector}

theorem kernel{index} : ∀ c : Fin 512,
    codeLinear images{index} (codeMat c.val) = 0 → c = 0 := by decide

theorem section{index} : ∀ j : Fin 127,
    codeLinear images{index} (codeMat (j.val + 1)) =
      codeMat (lift{index} ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport{index} : RowTransport standardCoordinates coordinates{index} where
  linear := codeLinearEquiv images{index} kernel{index}
  base := by
    change (spanCodes [256, 128]).map (codeLinear images{index}) = spanCodes {basis}
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [({basis[0]}, 256), ({basis[1]}, 128)] (codeLinear images{index})
      (by decide) (by decide)).symm
  lift_eq := section{index}

end QiushiMatmul.CalibrationRows
'''
        (args.output / f"QiushiCalibrationRowsTransport{index}.lean").write_text(transport)
    imports = "\n".join(f"import QiushiCalibrationRowsTransport{i}" for i in range(484, 492))
    source = f'''import QiushiCalibrationRowsData
import QiushiCalibrationRowsSpanMap
import QiushiCalibrationRowsProjection
import QiushiCalibrationRowsLabels
{imports}

namespace QiushiMatmul.CalibrationRows

open OccupationSystemBridge

def rowMask (i : Fin 29210) : Nat := (standardRows i).mask

def quotientBasis (i : Fin 29210) : List Nat :=
  (allData.get ⟨i.val, by rw [allData_length]; exact i.isLt⟩).basis
'''
    for index in range(484, 492):
        source += f'''
def rowBasis{index} (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images{index} (codeMat c)))

noncomputable def rows{index} (i : Fin 29210) : Row coordinates{index} :=
  (standardRows i).transport transport{index}

theorem rows{index}_mask (i : Fin 29210) : (rows{index} i).mask = rowMask i := rfl

theorem rows{index}_space (i : Fin 29210) :
    (rows{index} i).space = spanCodes (rowBasis{index} i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images{index})

theorem rows{index}_complete (U : Submodule F2 Mat3)
    (hWU : plane{index}GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows{index} i).space = U :=
  transported_rows_complete transport{index} standardRows standardRows_distinct U hWU hU

theorem rowBasis{index}_complete (U : Submodule F2 Mat3)
    (hWU : plane{index}GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis{index} i) = U := by
  simpa only [rows{index}_space] using rows{index}_complete U hWU hU

theorem rows{index}_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates{index}.weight x) (spanCodes (rowBasis{index} i)) := by
  simpa only [rows{index}_mask, rows{index}_space] using (rows{index} i).maskMass_eq x

theorem caps{index}_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis{index} i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane{index}GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates{index}.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows{index}_mask, rows{index}_space] using
    row_caps_iff rows{index} (fun U hWU hU => (rows{index}_complete U hWU hU).exists)
      L target x
'''
    source += "\nend QiushiMatmul.CalibrationRows\n"
    (args.output / "QiushiCalibrationRowsAll.lean").write_text(source)
    receipt = {"summary_sha256": hashlib.sha256(raw).hexdigest(),
               "indices": list(range(484, 492)),
               "consumed_fields": ["cert_index", "W_basis_from_orbit",
                                   "row_records.18.meta.free_bits"]}
    (args.output / "QiushiCalibrationRowsCoordinates.json").write_text(
        json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
