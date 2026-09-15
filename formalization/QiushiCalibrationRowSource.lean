import QiushiCalibrationOrbitRecords
import QiushiCalibrationRowsTransport484
import QiushiCalibrationRowsTransport485
import QiushiCalibrationRowsTransport486
import QiushiCalibrationRowsTransport487
import QiushiCalibrationRowsTransport488
import QiushiCalibrationRowsTransport489
import QiushiCalibrationRowsTransport490
import QiushiCalibrationRowsTransport491

namespace QiushiMatmul.Calibration

open CalibrationRows

def rowImages : Fin 8 → Fin 9 → Nat :=
  ![images484, images485, images486, images487, images488, images489, images490, images491]

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem rowSource_base : ∀ i : Fin 8,
    planeBasis i = [256, 128].map (fun c => matrixCodeNat (codeLinear (rowImages i) (codeMat c))) := by
  decide +kernel

theorem rowSource_lift : ∀ i : Fin 8, ∀ c : Fin 128,
    (coordinateLift i c).val = matrixCodeNat (codeLinear (rowImages i) (codeMat c.val)) := by
  decide +kernel

/-- Exact ordered-list equality with the coordinate-transported source basis. -/
theorem rowSource_eq_map (i : Fin 8) (bs : List Nat) (hb : ∀ c ∈ bs, c < 128) :
    rowSource i bs = ([256, 128] ++ bs).map
      (fun c => matrixCodeNat (codeLinear (rowImages i) (codeMat c))) := by
  rw [List.map_append]
  unfold rowSource
  rw [rowSource_base]
  congr 1
  apply List.map_congr_left
  intro c hc
  have h := rowSource_lift i ⟨c, hb c hc⟩
  simpa only [Nat.mod_eq_of_lt (hb c hc)] using h

end QiushiMatmul.Calibration
