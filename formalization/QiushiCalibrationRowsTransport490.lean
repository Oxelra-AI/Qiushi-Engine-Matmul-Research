import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane490

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images490 : Fin 9 → Nat := ![1, 2, 4, 16, 32, 64, 128, 10, 275]

theorem kernel490 : ∀ c : Fin 512,
    codeLinear images490 (codeMat c.val) = 0 → c = 0 := by decide

theorem section490 : ∀ j : Fin 127,
    codeLinear images490 (codeMat (j.val + 1)) =
      codeMat (lift490 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport490 : RowTransport standardCoordinates coordinates490 where
  linear := codeLinearEquiv images490 kernel490
  base := by
    change (spanCodes [256, 128]).map (codeLinear images490) = spanCodes [275, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(275, 256), (10, 128)] (codeLinear images490)
      (by decide) (by decide)).symm
  lift_eq := section490

end QiushiMatmul.CalibrationRows
