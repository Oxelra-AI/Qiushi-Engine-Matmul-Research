import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane486

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images486 : Fin 9 → Nat := ![1, 2, 4, 16, 32, 128, 256, 10, 68]

theorem kernel486 : ∀ c : Fin 512,
    codeLinear images486 (codeMat c.val) = 0 → c = 0 := by decide

theorem section486 : ∀ j : Fin 127,
    codeLinear images486 (codeMat (j.val + 1)) =
      codeMat (lift486 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport486 : RowTransport standardCoordinates coordinates486 where
  linear := codeLinearEquiv images486 kernel486
  base := by
    change (spanCodes [256, 128]).map (codeLinear images486) = spanCodes [68, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(68, 256), (10, 128)] (codeLinear images486)
      (by decide) (by decide)).symm
  lift_eq := section486

end QiushiMatmul.CalibrationRows
