import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane484

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images484 : Fin 9 → Nat := ![1, 2, 4, 32, 64, 128, 256, 10, 19]

theorem kernel484 : ∀ c : Fin 512,
    codeLinear images484 (codeMat c.val) = 0 → c = 0 := by decide

theorem section484 : ∀ j : Fin 127,
    codeLinear images484 (codeMat (j.val + 1)) =
      codeMat (lift484 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport484 : RowTransport standardCoordinates coordinates484 where
  linear := codeLinearEquiv images484 kernel484
  base := by
    change (spanCodes [256, 128]).map (codeLinear images484) = spanCodes [19, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(19, 256), (10, 128)] (codeLinear images484)
      (by decide) (by decide)).symm
  lift_eq := section484

end QiushiMatmul.CalibrationRows
