import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane491

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images491 : Fin 9 → Nat := ![1, 2, 4, 8, 16, 32, 256, 84, 163]

theorem kernel491 : ∀ c : Fin 512,
    codeLinear images491 (codeMat c.val) = 0 → c = 0 := by decide

theorem section491 : ∀ j : Fin 127,
    codeLinear images491 (codeMat (j.val + 1)) =
      codeMat (lift491 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport491 : RowTransport standardCoordinates coordinates491 where
  linear := codeLinearEquiv images491 kernel491
  base := by
    change (spanCodes [256, 128]).map (codeLinear images491) = spanCodes [163, 84]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(163, 256), (84, 128)] (codeLinear images491)
      (by decide) (by decide)).symm
  lift_eq := section491

end QiushiMatmul.CalibrationRows
