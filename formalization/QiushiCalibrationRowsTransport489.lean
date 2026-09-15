import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane489

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images489 : Fin 9 → Nat := ![1, 2, 4, 16, 32, 64, 128, 10, 258]

theorem kernel489 : ∀ c : Fin 512,
    codeLinear images489 (codeMat c.val) = 0 → c = 0 := by decide

theorem section489 : ∀ j : Fin 127,
    codeLinear images489 (codeMat (j.val + 1)) =
      codeMat (lift489 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport489 : RowTransport standardCoordinates coordinates489 where
  linear := codeLinearEquiv images489 kernel489
  base := by
    change (spanCodes [256, 128]).map (codeLinear images489) = spanCodes [258, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(258, 256), (10, 128)] (codeLinear images489)
      (by decide) (by decide)).symm
  lift_eq := section489

end QiushiMatmul.CalibrationRows
