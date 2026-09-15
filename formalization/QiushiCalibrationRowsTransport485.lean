import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane485

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images485 : Fin 9 → Nat := ![1, 2, 4, 32, 64, 128, 256, 10, 20]

theorem kernel485 : ∀ c : Fin 512,
    codeLinear images485 (codeMat c.val) = 0 → c = 0 := by decide

theorem section485 : ∀ j : Fin 127,
    codeLinear images485 (codeMat (j.val + 1)) =
      codeMat (lift485 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport485 : RowTransport standardCoordinates coordinates485 where
  linear := codeLinearEquiv images485 kernel485
  base := by
    change (spanCodes [256, 128]).map (codeLinear images485) = spanCodes [20, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(20, 256), (10, 128)] (codeLinear images485)
      (by decide) (by decide)).symm
  lift_eq := section485

end QiushiMatmul.CalibrationRows
