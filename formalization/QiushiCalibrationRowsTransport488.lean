import QiushiCalibrationRowsTransport
import QiushiCalibrationRowsPlane488

namespace QiushiMatmul.CalibrationRows

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

def images488 : Fin 9 → Nat := ![1, 2, 4, 16, 32, 128, 256, 10, 96]

theorem kernel488 : ∀ c : Fin 512,
    codeLinear images488 (codeMat c.val) = 0 → c = 0 := by decide

theorem section488 : ∀ j : Fin 127,
    codeLinear images488 (codeMat (j.val + 1)) =
      codeMat (lift488 ⟨j.val + 1, by omega⟩).val := by decide

noncomputable def transport488 : RowTransport standardCoordinates coordinates488 where
  linear := codeLinearEquiv images488 kernel488
  base := by
    change (spanCodes [256, 128]).map (codeLinear images488) = spanCodes [96, 10]
    exact (spanCodes_map_eq_of_code_pairs [256, 128]
      [(96, 256), (10, 128)] (codeLinear images488)
      (by decide) (by decide)).symm
  lift_eq := section488

end QiushiMatmul.CalibrationRows
