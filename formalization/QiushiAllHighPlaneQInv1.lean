import QiushiAllHighPlaneQInv0

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecQTInv_one : ∀ b : Fin 512,
    (ahSecQ (1 : Fin 3) b).transpose * ahSecQTInv (1 : Fin 3) b = 1 := by
  decide +revert

end QiushiMatmul
