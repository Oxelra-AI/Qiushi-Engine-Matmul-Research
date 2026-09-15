import QiushiAllHighPlaneQInv1

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecQTInv_two : ∀ b : Fin 512,
    (ahSecQ (2 : Fin 3) b).transpose * ahSecQTInv (2 : Fin 3) b = 1 := by
  decide +revert

end QiushiMatmul
