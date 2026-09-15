import QiushiAllHighPlaneQInv

namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecSelectors_ne_all : ∀ k : Fin 3, ∀ b : Fin 512,
    ahSecValid k b → ahSecSelA k b ≠ ahSecSelB k b := by
  decide +revert

end QiushiMatmul
