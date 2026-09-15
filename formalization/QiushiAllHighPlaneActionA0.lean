import QiushiAllHighPlaneSelectors

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionA_zero : ∀ b : Fin 512,
    ahSecValid (0 : Fin 3) b →
      (ahSecP (0 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (0 : Fin 3) b) (ahSecTranspose (0 : Fin 3) b)
          (ahSecSelA (0 : Fin 3) b) * ahSecQTInv (0 : Fin 3) b =
            codeMat (ahLineRepCode (0 : Fin 3)) := by
  decide +revert

end QiushiMatmul
