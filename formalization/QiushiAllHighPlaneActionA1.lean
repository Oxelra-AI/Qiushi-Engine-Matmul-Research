import QiushiAllHighPlaneActionA0

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionA_one : ∀ b : Fin 512,
    ahSecValid (1 : Fin 3) b →
      (ahSecP (1 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (1 : Fin 3) b) (ahSecTranspose (1 : Fin 3) b)
          (ahSecSelA (1 : Fin 3) b) * ahSecQTInv (1 : Fin 3) b =
            codeMat (ahLineRepCode (1 : Fin 3)) := by
  decide +revert

end QiushiMatmul
