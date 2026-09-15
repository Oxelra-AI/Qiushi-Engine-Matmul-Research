import QiushiAllHighPlaneActionA1

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionA_two_a : ∀ b : Fin 512, b.val < 128 →
    ahSecValid (2 : Fin 3) b →
      (ahSecP (2 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (2 : Fin 3) b) (ahSecTranspose (2 : Fin 3) b)
          (ahSecSelA (2 : Fin 3) b) * ahSecQTInv (2 : Fin 3) b =
            codeMat (ahLineRepCode (2 : Fin 3)) := by
  decide +revert

end QiushiMatmul
