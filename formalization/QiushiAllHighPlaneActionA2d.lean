import QiushiAllHighPlaneQInv

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionA_two_d : ∀ b : Fin 512, 384 ≤ b.val →
    ahSecValid (2 : Fin 3) b →
      (ahSecP (2 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (2 : Fin 3) b) (ahSecTranspose (2 : Fin 3) b)
          (ahSecSelA (2 : Fin 3) b) * ahSecQTInv (2 : Fin 3) b =
            codeMat (ahLineRepCode (2 : Fin 3)) := by
  decide +revert +kernel

end QiushiMatmul
