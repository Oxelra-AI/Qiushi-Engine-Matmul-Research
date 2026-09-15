import QiushiAllHighPlaneQInv

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionB_one_d : ∀ b : Fin 512, 384 ≤ b.val →
    ahSecValid (1 : Fin 3) b →
      (ahSecP (1 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (1 : Fin 3) b) (ahSecTranspose (1 : Fin 3) b)
          (ahSecSelB (1 : Fin 3) b) * ahSecQTInv (1 : Fin 3) b = codeMat b.val := by
  decide +revert +kernel

end QiushiMatmul
