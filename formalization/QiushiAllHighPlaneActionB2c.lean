import QiushiAllHighPlaneQInv

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionB_two_c : ∀ b : Fin 512, 256 ≤ b.val → b.val < 384 →
    ahSecValid (2 : Fin 3) b →
      (ahSecP (2 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (2 : Fin 3) b) (ahSecTranspose (2 : Fin 3) b)
          (ahSecSelB (2 : Fin 3) b) * ahSecQTInv (2 : Fin 3) b = codeMat b.val := by
  decide +revert +kernel

end QiushiMatmul
