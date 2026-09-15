import QiushiAllHighPlaneActionA

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecActionB_zero : ∀ b : Fin 512,
    ahSecValid (0 : Fin 3) b →
      (ahSecP (0 : Fin 3) b).transpose *
        ahSourcePick (ahSecPlane (0 : Fin 3) b) (ahSecTranspose (0 : Fin 3) b)
          (ahSecSelB (0 : Fin 3) b) * ahSecQTInv (0 : Fin 3) b = codeMat b.val := by
  decide +revert

end QiushiMatmul
