import QiushiAllHighPlaneActionA2a
import QiushiAllHighPlaneActionA2b
import QiushiAllHighPlaneActionA2c
import QiushiAllHighPlaneActionA2d

open Matrix BigOperators
namespace QiushiMatmul

theorem ahSecActionA_two (b : Fin 512) (hv : ahSecValid (2 : Fin 3) b) :
    (ahSecP (2 : Fin 3) b).transpose *
      ahSourcePick (ahSecPlane (2 : Fin 3) b) (ahSecTranspose (2 : Fin 3) b)
        (ahSecSelA (2 : Fin 3) b) * ahSecQTInv (2 : Fin 3) b =
          codeMat (ahLineRepCode (2 : Fin 3)) := by
  by_cases h128 : b.val < 128
  · exact ahSecActionA_two_a b h128 hv
  by_cases h256 : b.val < 256
  · exact ahSecActionA_two_b b (by omega) h256 hv
  by_cases h384 : b.val < 384
  · exact ahSecActionA_two_c b (by omega) h384 hv
  · exact ahSecActionA_two_d b (by omega) hv

end QiushiMatmul
