import QiushiAllHighPlaneActionB1a
import QiushiAllHighPlaneActionB1b
import QiushiAllHighPlaneActionB1c
import QiushiAllHighPlaneActionB1d

open Matrix BigOperators
namespace QiushiMatmul

theorem ahSecActionB_one (b : Fin 512) (hv : ahSecValid (1 : Fin 3) b) :
    (ahSecP (1 : Fin 3) b).transpose *
      ahSourcePick (ahSecPlane (1 : Fin 3) b) (ahSecTranspose (1 : Fin 3) b)
        (ahSecSelB (1 : Fin 3) b) * ahSecQTInv (1 : Fin 3) b = codeMat b.val := by
  by_cases h128 : b.val < 128
  · exact ahSecActionB_one_a b h128 hv
  by_cases h256 : b.val < 256
  · exact ahSecActionB_one_b b (by omega) h256 hv
  by_cases h384 : b.val < 384
  · exact ahSecActionB_one_c b (by omega) h384 hv
  · exact ahSecActionB_one_d b (by omega) hv

end QiushiMatmul
