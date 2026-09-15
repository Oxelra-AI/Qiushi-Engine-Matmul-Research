import QiushiAllHighPlaneActionA
import QiushiAllHighPlaneActionB0
import QiushiAllHighPlaneActionB1
import QiushiAllHighPlaneActionB2

open Matrix BigOperators
noncomputable section
namespace QiushiMatmul

theorem ahSecActionB_all (k : Fin 3) (b : Fin 512)
    (hv : ahSecValid k b) :
      (ahSecP k b).transpose *
        ahSourcePick (ahSecPlane k b) (ahSecTranspose k b) (ahSecSelB k b) *
          ahSecQTInv k b = codeMat b.val := by
  fin_cases k
  · exact ahSecActionB_zero b hv
  · exact ahSecActionB_one b hv
  · exact ahSecActionB_two b hv

lemma ahSecActionB (k : Fin 3) (b : Fin 512) [Invertible (ahSecQ k b)]
    (hv : ahSecValid k b) :
    actionA (ahSecP k b) (ahSecQ k b)
      (ahSourcePick (ahSecPlane k b) (ahSecTranspose k b) (ahSecSelB k b)) =
        codeMat b.val := by
  rw [actionA, ahSecQ_transpose_inv]
  exact ahSecActionB_all k b hv

end QiushiMatmul
end
