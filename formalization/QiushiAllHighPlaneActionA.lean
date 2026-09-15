import QiushiAllHighPlaneActionA2

open Matrix BigOperators
noncomputable section
namespace QiushiMatmul

theorem ahSecActionA_all (k : Fin 3) (b : Fin 512)
    (hv : ahSecValid k b) :
      (ahSecP k b).transpose *
        ahSourcePick (ahSecPlane k b) (ahSecTranspose k b) (ahSecSelA k b) *
          ahSecQTInv k b = codeMat (ahLineRepCode k) := by
  fin_cases k
  · exact ahSecActionA_zero b hv
  · exact ahSecActionA_one b hv
  · exact ahSecActionA_two b hv

lemma ahSecActionA (k : Fin 3) (b : Fin 512) [Invertible (ahSecQ k b)]
    (hv : ahSecValid k b) :
    actionA (ahSecP k b) (ahSecQ k b)
      (ahSourcePick (ahSecPlane k b) (ahSecTranspose k b) (ahSecSelA k b)) =
        codeMat (ahLineRepCode k) := by
  rw [actionA, ahSecQ_transpose_inv]
  exact ahSecActionA_all k b hv

end QiushiMatmul
end
