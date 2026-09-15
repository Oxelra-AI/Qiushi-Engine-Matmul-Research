import QiushiAllHighPlaneQInv2

open Matrix BigOperators
noncomputable section
namespace QiushiMatmul

theorem ahSecQTInv_all (k : Fin 3) (b : Fin 512) :
    (ahSecQ k b).transpose * ahSecQTInv k b = 1 := by
  fin_cases k
  · exact ahSecQTInv_zero b
  · exact ahSecQTInv_one b
  · exact ahSecQTInv_two b

lemma ahSecQ_transpose_inv (k : Fin 3) (b : Fin 512)
    [Invertible (ahSecQ k b)] : (ahSecQ k b).transpose⁻¹ = ahSecQTInv k b := by
  apply Matrix.inv_eq_right_inv
  exact ahSecQTInv_all k b

end QiushiMatmul
end
