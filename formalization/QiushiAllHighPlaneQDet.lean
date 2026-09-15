import QiushiAllHighPlanePDet

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecQ_det_all : ∀ k : Fin 3, ∀ b : Fin 512,
    (ahSecQ k b).det ≠ 0 := by
  have h : ahSecQTable.toList.all (fun x => decide ((codeMat x).det ≠ 0)) = true := by
    decide
  intro k b
  exact of_decide_eq_true (List.all_eq_true.mp h _
    (Vector.mem_toList_iff.mpr (Vector.getElem_mem (ahPairIndex k b).isLt)))

lemma ahSecP_isUnitDet (k : Fin 3) (b : Fin 512) : IsUnit (ahSecP k b).det :=
  isUnit_iff_ne_zero.mpr (ahSecP_det_all k b)

lemma ahSecQ_isUnitDet (k : Fin 3) (b : Fin 512) : IsUnit (ahSecQ k b).det :=
  isUnit_iff_ne_zero.mpr (ahSecQ_det_all k b)

end QiushiMatmul
