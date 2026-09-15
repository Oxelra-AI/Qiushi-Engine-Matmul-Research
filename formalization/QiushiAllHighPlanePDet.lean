import QiushiAllHighPlaneClassifier

open Matrix BigOperators
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem ahSecP_det_all : ∀ k : Fin 3, ∀ b : Fin 512,
    (ahSecP k b).det ≠ 0 := by
  have h : ahSecPTable.toList.all (fun x => decide ((codeMat x).det ≠ 0)) = true := by
    decide
  intro k b
  exact of_decide_eq_true (List.all_eq_true.mp h _
    (Vector.mem_toList_iff.mpr (Vector.getElem_mem (ahPairIndex k b).isLt)))

end QiushiMatmul
