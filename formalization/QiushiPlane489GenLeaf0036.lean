import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0036Refs : Fin 20 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 105, .occ 131, .occ 136, .occ 137, .occ 168, .occ 189, .occ 205, .occ 210, .occ 266, .occ 280, .occ 318, .occ 336, .occ 350, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchGe 18 (1)]

def plane489GenLeaf0036Mult : Fin 20 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7, 9]

theorem plane489GenLeaf0036 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0036Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0036Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 105
  · exact hroot.hOcc 131
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 168
  · exact hroot.hOcc 189
  · exact hroot.hOcc 205
  · exact hroot.hOcc 210
  · exact hroot.hOcc 266
  · exact hroot.hOcc 280
  · exact hroot.hOcc 318
  · exact hroot.hOcc 336
  · exact hroot.hOcc 350
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
