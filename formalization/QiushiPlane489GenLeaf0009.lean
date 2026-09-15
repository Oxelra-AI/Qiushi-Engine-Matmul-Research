import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0009Refs : Fin 30 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 102, .occ 107, .occ 118, .occ 135, .occ 197, .occ 202, .occ 206, .occ 208, .occ 229, .occ 276, .occ 296, .occ 306, .occ 308, .occ 312, .occ 321, .occ 322, .occ 338, .occ 340, .occ 350, .occ 364, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 4 (0), .branchGe 12 (1), .branchGe 18 (1)]

def plane489GenLeaf0009Mult : Fin 30 → Nat := ![4, 22, 3, 1, 17, 9, 7, 8, 12, 12, 11, 2, 4, 4, 6, 10, 12, 4, 9, 9, 14, 9, 38, 34, 17, 32, 24, 12, 61, 57]

theorem plane489GenLeaf0009 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0009Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0009Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 118
  · exact hroot.hOcc 135
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 229
  · exact hroot.hOcc 276
  · exact hroot.hOcc 296
  · exact hroot.hOcc 306
  · exact hroot.hOcc 308
  · exact hroot.hOcc 312
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 338
  · exact hroot.hOcc 340
  · exact hroot.hOcc 350
  · exact hroot.hOcc 364
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (18 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
