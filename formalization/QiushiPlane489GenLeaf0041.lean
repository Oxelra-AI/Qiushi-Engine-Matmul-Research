import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0041Refs : Fin 31 → RowRef 371 32 := ![.occ 95, .occ 97, .occ 100, .occ 102, .occ 124, .occ 133, .occ 152, .occ 159, .occ 164, .occ 180, .occ 183, .occ 220, .occ 223, .occ 224, .occ 225, .occ 253, .occ 258, .occ 262, .occ 267, .occ 286, .occ 300, .occ 306, .occ 313, .occ 322, .occ 345, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchGe 30 (1), .branchLe 22 (0), .branchGe 0 (2)]

def plane489GenLeaf0041Mult : Fin 31 → Nat := ![5, 1, 1, 3, 1, 7, 3, 4, 2, 1, 1, 1, 1, 7, 5, 3, 1, 2, 2, 3, 5, 1, 4, 1, 4, 9, 11, 30, 26, 6, 29]

theorem plane489GenLeaf0041 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_0 : (2 : Int) ≤ x 0)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0041Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0041Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 124
  · exact hroot.hOcc 133
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 180
  · exact hroot.hOcc 183
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 253
  · exact hroot.hOcc 258
  · exact hroot.hOcc 262
  · exact hroot.hOcc 267
  · exact hroot.hOcc 286
  · exact hroot.hOcc 300
  · exact hroot.hOcc 306
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 345
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
