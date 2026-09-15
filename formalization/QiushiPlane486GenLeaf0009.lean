import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0009Refs : Fin 42 → RowRef 262 41 := ![.occ 87, .occ 88, .occ 90, .occ 91, .occ 95, .occ 100, .occ 103, .occ 105, .occ 114, .occ 118, .occ 119, .occ 121, .occ 126, .occ 131, .occ 133, .occ 146, .occ 154, .occ 161, .occ 166, .occ 178, .occ 179, .occ 180, .occ 182, .occ 202, .occ 208, .occ 209, .occ 214, .occ 222, .occ 232, .occ 233, .occ 236, .occ 237, .occ 243, .occ 247, .occ 260, .sumGe, .nonneg 0, .nonneg 7, .branchGe 22 (1), .branchLe 16 (0), .branchLe 3 (0), .branchLe 10 (0)]

def plane486GenLeaf0009Mult : Fin 42 → Nat := ![1045, 352, 4583, 791, 2363, 1150, 944, 1556, 1020, 566, 2775, 950, 1248, 811, 1474, 2263, 2078, 1492, 2438, 3067, 559, 1892, 3165, 814, 315, 1244, 296, 54, 1252, 205, 579, 1068, 248, 716, 23, 6834, 5174, 406, 12602, 5342, 4991, 4571]

theorem plane486GenLeaf0009 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0009Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0009Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 182
  · exact hroot.hOcc 202
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 214
  · exact hroot.hOcc 222
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 243
  · exact hroot.hOcc 247
  · exact hroot.hOcc 260
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (3 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (10 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
