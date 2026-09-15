import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0013Refs : Fin 34 → RowRef 262 41 := ![.occ 87, .occ 90, .occ 91, .occ 105, .occ 111, .occ 116, .occ 119, .occ 146, .occ 149, .occ 150, .occ 154, .occ 160, .occ 161, .occ 162, .occ 166, .occ 178, .occ 181, .occ 200, .occ 204, .occ 207, .occ 213, .occ 220, .occ 223, .occ 231, .occ 236, .occ 237, .occ 239, .occ 258, .occ 259, .sumGe, .nonneg 0, .nonneg 27, .branchGe 22 (1), .branchGe 16 (1)]

def plane486GenLeaf0013Mult : Fin 34 → Nat := ![11, 2, 3, 2, 2, 8, 8, 9, 3, 3, 1, 3, 9, 3, 1, 8, 8, 4, 2, 2, 2, 2, 11, 1, 1, 1, 1, 2, 2, 19, 21, 3, 37, 37]

theorem plane486GenLeaf0013 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_22 : (1 : Int) ≤ x 22)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0013Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0013Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 154
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 166
  · exact hroot.hOcc 178
  · exact hroot.hOcc 181
  · exact hroot.hOcc 200
  · exact hroot.hOcc 204
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 258
  · exact hroot.hOcc 259
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
