import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0004Refs : Fin 41 → RowRef 262 41 := ![.occ 89, .occ 91, .occ 102, .occ 105, .occ 108, .occ 114, .occ 116, .occ 119, .occ 121, .occ 128, .occ 141, .occ 146, .occ 152, .occ 154, .occ 161, .occ 164, .occ 166, .occ 171, .occ 174, .occ 179, .occ 180, .occ 181, .occ 201, .occ 212, .occ 216, .occ 217, .occ 222, .occ 223, .occ 231, .occ 235, .occ 239, .sumGe, .nonneg 0, .nonneg 27, .nonneg 39, .branchLe 22 (0), .branchGe 21 (1), .branchLe 17 (0), .branchLe 37 (0), .branchLe 4 (0), .branchGe 16 (1)]

def plane486GenLeaf0004Mult : Fin 41 → Nat := ![13, 47, 42, 38, 35, 8, 54, 20, 32, 9, 15, 38, 45, 8, 32, 4, 46, 26, 32, 20, 7, 68, 14, 8, 24, 3, 25, 46, 19, 5, 38, 133, 76, 22, 11, 21, 116, 64, 19, 133, 265]

theorem plane486GenLeaf0004 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0004Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0004Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 201
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
