import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0001Refs : Fin 42 → RowRef 262 41 := ![.occ 90, .occ 91, .occ 116, .occ 123, .occ 127, .occ 129, .occ 130, .occ 139, .occ 140, .occ 146, .occ 154, .occ 158, .occ 159, .occ 161, .occ 166, .occ 168, .occ 178, .occ 179, .occ 180, .occ 181, .occ 184, .occ 187, .occ 198, .occ 215, .occ 219, .occ 222, .occ 226, .occ 231, .occ 232, .occ 235, .occ 238, .occ 249, .occ 254, .occ 260, .sumGe, .nonneg 0, .nonneg 7, .nonneg 11, .branchLe 22 (0), .branchLe 21 (0), .branchLe 18 (0), .branchGe 31 (1)]

def plane486GenLeaf0001Mult : Fin 42 → Nat := ![31769, 24495, 27666, 37498, 32675, 49744, 924, 12021, 14703, 22643, 16805, 3903, 14229, 24934, 66088, 26522, 24923, 12445, 14303, 41034, 32339, 7500, 18840, 17242, 6956, 8694, 5002, 4888, 33712, 19989, 2316, 7207, 8360, 12920, 125044, 140185, 29534, 19602, 70271, 94657, 85578, 204130]

theorem plane486GenLeaf0001 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0001Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0001Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 116
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 168
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 198
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 249
  · exact hroot.hOcc 254
  · exact hroot.hOcc 260
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
