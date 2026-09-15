import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0005Refs : Fin 42 → RowRef 262 41 := ![.occ 86, .occ 90, .occ 93, .occ 94, .occ 98, .occ 102, .occ 105, .occ 113, .occ 114, .occ 121, .occ 123, .occ 124, .occ 127, .occ 131, .occ 133, .occ 135, .occ 136, .occ 142, .occ 151, .occ 158, .occ 161, .occ 166, .occ 171, .occ 179, .occ 180, .occ 191, .occ 217, .occ 221, .occ 226, .occ 231, .occ 238, .occ 239, .occ 248, .occ 252, .sumGe, .nonneg 0, .branchLe 22 (0), .branchGe 21 (1), .branchLe 17 (0), .branchLe 37 (0), .branchGe 4 (1), .branchLe 10 (0)]

def plane486GenLeaf0005Mult : Fin 42 → Nat := ![2229, 1923, 3649, 307, 437, 6258, 12093, 865, 5772, 3245, 3357, 1341, 5835, 3583, 3047, 3286, 4102, 3896, 1550, 205, 3349, 6684, 4507, 6228, 1698, 2879, 87, 2107, 1235, 63, 2886, 2556, 802, 2492, 16270, 19893, 16270, 9270, 13770, 10061, 8722, 14233]

theorem plane486GenLeaf0005 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0005Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0005Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 142
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 171
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 191
  · exact hroot.hOcc 217
  · exact hroot.hOcc 221
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 248
  · exact hroot.hOcc 252
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (10 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
