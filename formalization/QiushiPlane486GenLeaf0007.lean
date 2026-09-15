import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0007Refs : Fin 42 → RowRef 262 41 := ![.occ 90, .occ 114, .occ 116, .occ 120, .occ 121, .occ 123, .occ 127, .occ 129, .occ 133, .occ 134, .occ 135, .occ 136, .occ 146, .occ 154, .occ 156, .occ 161, .occ 167, .occ 174, .occ 175, .occ 179, .occ 180, .occ 181, .occ 189, .occ 191, .occ 211, .occ 221, .occ 226, .occ 231, .occ 235, .occ 240, .occ 242, .occ 260, .occ 261, .sumGe, .nonneg 0, .nonneg 3, .nonneg 8, .nonneg 28, .branchLe 22 (0), .branchGe 21 (1), .branchLe 17 (0), .branchGe 37 (1)]

def plane486GenLeaf0007Mult : Fin 42 → Nat := ![107084, 31210, 12066, 37408, 24092, 8098, 14266, 10342, 50170, 1204, 30776, 79190, 28093, 101595, 36464, 71322, 63958, 3456, 39728, 33708, 13030, 67382, 25004, 25657, 17416, 1720, 12514, 37618, 75026, 5868, 1701, 15990, 25327, 191809, 220420, 19466, 26824, 78684, 163716, 240524, 28654, 359896]

theorem plane486GenLeaf0007 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0007Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0007Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 211
  · exact hroot.hOcc 221
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (3 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (37 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
