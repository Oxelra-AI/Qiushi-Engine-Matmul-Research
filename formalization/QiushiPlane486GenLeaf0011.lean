import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0011Refs : Fin 42 → RowRef 262 41 := ![.occ 103, .occ 104, .occ 105, .occ 106, .occ 114, .occ 115, .occ 118, .occ 119, .occ 121, .occ 127, .occ 129, .occ 136, .occ 139, .occ 144, .occ 145, .occ 146, .occ 154, .occ 163, .occ 165, .occ 166, .occ 169, .occ 178, .occ 179, .occ 180, .occ 186, .occ 202, .occ 222, .occ 223, .occ 227, .occ 232, .occ 237, .occ 240, .occ 247, .occ 255, .occ 259, .sumGe, .nonneg 0, .nonneg 31, .branchGe 22 (1), .branchLe 16 (0), .branchGe 3 (1), .branchLe 36 (0)]

def plane486GenLeaf0011Mult : Fin 42 → Nat := ![12140, 1006, 38277, 9136, 14911, 6333, 30553, 28096, 5691, 8137, 24659, 21122, 18516, 8255, 5163, 37439, 24390, 9321, 11585, 23894, 2956, 45662, 16253, 4067, 5080, 9233, 15240, 2358, 3414, 16626, 13336, 9761, 5147, 3508, 3403, 84398, 106119, 48594, 120138, 82040, 25963, 76928]

theorem plane486GenLeaf0011 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0011Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0011Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 202
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 227
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 247
  · exact hroot.hOcc 255
  · exact hroot.hOcc 259
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (31 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (3 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (36 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
