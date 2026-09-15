import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0010Refs : Fin 51 → RowRef 237 50 := ![.occ 7, .occ 9, .occ 14, .occ 20, .occ 23, .occ 27, .occ 34, .occ 40, .occ 46, .occ 47, .occ 53, .occ 59, .occ 104, .occ 119, .occ 126, .occ 128, .occ 148, .occ 149, .occ 157, .occ 166, .occ 167, .occ 168, .occ 170, .occ 173, .occ 174, .occ 187, .occ 190, .occ 191, .occ 195, .occ 198, .occ 199, .occ 203, .occ 206, .occ 207, .occ 208, .occ 209, .occ 211, .occ 212, .occ 217, .occ 235, .sumGe, .nonneg 4, .nonneg 24, .nonneg 39, .nonneg 41, .nonneg 44, .nonneg 49, .branchLe 26 (0), .branchGe 15 (1), .branchLe 35 (0), .branchLe 47 (0)]

def plane427GenLeaf0010Mult : Fin 51 → Nat := ![20307, 15875, 1637, 8964, 3806, 6028, 3518, 529, 458, 5699, 9160, 7625, 3268, 6784, 1878, 1878, 3719, 1600, 1780, 2313, 7801, 861, 2246, 73, 3334, 4909, 951, 4535, 1330, 6245, 6869, 1132, 4196, 6783, 4412, 3346, 6796, 9169, 709, 1496, 26335, 8640, 3280, 3875, 939, 2442, 11704, 16562, 44510, 19498, 22928]

theorem plane427GenLeaf0010 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0010Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0010Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 14
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 27
  · exact hroot.hOcc 34
  · exact hroot.hOcc 40
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 53
  · exact hroot.hOcc 59
  · exact hroot.hOcc 104
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 157
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 217
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (47 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47

end QiushiMatmul
