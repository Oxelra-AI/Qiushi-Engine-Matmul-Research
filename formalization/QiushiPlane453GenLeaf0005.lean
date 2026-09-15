import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0005Refs : Fin 51 → RowRef 210 50 := ![.occ 13, .occ 17, .occ 19, .occ 23, .occ 29, .occ 38, .occ 50, .occ 51, .occ 52, .occ 56, .occ 57, .occ 67, .occ 68, .occ 70, .occ 81, .occ 85, .occ 94, .occ 103, .occ 104, .occ 105, .occ 106, .occ 108, .occ 119, .occ 133, .occ 139, .occ 147, .occ 151, .occ 154, .occ 157, .occ 166, .occ 167, .occ 171, .occ 174, .occ 175, .occ 178, .occ 188, .occ 189, .occ 193, .occ 197, .sumGe, .nonneg 0, .nonneg 2, .nonneg 22, .nonneg 24, .nonneg 31, .nonneg 39, .nonneg 47, .branchLe 35 (0), .branchLe 5 (1), .branchGe 15 (1), .branchGe 1 (1)]

def plane453GenLeaf0005Mult : Fin 51 → Nat := ![6190, 4971, 956, 976, 201, 6857, 874, 55, 2980, 5283, 2758, 4188, 2588, 3587, 1006, 624, 299, 1625, 2106, 1939, 1907, 587, 132, 637, 1315, 2723, 1901, 2518, 1173, 2587, 776, 378, 314, 447, 212, 1243, 81, 443, 126, 7559, 3812, 2804, 3933, 437, 1278, 3803, 1051, 5400, 7559, 13449, 26483]

theorem plane453GenLeaf0005 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0005Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0005Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 29
  · exact hroot.hOcc 38
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 119
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
