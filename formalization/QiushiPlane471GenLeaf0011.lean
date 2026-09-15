import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0011Refs : Fin 64 → RowRef 304 63 := ![.occ 12, .occ 13, .occ 17, .occ 28, .occ 31, .occ 40, .occ 51, .occ 60, .occ 65, .occ 85, .occ 91, .occ 92, .occ 93, .occ 95, .occ 96, .occ 98, .occ 116, .occ 119, .occ 130, .occ 141, .occ 145, .occ 151, .occ 187, .occ 192, .occ 196, .occ 212, .occ 221, .occ 223, .occ 224, .occ 225, .occ 232, .occ 241, .occ 246, .occ 259, .occ 267, .occ 272, .occ 274, .occ 290, .occ 292, .occ 296, .occ 297, .sumGe, .nonneg 10, .nonneg 13, .nonneg 18, .nonneg 24, .nonneg 26, .nonneg 27, .nonneg 30, .nonneg 34, .nonneg 35, .nonneg 42, .nonneg 51, .nonneg 52, .nonneg 55, .nonneg 59, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchLe 16 (0), .branchLe 25 (0), .branchLe 22 (0), .branchGe 38 (1)]

def plane471GenLeaf0011Mult : Fin 64 → Nat := ![3053, 3452, 3402, 2051, 515, 6354, 876, 1066, 296, 1179, 569, 940, 1955, 531, 3878, 1106, 5577, 205, 779, 874, 982, 659, 1213, 2495, 1718, 889, 147, 370, 214, 2071, 725, 1285, 621, 2005, 1255, 1130, 1304, 920, 546, 1777, 719, 7903, 1041, 874, 5764, 2466, 4499, 44, 766, 4062, 2793, 5435, 2003, 4106, 388, 1723, 7357, 5552, 2169, 7357, 7184, 7143, 4733, 27973]

theorem plane471GenLeaf0011 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0011Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0011Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 17
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 40
  · exact hroot.hOcc 51
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · exact hroot.hOcc 85
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 196
  · exact hroot.hOcc 212
  · exact hroot.hOcc 221
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 232
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · exact hroot.hOcc 259
  · exact hroot.hOcc 267
  · exact hroot.hOcc 272
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 292
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
