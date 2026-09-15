import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0016Refs : Fin 64 → RowRef 304 63 := ![.occ 3, .occ 6, .occ 7, .occ 9, .occ 39, .occ 50, .occ 51, .occ 53, .occ 69, .occ 74, .occ 82, .occ 85, .occ 93, .occ 96, .occ 103, .occ 112, .occ 118, .occ 119, .occ 120, .occ 122, .occ 141, .occ 149, .occ 154, .occ 169, .occ 185, .occ 190, .occ 192, .occ 212, .occ 213, .occ 225, .occ 236, .occ 243, .occ 248, .occ 249, .occ 259, .occ 268, .occ 271, .occ 295, .occ 296, .occ 297, .sumGe, .nonneg 17, .nonneg 18, .nonneg 21, .nonneg 24, .nonneg 26, .nonneg 27, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 36, .nonneg 39, .nonneg 44, .nonneg 47, .nonneg 49, .nonneg 55, .nonneg 59, .nonneg 61, .nonneg 62, .branchLe 48 (0), .branchGe 14 (1), .branchLe 8 (0), .branchGe 16 (1), .branchGe 11 (1)]

def plane471GenLeaf0016Mult : Fin 64 → Nat := ![2390, 1761, 2371, 487, 598, 346, 304, 617, 93, 783, 190, 1720, 2415, 706, 148, 1568, 1386, 294, 785, 196, 190, 124, 818, 1392, 1390, 1635, 1034, 668, 9, 224, 426, 589, 1019, 966, 785, 6, 155, 610, 1200, 420, 4034, 27, 1125, 144, 1784, 824, 2512, 1651, 1577, 1459, 636, 1635, 2402, 53, 3405, 622, 324, 510, 51, 3015, 2259, 4034, 6550, 14651]

theorem plane471GenLeaf0016 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0016Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0016Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 39
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 103
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 141
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 169
  · exact hroot.hOcc 185
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 225
  · exact hroot.hOcc 236
  · exact hroot.hOcc 243
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · exact hroot.hOcc 259
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
