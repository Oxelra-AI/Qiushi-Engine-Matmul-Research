import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0014Refs : Fin 64 → RowRef 304 63 := ![.occ 0, .occ 7, .occ 9, .occ 12, .occ 17, .occ 26, .occ 28, .occ 30, .occ 31, .occ 34, .occ 39, .occ 50, .occ 51, .occ 52, .occ 69, .occ 80, .occ 81, .occ 82, .occ 83, .occ 85, .occ 96, .occ 107, .occ 114, .occ 118, .occ 119, .occ 146, .occ 184, .occ 191, .occ 212, .occ 227, .occ 240, .occ 243, .occ 257, .occ 261, .occ 265, .occ 268, .occ 290, .occ 294, .occ 295, .occ 296, .occ 297, .occ 298, .sumGe, .nonneg 3, .nonneg 18, .nonneg 21, .nonneg 26, .nonneg 27, .nonneg 30, .nonneg 36, .nonneg 37, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 49, .nonneg 52, .nonneg 55, .nonneg 56, .nonneg 59, .branchLe 48 (0), .branchLe 8 (0), .branchGe 16 (1), .branchLe 11 (0), .branchLe 33 (0)]

def plane471GenLeaf0014Mult : Fin 64 → Nat := ![711, 1312, 2074, 373, 17, 530, 38, 1096, 212, 1359, 921, 1440, 87, 642, 205, 498, 1214, 55, 268, 366, 206, 313, 46, 300, 252, 423, 112, 578, 206, 211, 127, 1313, 724, 788, 7, 530, 127, 121, 577, 127, 623, 450, 2640, 48, 833, 129, 407, 416, 6, 206, 211, 326, 1335, 1318, 139, 7, 603, 813, 1122, 2519, 1619, 11853, 1936, 1811]

theorem plane471GenLeaf0014 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0014Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0014Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 17
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 39
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 69
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 96
  · exact hroot.hOcc 107
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 146
  · exact hroot.hOcc 184
  · exact hroot.hOcc 191
  · exact hroot.hOcc 212
  · exact hroot.hOcc 227
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 257
  · exact hroot.hOcc 261
  · exact hroot.hOcc 265
  · exact hroot.hOcc 268
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · exact hroot.hOcc 298
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (36 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (11 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (33 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
