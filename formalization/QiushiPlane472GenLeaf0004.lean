import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0004Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 4, .occ 5, .occ 15, .occ 29, .occ 59, .occ 60, .occ 64, .occ 65, .occ 75, .occ 76, .occ 82, .occ 88, .occ 94, .occ 99, .occ 102, .occ 103, .occ 113, .occ 115, .occ 126, .occ 130, .occ 136, .occ 139, .occ 145, .occ 172, .occ 175, .occ 176, .occ 177, .occ 178, .occ 185, .occ 201, .occ 203, .occ 204, .occ 212, .occ 217, .occ 220, .occ 222, .occ 224, .occ 227, .occ 228, .occ 229, .occ 234, .occ 235, .occ 236, .sumGe, .nonneg 6, .nonneg 10, .nonneg 16, .nonneg 22, .nonneg 27, .nonneg 30, .nonneg 36, .nonneg 40, .nonneg 49, .nonneg 55, .nonneg 61, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchGe 11 (1), .branchLe 28 (0), .branchGe 17 (1), .branchLe 26 (0)]

def plane472GenLeaf0004Mult : Fin 63 → Nat := ![561008, 674208, 850488, 44120, 653000, 1582448, 72040, 1281840, 899224, 651444, 1736856, 61276, 1568228, 3044252, 224060, 1685264, 87696, 154100, 2296, 1236312, 150312, 106070, 364248, 311610, 465190, 1020480, 1293804, 1497572, 536298, 375566, 682880, 378546, 98168, 65654, 745068, 857262, 230212, 533964, 772447, 1560191, 345752, 1387798, 1235081, 672931, 6830200, 80088, 1456928, 245456, 1278968, 632208, 217296, 2876008, 661296, 775568, 117624, 1868248, 5033096, 5566728, 4034928, 3493776, 3306128, 6218056, 3651272]

theorem plane472GenLeaf0004 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0004Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0004Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 15
  · exact hroot.hOcc 29
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 82
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 172
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 185
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 212
  · exact hroot.hOcc 217
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (26 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
