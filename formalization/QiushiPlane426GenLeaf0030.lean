import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0030Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 60, .occ 68, .occ 69, .occ 73, .occ 76, .occ 83, .occ 84, .occ 86, .occ 89, .occ 98, .occ 108, .occ 109, .occ 116, .occ 117, .occ 121, .occ 122, .occ 132, .occ 142, .occ 155, .occ 170, .occ 176, .occ 220, .occ 221, .occ 227, .occ 237, .occ 239, .occ 244, .occ 252, .occ 260, .occ 265, .occ 289, .occ 294, .occ 316, .occ 321, .occ 325, .occ 334, .sumGe, .nonneg 4, .nonneg 5, .nonneg 6, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 30, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 46, .nonneg 47, .nonneg 50, .branchLe 43 (0), .branchGe 14 (1), .branchGe 18 (1), .branchGe 49 (1), .branchGe 0 (2)]

def plane426GenLeaf0030Mult : Fin 59 → Nat := ![2992, 1592, 3620, 2730, 4085, 341, 908, 1475, 1459, 475, 3966, 2881, 1471, 3850, 676, 412, 643, 357, 542, 1304, 1422, 2016, 104, 1977, 2119, 156, 356, 2017, 357, 2172, 950, 29, 146, 183, 515, 1605, 1437, 6113, 200, 454, 4733, 3586, 4477, 1815, 125, 1201, 898, 2342, 328, 1170, 616, 728, 938, 3890, 3042, 2300, 10723, 12272, 16521]

theorem plane426GenLeaf0030 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hLB_0 : (2 : Int) ≤ x 0)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0030Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0030Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 60
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 98
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 155
  · exact hroot.hOcc 170
  · exact hroot.hOcc 176
  · exact hroot.hOcc 220
  · exact hroot.hOcc 221
  · exact hroot.hOcc 227
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 252
  · exact hroot.hOcc 260
  · exact hroot.hOcc 265
  · exact hroot.hOcc 289
  · exact hroot.hOcc 294
  · exact hroot.hOcc 316
  · exact hroot.hOcc 321
  · exact hroot.hOcc 325
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49
  · change (∑ k, (if k = (0 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
