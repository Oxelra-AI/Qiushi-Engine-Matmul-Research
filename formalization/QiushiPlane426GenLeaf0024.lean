import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0024Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 55, .occ 56, .occ 58, .occ 60, .occ 63, .occ 69, .occ 71, .occ 76, .occ 81, .occ 88, .occ 102, .occ 103, .occ 104, .occ 109, .occ 113, .occ 116, .occ 117, .occ 122, .occ 125, .occ 132, .occ 142, .occ 144, .occ 164, .occ 176, .occ 185, .occ 192, .occ 193, .occ 194, .occ 197, .occ 202, .occ 237, .occ 258, .occ 265, .occ 266, .occ 275, .occ 294, .occ 295, .occ 316, .occ 325, .occ 331, .sumGe, .nonneg 16, .nonneg 17, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 29, .nonneg 30, .nonneg 33, .nonneg 36, .nonneg 41, .nonneg 44, .nonneg 47, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchGe 56 (1)]

def plane426GenLeaf0024Mult : Fin 59 → Nat := ![4262, 5839, 4584, 10603, 1725, 415, 859, 1373, 2803, 2831, 1324, 585, 148, 2383, 2070, 5318, 1323, 1989, 4873, 735, 3081, 9861, 4448, 642, 314, 862, 5729, 4352, 2021, 3439, 514, 585, 316, 1158, 4447, 1236, 4055, 2649, 2893, 1056, 148, 11650, 8741, 27264, 4232, 257, 1061, 591, 4557, 1053, 8955, 88, 1314, 5192, 1661, 15934, 9001, 4522, 56314]

theorem plane426GenLeaf0024 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_56 : (1 : Int) ≤ x 56)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0024Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0024Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 164
  · exact hroot.hOcc 176
  · exact hroot.hOcc 185
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 237
  · exact hroot.hOcc 258
  · exact hroot.hOcc 265
  · exact hroot.hOcc 266
  · exact hroot.hOcc 275
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 316
  · exact hroot.hOcc 325
  · exact hroot.hOcc 331
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_56

end QiushiMatmul
