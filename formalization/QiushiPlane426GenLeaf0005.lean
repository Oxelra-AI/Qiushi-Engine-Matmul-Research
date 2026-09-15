import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0005Refs : Fin 58 → RowRef 340 58 := ![.occ 7, .occ 9, .occ 10, .occ 15, .occ 18, .occ 75, .occ 76, .occ 80, .occ 88, .occ 99, .occ 104, .occ 117, .occ 121, .occ 122, .occ 142, .occ 147, .occ 155, .occ 156, .occ 162, .occ 163, .occ 183, .occ 184, .occ 192, .occ 194, .occ 197, .occ 200, .occ 209, .occ 212, .occ 233, .occ 238, .occ 239, .occ 250, .occ 278, .occ 280, .occ 282, .occ 290, .occ 300, .occ 308, .occ 322, .occ 323, .occ 325, .occ 328, .occ 333, .sumGe, .nonneg 1, .nonneg 6, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 23, .nonneg 28, .nonneg 33, .nonneg 42, .nonneg 47, .branchLe 43 (0), .branchLe 14 (0), .branchGe 13 (1), .branchGe 21 (1)]

def plane426GenLeaf0005Mult : Fin 58 → Nat := ![48922, 7994, 3032, 23288, 10172, 20018, 6616, 2210, 55794, 21000, 9876, 6108, 23796, 3144, 9480, 184, 5600, 5752, 10908, 508, 55144, 4244, 5092, 9152, 576, 8328, 13624, 48692, 7697, 9320, 34025, 5500, 508, 18016, 9816, 9035, 744, 2823, 168, 11413, 11094, 12358, 29397, 86352, 10252, 38610, 57940, 52264, 145164, 33428, 5184, 43740, 31900, 32096, 24144, 69150, 298286, 244894]

theorem plane426GenLeaf0005 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0005Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0005Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 142
  · exact hroot.hOcc 147
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 200
  · exact hroot.hOcc 209
  · exact hroot.hOcc 212
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 250
  · exact hroot.hOcc 278
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 290
  · exact hroot.hOcc 300
  · exact hroot.hOcc 308
  · exact hroot.hOcc 322
  · exact hroot.hOcc 323
  · exact hroot.hOcc 325
  · exact hroot.hOcc 328
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (42 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
