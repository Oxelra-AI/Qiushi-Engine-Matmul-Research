import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0017Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 16, .occ 18, .occ 32, .occ 36, .occ 39, .occ 61, .occ 71, .occ 74, .occ 76, .occ 86, .occ 88, .occ 89, .occ 104, .occ 109, .occ 116, .occ 124, .occ 142, .occ 166, .occ 177, .occ 180, .occ 229, .occ 247, .occ 248, .occ 252, .occ 253, .occ 265, .occ 269, .occ 280, .occ 282, .occ 284, .occ 286, .occ 312, .occ 321, .occ 323, .occ 333, .occ 335, .sumGe, .nonneg 6, .nonneg 11, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 24, .nonneg 25, .nonneg 26, .nonneg 27, .nonneg 28, .nonneg 33, .nonneg 36, .nonneg 40, .nonneg 47, .nonneg 53, .nonneg 55, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchGe 35 (1), .branchGe 13 (1)]

def plane426GenLeaf0017Mult : Fin 59 → Nat := ![44, 94, 132, 130, 54, 136, 66, 194, 50, 58, 164, 68, 12, 108, 70, 24, 236, 90, 224, 82, 234, 22, 114, 49, 17, 14, 33, 45, 52, 14, 90, 59, 66, 70, 45, 166, 158, 484, 170, 16, 90, 514, 412, 2, 72, 508, 2, 216, 48, 212, 554, 74, 76, 48, 320, 414, 390, 1128, 1244]

theorem plane426GenLeaf0017 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0017Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0017Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 16
  · exact hroot.hOcc 18
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 61
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 142
  · exact hroot.hOcc 166
  · exact hroot.hOcc 177
  · exact hroot.hOcc 180
  · exact hroot.hOcc 229
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 252
  · exact hroot.hOcc 253
  · exact hroot.hOcc 265
  · exact hroot.hOcc 269
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 284
  · exact hroot.hOcc 286
  · exact hroot.hOcc 312
  · exact hroot.hOcc 321
  · exact hroot.hOcc 323
  · exact hroot.hOcc 333
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (11 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (53 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
