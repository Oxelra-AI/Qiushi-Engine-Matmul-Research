import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0035Refs : Fin 58 → RowRef 340 58 := ![.occ 5, .occ 6, .occ 20, .occ 21, .occ 31, .occ 41, .occ 63, .occ 71, .occ 84, .occ 88, .occ 90, .occ 93, .occ 113, .occ 117, .occ 122, .occ 124, .occ 129, .occ 133, .occ 135, .occ 138, .occ 144, .occ 149, .occ 158, .occ 159, .occ 167, .occ 169, .occ 175, .occ 188, .occ 203, .occ 207, .occ 209, .occ 235, .occ 264, .occ 268, .occ 295, .occ 299, .occ 309, .occ 316, .occ 322, .occ 323, .occ 330, .occ 333, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 33, .nonneg 46, .nonneg 50, .nonneg 55, .nonneg 56, .branchGe 43 (1), .branchGe 34 (1), .branchLe 49 (0), .branchGe 11 (1)]

def plane426GenLeaf0035Mult : Fin 58 → Nat := ![146, 36, 145, 30, 64, 12, 554, 327, 400, 66, 406, 22, 405, 17, 282, 191, 583, 366, 717, 284, 264, 77, 157, 113, 160, 408, 252, 177, 147, 6, 78, 213, 177, 266, 318, 141, 208, 12, 158, 52, 71, 136, 1001, 250, 626, 2466, 156, 136, 1138, 101, 233, 832, 349, 330, 3739, 483, 659, 3332]

theorem plane426GenLeaf0035 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0035Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0035Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 31
  · exact hroot.hOcc 41
  · exact hroot.hOcc 63
  · exact hroot.hOcc 71
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 175
  · exact hroot.hOcc 188
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · exact hroot.hOcc 235
  · exact hroot.hOcc 264
  · exact hroot.hOcc 268
  · exact hroot.hOcc 295
  · exact hroot.hOcc 299
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 322
  · exact hroot.hOcc 323
  · exact hroot.hOcc 330
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (34 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (11 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
