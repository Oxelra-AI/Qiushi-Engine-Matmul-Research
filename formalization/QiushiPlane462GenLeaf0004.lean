import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0004Refs : Fin 62 → RowRef 294 62 := ![.occ 14, .occ 47, .occ 48, .occ 49, .occ 62, .occ 65, .occ 68, .occ 71, .occ 73, .occ 76, .occ 77, .occ 78, .occ 80, .occ 83, .occ 84, .occ 86, .occ 88, .occ 89, .occ 91, .occ 94, .occ 99, .occ 100, .occ 102, .occ 103, .occ 105, .occ 109, .occ 118, .occ 143, .occ 160, .occ 174, .occ 183, .occ 185, .occ 193, .occ 208, .occ 209, .occ 211, .occ 213, .occ 228, .occ 236, .occ 253, .occ 260, .occ 261, .occ 268, .occ 279, .occ 285, .occ 292, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 13, .nonneg 38, .nonneg 41, .nonneg 47, .nonneg 48, .nonneg 51, .nonneg 54, .nonneg 57, .nonneg 59, .nonneg 61, .branchLe 3 (0), .branchGe 34 (2)]

def plane462GenLeaf0004Mult : Fin 62 → Nat := ![7016, 1636, 5456, 9492, 15752, 3816, 5180, 2964, 3582, 7838, 3508, 2642, 11110, 3816, 7498, 2778, 2555, 2881, 3408, 7704, 648, 2728, 6133, 5267, 3000, 5692, 206, 2044, 2522, 3000, 684, 1090, 1978, 1472, 5154, 136, 2028, 2028, 3858, 40, 4294, 1774, 2618, 3296, 5476, 4730, 25024, 17304, 31416, 31416, 2768, 15816, 28736, 8654, 12266, 11656, 5662, 1090, 2112, 13904, 25024, 66376]

theorem plane462GenLeaf0004 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_34 : (2 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0004Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0004Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 143
  · exact hroot.hOcc 160
  · exact hroot.hOcc 174
  · exact hroot.hOcc 183
  · exact hroot.hOcc 185
  · exact hroot.hOcc 193
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 211
  · exact hroot.hOcc 213
  · exact hroot.hOcc 228
  · exact hroot.hOcc 236
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 268
  · exact hroot.hOcc 279
  · exact hroot.hOcc 285
  · exact hroot.hOcc 292
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (3 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
