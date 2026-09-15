import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0003Refs : Fin 63 → RowRef 294 62 := ![.occ 53, .occ 56, .occ 66, .occ 70, .occ 74, .occ 76, .occ 77, .occ 80, .occ 81, .occ 84, .occ 85, .occ 89, .occ 91, .occ 95, .occ 97, .occ 99, .occ 102, .occ 103, .occ 113, .occ 116, .occ 118, .occ 125, .occ 138, .occ 153, .occ 157, .occ 165, .occ 172, .occ 176, .occ 184, .occ 189, .occ 192, .occ 193, .occ 195, .occ 196, .occ 200, .occ 211, .occ 213, .occ 218, .occ 241, .occ 243, .occ 244, .occ 258, .occ 263, .occ 264, .occ 275, .occ 278, .occ 279, .occ 281, .occ 288, .sumGe, .nonneg 7, .nonneg 12, .nonneg 13, .nonneg 30, .nonneg 31, .nonneg 47, .nonneg 50, .nonneg 52, .nonneg 58, .branchLe 3 (0), .branchLe 34 (1), .branchGe 28 (1), .branchGe 43 (1)]

def plane462GenLeaf0003Mult : Fin 63 → Nat := ![44, 932, 562, 682, 90, 104, 422, 24, 6, 268, 242, 30, 446, 26, 60, 338, 48, 42, 136, 42, 330, 6, 154, 326, 107, 24, 118, 160, 12, 30, 170, 236, 154, 44, 52, 20, 648, 16, 594, 234, 12, 183, 163, 483, 42, 246, 344, 458, 374, 2184, 712, 12, 472, 856, 604, 12, 12, 108, 144, 2184, 964, 228, 5580]

theorem plane462GenLeaf0003 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0003Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0003Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 125
  · exact hroot.hOcc 138
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 165
  · exact hroot.hOcc 172
  · exact hroot.hOcc 176
  · exact hroot.hOcc 184
  · exact hroot.hOcc 189
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 211
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 241
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 258
  · exact hroot.hOcc 263
  · exact hroot.hOcc 264
  · exact hroot.hOcc 275
  · exact hroot.hOcc 278
  · exact hroot.hOcc 279
  · exact hroot.hOcc 281
  · exact hroot.hOcc 288
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (58 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (3 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (43 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
