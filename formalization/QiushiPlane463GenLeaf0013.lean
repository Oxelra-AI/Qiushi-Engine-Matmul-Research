import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0013Refs : Fin 63 → RowRef 278 63 := ![.occ 0, .occ 1, .occ 2, .occ 10, .occ 11, .occ 15, .occ 16, .occ 40, .occ 46, .occ 54, .occ 74, .occ 79, .occ 80, .occ 82, .occ 85, .occ 86, .occ 87, .occ 89, .occ 92, .occ 106, .occ 108, .occ 136, .occ 144, .occ 167, .occ 173, .occ 174, .occ 197, .occ 202, .occ 203, .occ 209, .occ 210, .occ 222, .occ 225, .occ 228, .occ 231, .occ 246, .occ 261, .occ 267, .occ 268, .occ 269, .occ 270, .occ 273, .occ 274, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 12, .nonneg 13, .nonneg 14, .nonneg 37, .nonneg 38, .nonneg 39, .nonneg 40, .nonneg 43, .nonneg 44, .nonneg 52, .nonneg 54, .nonneg 57, .nonneg 59, .nonneg 61, .branchGe 15 (1), .branchGe 23 (1)]

def plane463GenLeaf0013Mult : Fin 63 → Nat := ![1052, 1324, 176, 1196, 780, 504, 344, 492, 1256, 492, 840, 252, 16, 52, 16, 20, 292, 196, 448, 500, 352, 516, 352, 504, 264, 80, 238, 120, 516, 74, 2, 302, 314, 684, 314, 302, 446, 189, 165, 223, 207, 84, 124, 1796, 1376, 1008, 440, 264, 440, 264, 180, 164, 160, 144, 1208, 792, 1408, 252, 16, 2000, 92, 6108, 5980]

theorem plane463GenLeaf0013 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0013Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0013Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 40
  · exact hroot.hOcc 46
  · exact hroot.hOcc 54
  · exact hroot.hOcc 74
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 136
  · exact hroot.hOcc 144
  · exact hroot.hOcc 167
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · exact hroot.hOcc 222
  · exact hroot.hOcc 225
  · exact hroot.hOcc 228
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 261
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 269
  · exact hroot.hOcc 270
  · exact hroot.hOcc 273
  · exact hroot.hOcc 274
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (23 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
