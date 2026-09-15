import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0009Refs : Fin 63 → RowRef 278 63 := ![.occ 17, .occ 19, .occ 42, .occ 51, .occ 66, .occ 67, .occ 68, .occ 69, .occ 70, .occ 96, .occ 113, .occ 114, .occ 118, .occ 127, .occ 134, .occ 138, .occ 139, .occ 140, .occ 142, .occ 143, .occ 144, .occ 170, .occ 171, .occ 173, .occ 175, .occ 186, .occ 187, .occ 188, .occ 198, .occ 218, .occ 222, .occ 224, .occ 225, .occ 226, .occ 227, .occ 236, .occ 239, .occ 240, .occ 241, .occ 244, .occ 257, .occ 258, .occ 259, .occ 262, .occ 264, .occ 268, .occ 271, .occ 272, .occ 276, .sumGe, .nonneg 0, .nonneg 12, .nonneg 14, .nonneg 37, .nonneg 38, .nonneg 39, .nonneg 40, .nonneg 42, .nonneg 57, .nonneg 59, .branchLe 15 (0), .branchLe 24 (0), .branchGe 60 (1)]

def plane463GenLeaf0009Mult : Fin 63 → Nat := ![65744, 4520, 37984, 14136, 146324, 9116, 270440, 255660, 65820, 7016, 11688, 2360, 2496, 48756, 16, 216308, 144044, 89960, 156926, 246810, 245950, 11680, 23972, 2268, 6932, 4374, 22584, 15240, 11864, 1096, 47974, 87743, 44703, 20011, 60281, 1088, 8622, 22133, 64325, 18832, 88831, 33805, 9480, 36659, 5292, 7780, 7195, 21125, 172978, 360585, 581620, 102304, 42472, 9208, 18992, 18520, 102336, 37848, 14136, 567284, 70536, 248736, 2179156]

theorem plane463GenLeaf0009 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_60 : (1 : Int) ≤ x 60)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0009Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0009Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 42
  · exact hroot.hOcc 51
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 96
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 198
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 236
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 259
  · exact hroot.hOcc 262
  · exact hroot.hOcc 264
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_60

end QiushiMatmul
