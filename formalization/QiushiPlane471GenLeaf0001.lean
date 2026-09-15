import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0001Refs : Fin 64 → RowRef 304 63 := ![.occ 17, .occ 20, .occ 29, .occ 36, .occ 37, .occ 45, .occ 50, .occ 51, .occ 57, .occ 58, .occ 61, .occ 73, .occ 82, .occ 83, .occ 85, .occ 93, .occ 97, .occ 108, .occ 109, .occ 118, .occ 119, .occ 133, .occ 159, .occ 179, .occ 182, .occ 184, .occ 187, .occ 201, .occ 204, .occ 206, .occ 208, .occ 212, .occ 213, .occ 229, .occ 242, .occ 243, .occ 254, .occ 258, .occ 264, .occ 276, .occ 279, .occ 280, .occ 284, .occ 286, .occ 290, .occ 291, .occ 302, .sumGe, .nonneg 17, .nonneg 24, .nonneg 26, .nonneg 30, .nonneg 47, .nonneg 49, .nonneg 52, .nonneg 55, .nonneg 61, .nonneg 62, .branchLe 48 (0), .branchLe 14 (0), .branchLe 38 (0), .branchLe 12 (0), .branchLe 20 (0), .branchGe 43 (1)]

def plane471GenLeaf0001Mult : Fin 64 → Nat := ![178096, 153082, 423874, 114888, 122504, 607512, 153218, 457856, 48002, 309558, 242488, 264908, 50302, 193672, 68036, 315656, 14576, 647304, 117758, 88456, 254024, 124572, 568126, 28650, 107186, 67800, 82433, 174923, 48728, 104160, 28340, 58254, 255509, 47433, 12580, 185415, 309475, 126614, 251284, 7402, 42631, 53450, 14094, 87284, 49534, 108513, 146738, 1042422, 29110, 55016, 750006, 505778, 197188, 285850, 336764, 382546, 619240, 278578, 277360, 1042422, 554024, 279960, 654320, 2472822]

theorem plane471GenLeaf0001 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0001Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0001Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 73
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 133
  · exact hroot.hOcc 159
  · exact hroot.hOcc 179
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 229
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 254
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 276
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 284
  · exact hroot.hOcc 286
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (20 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
