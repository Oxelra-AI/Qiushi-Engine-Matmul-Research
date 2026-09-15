import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0013Refs : Fin 64 → RowRef 304 63 := ![.occ 2, .occ 6, .occ 8, .occ 36, .occ 46, .occ 70, .occ 76, .occ 83, .occ 85, .occ 89, .occ 93, .occ 96, .occ 108, .occ 118, .occ 119, .occ 154, .occ 159, .occ 161, .occ 163, .occ 164, .occ 174, .occ 183, .occ 186, .occ 187, .occ 192, .occ 213, .occ 222, .occ 224, .occ 225, .occ 232, .occ 243, .occ 245, .occ 246, .occ 252, .occ 258, .occ 267, .occ 268, .occ 272, .occ 300, .occ 301, .sumGe, .nonneg 7, .nonneg 24, .nonneg 30, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 44, .nonneg 45, .nonneg 47, .nonneg 49, .nonneg 50, .nonneg 51, .nonneg 52, .nonneg 55, .nonneg 56, .nonneg 58, .nonneg 61, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchLe 16 (0), .branchGe 25 (1)]

def plane471GenLeaf0013Mult : Fin 64 → Nat := ![3383, 4202, 13147, 4396, 27898, 6462, 3649, 11059, 4075, 9315, 1196, 9412, 36, 29258, 1096, 14544, 170, 3370, 13582, 9865, 9501, 3537, 16830, 7603, 6337, 12128, 354, 14966, 2024, 1574, 16, 5039, 5969, 7086, 17271, 2208, 2895, 2051, 2124, 5003, 35457, 2500, 2966, 66357, 15576, 18684, 7406, 2942, 2096, 929, 15904, 6362, 6649, 6529, 13838, 22050, 6244, 2534, 28335, 11154, 87076, 35421, 13961, 163661]

theorem plane471GenLeaf0013 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0013Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0013Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 36
  · exact hroot.hOcc 46
  · exact hroot.hOcc 70
  · exact hroot.hOcc 76
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 108
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 174
  · exact hroot.hOcc 183
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 213
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 232
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 252
  · exact hroot.hOcc 258
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 300
  · exact hroot.hOcc 301
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (25 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
