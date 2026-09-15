import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0006Refs : Fin 64 → RowRef 304 63 := ![.occ 11, .occ 17, .occ 31, .occ 50, .occ 61, .occ 64, .occ 69, .occ 82, .occ 83, .occ 93, .occ 96, .occ 102, .occ 109, .occ 118, .occ 119, .occ 137, .occ 139, .occ 144, .occ 147, .occ 148, .occ 150, .occ 159, .occ 162, .occ 165, .occ 168, .occ 184, .occ 185, .occ 193, .occ 197, .occ 201, .occ 202, .occ 224, .occ 225, .occ 248, .occ 254, .occ 264, .occ 266, .occ 271, .occ 284, .occ 285, .occ 286, .occ 295, .occ 300, .sumGe, .nonneg 19, .nonneg 22, .nonneg 26, .nonneg 34, .nonneg 35, .nonneg 41, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 49, .nonneg 51, .nonneg 55, .nonneg 56, .nonneg 58, .nonneg 59, .nonneg 62, .branchLe 48 (0), .branchLe 4 (0), .branchLe 38 (0), .branchGe 6 (1)]

def plane471GenLeaf0006Mult : Fin 64 → Nat := ![1188, 3395, 514, 2128, 287, 394, 782, 552, 2829, 850, 651, 2212, 1287, 922, 664, 291, 180, 246, 230, 1112, 313, 241, 432, 298, 427, 1932, 372, 498, 2101, 546, 596, 776, 148, 2140, 57, 262, 256, 394, 570, 435, 114, 482, 500, 4537, 88, 904, 307, 2131, 473, 1233, 57, 222, 1540, 1005, 1187, 1843, 619, 1376, 1900, 1931, 1110, 4105, 3923, 16111]

theorem plane471GenLeaf0006 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0006Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0006Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 17
  · exact hroot.hOcc 31
  · exact hroot.hOcc 50
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 159
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 248
  · exact hroot.hOcc 254
  · exact hroot.hOcc 264
  · exact hroot.hOcc 266
  · exact hroot.hOcc 271
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 286
  · exact hroot.hOcc 295
  · exact hroot.hOcc 300
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
