import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0015Refs : Fin 64 → RowRef 304 63 := ![.occ 0, .occ 7, .occ 9, .occ 18, .occ 26, .occ 34, .occ 36, .occ 50, .occ 52, .occ 58, .occ 60, .occ 64, .occ 69, .occ 85, .occ 87, .occ 95, .occ 96, .occ 103, .occ 119, .occ 144, .occ 153, .occ 156, .occ 159, .occ 177, .occ 192, .occ 201, .occ 202, .occ 210, .occ 211, .occ 212, .occ 215, .occ 225, .occ 231, .occ 236, .occ 243, .occ 251, .occ 258, .occ 259, .occ 264, .occ 271, .occ 272, .sumGe, .nonneg 17, .nonneg 22, .nonneg 26, .nonneg 27, .nonneg 32, .nonneg 35, .nonneg 41, .nonneg 44, .nonneg 49, .nonneg 50, .nonneg 52, .nonneg 55, .nonneg 56, .nonneg 59, .nonneg 62, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchGe 16 (1), .branchLe 11 (0), .branchGe 33 (1)]

def plane471GenLeaf0015Mult : Fin 64 → Nat := ![9, 406, 3, 424, 99, 286, 105, 70, 696, 376, 184, 156, 41, 148, 172, 2, 481, 283, 759, 9, 2, 8, 174, 19, 85, 303, 173, 35, 92, 9, 428, 221, 183, 446, 129, 52, 155, 128, 173, 612, 9, 932, 93, 19, 316, 141, 21, 991, 308, 378, 314, 1165, 400, 277, 511, 284, 390, 452, 820, 133, 932, 3387, 226, 2851]

theorem plane471GenLeaf0015 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0015Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0015Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 18
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 103
  · exact hroot.hOcc 119
  · exact hroot.hOcc 144
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 177
  · exact hroot.hOcc 192
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 215
  · exact hroot.hOcc 225
  · exact hroot.hOcc 231
  · exact hroot.hOcc 236
  · exact hroot.hOcc 243
  · exact hroot.hOcc 251
  · exact hroot.hOcc 258
  · exact hroot.hOcc 259
  · exact hroot.hOcc 264
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (11 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (33 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
