import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0008Refs : Fin 64 → RowRef 304 63 := ![.occ 12, .occ 13, .occ 17, .occ 28, .occ 38, .occ 40, .occ 47, .occ 50, .occ 51, .occ 59, .occ 60, .occ 65, .occ 79, .occ 91, .occ 92, .occ 93, .occ 95, .occ 96, .occ 109, .occ 116, .occ 119, .occ 126, .occ 145, .occ 157, .occ 198, .occ 201, .occ 221, .occ 224, .occ 225, .occ 227, .occ 230, .occ 237, .occ 243, .occ 256, .occ 262, .occ 271, .occ 286, .occ 287, .occ 295, .occ 296, .occ 298, .occ 299, .sumGe, .nonneg 10, .nonneg 18, .nonneg 24, .nonneg 26, .nonneg 32, .nonneg 34, .nonneg 35, .nonneg 41, .nonneg 44, .nonneg 45, .nonneg 49, .nonneg 50, .nonneg 51, .nonneg 53, .nonneg 55, .nonneg 58, .nonneg 62, .branchLe 48 (0), .branchGe 14 (1), .branchLe 4 (0), .branchGe 38 (1)]

def plane471GenLeaf0008Mult : Fin 64 → Nat := ![29022, 7218, 4866, 13224, 2406, 30030, 2152, 1036, 242, 1550, 10432, 11092, 4426, 1380, 734, 8512, 204, 17498, 8034, 16082, 7324, 4112, 20288, 9174, 6852, 8030, 8890, 3250, 9726, 6738, 3254, 944, 10716, 142, 8008, 2150, 1078, 2758, 7805, 13055, 12643, 623, 43366, 8574, 16700, 19048, 8282, 12824, 2852, 21250, 19306, 9020, 4874, 8034, 2860, 38104, 4788, 6894, 16486, 16966, 24070, 36762, 40608, 165200]

theorem plane471GenLeaf0008 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0008Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0008Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 17
  · exact hroot.hOcc 28
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · exact hroot.hOcc 79
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 145
  · exact hroot.hOcc 157
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 221
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 237
  · exact hroot.hOcc 243
  · exact hroot.hOcc 256
  · exact hroot.hOcc 262
  · exact hroot.hOcc 271
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
