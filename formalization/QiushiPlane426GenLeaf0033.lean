import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0033Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 20, .occ 25, .occ 31, .occ 49, .occ 53, .occ 62, .occ 66, .occ 71, .occ 76, .occ 79, .occ 94, .occ 95, .occ 99, .occ 112, .occ 116, .occ 117, .occ 121, .occ 122, .occ 123, .occ 124, .occ 134, .occ 135, .occ 140, .occ 144, .occ 152, .occ 167, .occ 169, .occ 173, .occ 184, .occ 188, .occ 228, .occ 239, .occ 244, .occ 245, .occ 253, .occ 264, .occ 267, .occ 280, .occ 282, .occ 295, .occ 309, .occ 316, .occ 334, .sumGe, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 31, .nonneg 33, .nonneg 46, .nonneg 53, .nonneg 56, .branchGe 43 (1), .branchLe 34 (0), .branchGe 37 (1)]

def plane426GenLeaf0033Mult : Fin 59 → Nat := ![2154, 7334, 6472, 7446, 845, 2729, 5991, 1208, 243, 3262, 2646, 4792, 3901, 1958, 1463, 394, 5746, 5015, 2123, 405, 3804, 440, 8794, 1533, 1071, 1928, 3270, 1672, 1905, 675, 3355, 1287, 1583, 470, 809, 2154, 912, 3074, 1333, 92, 332, 507, 4268, 845, 10521, 454, 9825, 19137, 7950, 562, 5835, 497, 1101, 6030, 3743, 1290, 46519, 10014, 36343]

theorem plane426GenLeaf0033 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0033Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0033Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 20
  · exact hroot.hOcc 25
  · exact hroot.hOcc 31
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 62
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 152
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 173
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 228
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 245
  · exact hroot.hOcc 253
  · exact hroot.hOcc 264
  · exact hroot.hOcc 267
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 295
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (31 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (53 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (34 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
