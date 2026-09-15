import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0010Refs : Fin 58 → RowRef 340 58 := ![.occ 7, .occ 15, .occ 59, .occ 60, .occ 62, .occ 63, .occ 64, .occ 76, .occ 84, .occ 86, .occ 88, .occ 98, .occ 104, .occ 105, .occ 116, .occ 121, .occ 132, .occ 142, .occ 147, .occ 148, .occ 150, .occ 152, .occ 155, .occ 205, .occ 208, .occ 238, .occ 252, .occ 278, .occ 281, .occ 285, .occ 287, .occ 295, .occ 311, .occ 312, .occ 324, .occ 325, .occ 334, .occ 335, .occ 339, .sumGe, .nonneg 6, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 18, .nonneg 19, .nonneg 23, .nonneg 24, .nonneg 28, .nonneg 32, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchLe 4 (0), .branchGe 10 (1), .branchGe 20 (1), .branchGe 57 (1)]

def plane426GenLeaf0010Mult : Fin 58 → Nat := ![17, 6, 1397, 763, 1455, 1842, 767, 713, 763, 1478, 258, 538, 83, 131, 532, 347, 629, 1197, 715, 123, 386, 208, 1700, 169, 440, 1553, 350, 108, 342, 351, 664, 593, 570, 318, 402, 191, 522, 250, 65, 2934, 1197, 596, 2168, 4844, 142, 1636, 2976, 638, 2443, 963, 1326, 2341, 1801, 2091, 2162, 2234, 2256, 9910]

theorem plane426GenLeaf0010 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_57 : (1 : Int) ≤ x 57)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0010Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0010Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 15
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 76
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 238
  · exact hroot.hOcc 252
  · exact hroot.hOcc 278
  · exact hroot.hOcc 281
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 295
  · exact hroot.hOcc 311
  · exact hroot.hOcc 312
  · exact hroot.hOcc 324
  · exact hroot.hOcc 325
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · exact hroot.hOcc 339
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (10 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (57 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_57

end QiushiMatmul
