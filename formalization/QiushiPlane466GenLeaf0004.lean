import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0004Refs : Fin 51 → RowRef 210 50 := ![.occ 31, .occ 57, .occ 62, .occ 64, .occ 75, .occ 79, .occ 83, .occ 84, .occ 87, .occ 92, .occ 95, .occ 100, .occ 101, .occ 103, .occ 108, .occ 111, .occ 113, .occ 120, .occ 123, .occ 124, .occ 132, .occ 133, .occ 150, .occ 151, .occ 156, .occ 159, .occ 165, .occ 169, .occ 172, .occ 188, .occ 194, .occ 196, .occ 198, .occ 201, .occ 202, .occ 203, .occ 204, .occ 208, .sumGe, .nonneg 0, .nonneg 14, .nonneg 33, .nonneg 35, .nonneg 37, .nonneg 43, .nonneg 46, .branchLe 24 (0), .branchGe 19 (1), .branchLe 30 (1), .branchLe 12 (0), .branchLe 21 (0)]

def plane466GenLeaf0004Mult : Fin 51 → Nat := ![42014, 413622, 450342, 359950, 598402, 436818, 62440, 258688, 337334, 490088, 263572, 826642, 285108, 1570742, 169238, 317526, 104274, 403428, 654574, 60706, 495976, 260024, 262954, 122490, 433022, 673708, 446888, 90526, 545292, 449202, 1894, 475936, 13513, 150357, 526637, 208982, 190189, 88230, 2547592, 1136496, 167080, 778828, 279500, 657874, 657946, 385944, 1846952, 3017616, 1096596, 2174254, 1947022]

theorem plane466GenLeaf0004 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (1 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0004Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0004Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 31
  · exact hroot.hOcc 57
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 165
  · exact hroot.hOcc 169
  · exact hroot.hOcc 172
  · exact hroot.hOcc 188
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 208
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (12 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (21 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
