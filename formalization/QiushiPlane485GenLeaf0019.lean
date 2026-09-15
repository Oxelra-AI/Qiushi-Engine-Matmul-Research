import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0019Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 93, .occ 96, .occ 135, .occ 136, .occ 137, .occ 140, .occ 151, .occ 152, .occ 154, .occ 178, .occ 179, .occ 181, .occ 184, .occ 192, .occ 207, .occ 219, .occ 222, .occ 233, .occ 238, .occ 246, .occ 252, .occ 263, .occ 265, .occ 302, .occ 353, .occ 358, .occ 359, .occ 362, .occ 371, .occ 394, .occ 396, .occ 397, .sumGe, .nonneg 0, .nonneg 12, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchGe 13 (1), .branchGe 1 (1)]

def plane485GenLeaf0019Mult : Fin 42 → Nat := ![1317, 5435, 2667, 1091, 2594, 2042, 1773, 710, 788, 2266, 231, 237, 575, 5617, 259, 5348, 2648, 1147, 2219, 1276, 2327, 3559, 2080, 263, 110, 269, 450, 155, 418, 424, 903, 886, 297, 6145, 7016, 1406, 4638, 222, 17634, 713, 23619, 9117]

theorem plane485GenLeaf0019 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0019Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0019Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 192
  · exact hroot.hOcc 207
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 252
  · exact hroot.hOcc 263
  · exact hroot.hOcc 265
  · exact hroot.hOcc 302
  · exact hroot.hOcc 353
  · exact hroot.hOcc 358
  · exact hroot.hOcc 359
  · exact hroot.hOcc 362
  · exact hroot.hOcc 371
  · exact hroot.hOcc 394
  · exact hroot.hOcc 396
  · exact hroot.hOcc 397
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
