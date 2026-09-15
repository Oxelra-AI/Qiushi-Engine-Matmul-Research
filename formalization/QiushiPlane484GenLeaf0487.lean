import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0487Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 130, .occ 142, .occ 231, .occ 329, .occ 529, .occ 621, .occ 702, .occ 708, .occ 858, .occ 1113, .occ 1136, .occ 1179, .occ 1216, .occ 1225, .occ 1245, .occ 1249, .occ 1275, .occ 1337, .occ 1339, .occ 1340, .occ 1358, .occ 1385, .occ 1458, .occ 1491, .occ 1564, .occ 1601, .occ 1602, .occ 1608, .occ 1610, .occ 1615, .sumGe, .nonneg 16, .nonneg 21, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchGe 25 (1), .branchLe 2 (0), .branchGe 31 (1)]

def plane484GenLeaf0487Mult : Fin 43 → Nat := ![13238, 1107, 25324, 2779, 14026, 2346, 5878, 140, 4010, 17699, 1617, 5337, 8388, 3112, 5016, 3298, 6250, 859, 375, 2352, 2456, 6728, 980, 2910, 4414, 118, 3558, 856, 9331, 2288, 987, 25324, 7715, 46545, 12443, 57471, 16936, 11983, 52169, 3211, 89516, 3211, 36480]

theorem plane484GenLeaf0487 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0487Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0487Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0487Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0487Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 142
  · exact hroot.hOcc 231
  · exact hroot.hOcc 329
  · exact hroot.hOcc 529
  · exact hroot.hOcc 621
  · exact hroot.hOcc 702
  · exact hroot.hOcc 708
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
