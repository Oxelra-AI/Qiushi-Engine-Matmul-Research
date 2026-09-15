import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0488Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 133, .occ 142, .occ 175, .occ 290, .occ 537, .occ 539, .occ 575, .occ 858, .occ 1067, .occ 1143, .occ 1145, .occ 1191, .occ 1200, .occ 1216, .occ 1249, .occ 1280, .occ 1330, .occ 1385, .occ 1401, .occ 1431, .occ 1458, .occ 1459, .occ 1483, .occ 1491, .occ 1564, .occ 1567, .occ 1608, .occ 1629, .sumGe, .nonneg 16, .nonneg 18, .nonneg 21, .nonneg 24, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchGe 25 (1), .branchGe 2 (1)]

def plane484GenLeaf0488Mult : Fin 43 → Nat := ![748, 663, 1802, 2439, 119, 226, 570, 32, 218, 2439, 220, 714, 340, 205, 354, 683, 603, 73, 143, 269, 145, 79, 110, 300, 354, 884, 382, 205, 71, 227, 2439, 410, 708, 6382, 1938, 754, 7122, 2012, 2368, 1099, 410, 10272, 4467]

theorem plane484GenLeaf0488 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0488Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0488Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0488Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0488Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 290
  · exact hroot.hOcc 537
  · exact hroot.hOcc 539
  · exact hroot.hOcc 575
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1067
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1629
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
