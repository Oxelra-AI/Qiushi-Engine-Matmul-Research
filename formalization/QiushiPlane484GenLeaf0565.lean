import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0565Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 133, .occ 135, .occ 207, .occ 211, .occ 366, .occ 432, .occ 434, .occ 468, .occ 693, .occ 696, .occ 710, .occ 909, .occ 910, .occ 923, .occ 1130, .occ 1145, .occ 1158, .occ 1225, .occ 1229, .occ 1293, .occ 1298, .occ 1347, .occ 1350, .occ 1385, .occ 1387, .occ 1426, .occ 1430, .occ 1562, .occ 1564, .occ 1607, .occ 1657, .sumGe, .nonneg 0, .nonneg 1, .nonneg 21, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchLe 29 (0), .branchGe 3 (1)]

def plane484GenLeaf0565Mult : Fin 42 → Nat := ![639, 695, 1072, 1337, 430, 1443, 1096, 80, 139, 46, 59, 1543, 1257, 851, 1257, 16, 244, 291, 185, 395, 265, 186, 209, 147, 62, 107, 56, 59, 126, 556, 121, 23, 85, 1628, 559, 224, 4230, 4739, 6516, 11055, 1628, 5873]

theorem plane484GenLeaf0565 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0565Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0565Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0565Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0565Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 207
  · exact hroot.hOcc 211
  · exact hroot.hOcc 366
  · exact hroot.hOcc 432
  · exact hroot.hOcc 434
  · exact hroot.hOcc 468
  · exact hroot.hOcc 693
  · exact hroot.hOcc 696
  · exact hroot.hOcc 710
  · exact hroot.hOcc 909
  · exact hroot.hOcc 910
  · exact hroot.hOcc 923
  · exact hroot.hOcc 1130
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
