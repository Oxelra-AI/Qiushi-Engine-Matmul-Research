import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0289Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 130, .occ 135, .occ 136, .occ 289, .occ 321, .occ 342, .occ 352, .occ 581, .occ 663, .occ 824, .occ 1145, .occ 1150, .occ 1160, .occ 1173, .occ 1190, .occ 1215, .occ 1220, .occ 1241, .occ 1251, .occ 1255, .occ 1437, .occ 1484, .occ 1486, .occ 1488, .occ 1492, .occ 1496, .occ 1560, .occ 1601, .occ 1638, .sumGe, .nonneg 3, .nonneg 10, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 13 (1), .branchGe 24 (1), .branchGe 4 (1)]

def plane484GenLeaf0289Mult : Fin 44 → Nat := ![3284, 2774, 1367, 2037, 2728, 973, 1495, 2094, 660, 1300, 574, 12, 16, 256, 605, 651, 8, 108, 204, 916, 916, 948, 481, 302, 116, 668, 864, 714, 225, 364, 3968, 444, 7900, 480, 542, 5622, 938, 3104, 2436, 1562, 3359, 10856, 10708, 12903]

theorem plane484GenLeaf0289 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0289Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0289Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0289Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0289Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 289
  · exact hroot.hOcc 321
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · exact hroot.hOcc 581
  · exact hroot.hOcc 663
  · exact hroot.hOcc 824
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
