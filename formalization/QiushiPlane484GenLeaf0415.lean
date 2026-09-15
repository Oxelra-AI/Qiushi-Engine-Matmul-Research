import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0415Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 135, .occ 136, .occ 139, .occ 321, .occ 386, .occ 443, .occ 449, .occ 505, .occ 925, .occ 1134, .occ 1146, .occ 1164, .occ 1183, .occ 1186, .occ 1190, .occ 1215, .occ 1238, .occ 1291, .occ 1357, .occ 1462, .occ 1466, .occ 1467, .occ 1573, .occ 1587, .occ 1606, .occ 1607, .occ 1608, .occ 1628, .occ 1657, .occ 1663, .sumGe, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchLe 29 (0), .branchLe 14 (0), .branchGe 24 (1), .branchLe 34 (0)]

def plane484GenLeaf0415Mult : Fin 44 → Nat := ![5203, 18001, 20268, 11812, 19801, 5670, 18636, 1238, 18690, 8052, 9193, 12493, 7338, 1616, 5165, 20409, 425, 2114, 1616, 2091, 683, 3145, 1616, 2422, 6731, 3730, 5943, 5332, 2076, 11054, 2744, 4411, 17179, 49154, 9898, 23273, 39597, 115602, 47538, 63956, 35642, 47538, 91845, 49154]

theorem plane484GenLeaf0415 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0415Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0415Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0415Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0415Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 321
  · exact hroot.hOcc 386
  · exact hroot.hOcc 443
  · exact hroot.hOcc 449
  · exact hroot.hOcc 505
  · exact hroot.hOcc 925
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1466
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1587
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
