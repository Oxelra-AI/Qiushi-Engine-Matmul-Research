import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0249Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 123, .occ 125, .occ 126, .occ 130, .occ 136, .occ 139, .occ 179, .occ 366, .occ 526, .occ 542, .occ 655, .occ 749, .occ 858, .occ 860, .occ 1158, .occ 1170, .occ 1188, .occ 1191, .occ 1196, .occ 1208, .occ 1261, .occ 1409, .occ 1477, .occ 1525, .occ 1580, .occ 1597, .occ 1602, .occ 1609, .occ 1639, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchGe 41 (1), .branchLe 40 (0), .branchLe 31 (0), .branchGe 14 (1)]

def plane484GenLeaf0249Mult : Fin 44 → Nat := ![4594, 2975, 2162, 7364, 4594, 4501, 5155, 841, 825, 2596, 1078, 3512, 10417, 1588, 2987, 573, 1685, 1619, 5403, 3513, 2258, 2256, 133, 1721, 5437, 1971, 538, 1336, 1864, 2641, 15471, 10733, 16295, 1362, 9843, 4879, 15471, 1062, 33090, 1163, 15014, 9495, 12516, 26378]

theorem plane484GenLeaf0249 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0249Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0249Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0249Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0249Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 179
  · exact hroot.hOcc 366
  · exact hroot.hOcc 526
  · exact hroot.hOcc 542
  · exact hroot.hOcc 655
  · exact hroot.hOcc 749
  · exact hroot.hOcc 858
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
