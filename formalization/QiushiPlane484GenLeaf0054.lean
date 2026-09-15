import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0054Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 132, .occ 136, .occ 137, .occ 140, .occ 141, .occ 145, .occ 233, .occ 634, .occ 995, .occ 1013, .occ 1146, .occ 1208, .occ 1238, .occ 1263, .occ 1273, .occ 1307, .occ 1335, .occ 1338, .occ 1406, .occ 1428, .occ 1506, .occ 1509, .occ 1517, .occ 1520, .occ 1545, .occ 1562, .occ 1607, .occ 1617, .occ 1618, .occ 1627, .occ 1628, .sumGe, .nonneg 20, .nonneg 21, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchGe 7 (1), .branchLe 10 (0), .branchGe 26 (1)]

def plane484GenLeaf0054Mult : Fin 44 → Nat := ![1334, 1067, 375, 3193, 2164, 1097, 108, 108, 1016, 286, 158, 108, 108, 1066, 1088, 496, 72, 72, 420, 1378, 692, 488, 1668, 1100, 84, 292, 312, 1536, 514, 466, 584, 598, 4788, 9632, 1004, 1442, 1112, 4292, 2056, 2272, 13310, 6928, 4788, 14032]

theorem plane484GenLeaf0054 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0054Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0054Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0054Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0054Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 233
  · exact hroot.hOcc 634
  · exact hroot.hOcc 995
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1628
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
