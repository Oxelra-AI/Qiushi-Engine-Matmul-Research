import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0264Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 128, .occ 132, .occ 135, .occ 136, .occ 141, .occ 579, .occ 670, .occ 1100, .occ 1140, .occ 1151, .occ 1170, .occ 1190, .occ 1248, .occ 1301, .occ 1302, .occ 1471, .occ 1484, .occ 1491, .occ 1495, .occ 1567, .occ 1603, .occ 1619, .occ 1640, .occ 1660, .occ 1661, .sumGe, .nonneg 10, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchGe 0 (1), .branchLe 25 (0), .branchLe 35 (0), .branchLe 33 (0), .branchGe 12 (1)]

def plane484GenLeaf0264Mult : Fin 44 → Nat := ![1467, 1315, 1865, 863, 261, 1391, 102, 1470, 476, 1127, 30, 726, 1030, 1390, 115, 222, 185, 143, 1570, 70, 103, 103, 1565, 247, 319, 398, 230, 4079, 271, 2045, 1284, 1128, 1637, 2119, 3977, 2995, 3681, 539, 1094, 2950, 1936, 1160, 3976, 10104]

theorem plane484GenLeaf0264 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0264Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0264Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0264Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0264Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 579
  · exact hroot.hOcc 670
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1660
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
