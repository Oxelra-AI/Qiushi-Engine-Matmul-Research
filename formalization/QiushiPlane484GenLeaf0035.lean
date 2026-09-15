import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0035Refs : Fin 44 → RowRef 1665 43 := ![.occ 91, .occ 129, .occ 134, .occ 141, .occ 375, .occ 468, .occ 696, .occ 766, .occ 1138, .occ 1145, .occ 1168, .occ 1179, .occ 1213, .occ 1264, .occ 1308, .occ 1333, .occ 1340, .occ 1348, .occ 1357, .occ 1387, .occ 1392, .occ 1459, .occ 1506, .occ 1580, .occ 1608, .occ 1618, .occ 1626, .occ 1627, .occ 1647, .occ 1653, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchLe 16 (0), .branchLe 10 (0), .branchLe 21 (0), .branchLe 28 (0)]

def plane484GenLeaf0035Mult : Fin 44 → Nat := ![3208, 2758, 4456, 742, 8, 1228, 4496, 254, 1054, 11, 211, 536, 1440, 476, 54, 963, 1087, 1237, 1487, 2360, 2282, 2830, 2513, 168, 1748, 3269, 483, 2278, 1655, 44, 11752, 7424, 10086, 11172, 8428, 3886, 758, 9798, 17982, 10086, 2000, 7916, 10182, 8564]

theorem plane484GenLeaf0035 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0035Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0035Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 375
  · exact hroot.hOcc 468
  · exact hroot.hOcc 696
  · exact hroot.hOcc 766
  · exact hroot.hOcc 1138
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
