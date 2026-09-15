import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0475Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 128, .occ 131, .occ 140, .occ 145, .occ 325, .occ 664, .occ 1024, .occ 1158, .occ 1164, .occ 1172, .occ 1188, .occ 1190, .occ 1205, .occ 1297, .occ 1311, .occ 1339, .occ 1358, .occ 1458, .occ 1470, .occ 1483, .occ 1484, .occ 1524, .occ 1580, .occ 1586, .occ 1590, .occ 1596, .occ 1603, .occ 1609, .occ 1619, .occ 1637, .occ 1651, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchGe 38 (1), .branchLe 34 (0), .branchLe 6 (0), .branchLe 21 (0)]

def plane484GenLeaf0475Mult : Fin 44 → Nat := ![3432, 438, 4700, 3256, 390, 844, 1682, 878, 1801, 212, 472, 1168, 802, 2717, 1046, 828, 816, 3160, 664, 357, 4318, 1694, 1016, 804, 178, 2988, 792, 1348, 445, 2406, 4400, 1032, 13226, 27478, 2696, 9636, 5140, 876, 12562, 6004, 15494, 12058, 5724, 11406]

theorem plane484GenLeaf0475 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0475Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0475Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0475Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0475Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 325
  · exact hroot.hOcc 664
  · exact hroot.hOcc 1024
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1586
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1596
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
