import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0191Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 125, .occ 129, .occ 148, .occ 196, .occ 198, .occ 281, .occ 358, .occ 376, .occ 705, .occ 855, .occ 975, .occ 1143, .occ 1160, .occ 1170, .occ 1236, .occ 1296, .occ 1300, .occ 1326, .occ 1367, .occ 1435, .occ 1439, .occ 1492, .occ 1496, .occ 1505, .occ 1524, .occ 1526, .occ 1542, .occ 1573, .occ 1639, .sumGe, .nonneg 2, .nonneg 11, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchLe 22 (0), .branchGe 30 (1), .branchLe 40 (0), .branchGe 4 (1)]

def plane484GenLeaf0191Mult : Fin 44 → Nat := ![570, 355, 570, 43, 1145, 942, 151, 21, 246, 175, 132, 83, 328, 240, 25, 615, 85, 372, 135, 324, 101, 362, 20, 598, 110, 146, 70, 135, 483, 46, 1405, 425, 50, 1043, 2058, 4098, 674, 793, 1405, 2589, 1405, 2225, 1165, 3604]

theorem plane484GenLeaf0191 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0191Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0191Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0191Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0191Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 148
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 281
  · exact hroot.hOcc 358
  · exact hroot.hOcc 376
  · exact hroot.hOcc 705
  · exact hroot.hOcc 855
  · exact hroot.hOcc 975
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
