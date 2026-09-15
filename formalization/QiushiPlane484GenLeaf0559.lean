import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0559Refs : Fin 44 → RowRef 1665 43 := ![.occ 131, .occ 138, .occ 139, .occ 142, .occ 380, .occ 386, .occ 387, .occ 591, .occ 713, .occ 736, .occ 749, .occ 779, .occ 954, .occ 1043, .occ 1052, .occ 1158, .occ 1208, .occ 1214, .occ 1221, .occ 1303, .occ 1377, .occ 1392, .occ 1398, .occ 1418, .occ 1426, .occ 1432, .occ 1440, .occ 1470, .occ 1483, .occ 1484, .occ 1496, .occ 1615, .occ 1643, .occ 1650, .sumGe, .nonneg 18, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 26 (1), .branchLe 17 (0), .branchGe 42 (1), .branchGe 16 (1)]

def plane484GenLeaf0559Mult : Fin 44 → Nat := ![463, 266, 774, 553, 91, 310, 174, 1120, 263, 28, 1919, 1735, 248, 464, 111, 468, 49, 489, 18, 443, 275, 255, 823, 32, 29, 464, 349, 464, 262, 230, 852, 575, 139, 283, 2059, 524, 866, 2896, 8487, 1506, 6700, 787, 7071, 5472]

theorem plane484GenLeaf0559 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0559Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0559Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0559Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0559Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 591
  · exact hroot.hOcc 713
  · exact hroot.hOcc 736
  · exact hroot.hOcc 749
  · exact hroot.hOcc 779
  · exact hroot.hOcc 954
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1052
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
