import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0077Refs : Fin 44 → RowRef 1665 43 := ![.occ 126, .occ 129, .occ 131, .occ 134, .occ 137, .occ 141, .occ 409, .occ 608, .occ 713, .occ 715, .occ 823, .occ 861, .occ 1172, .occ 1173, .occ 1284, .occ 1374, .occ 1378, .occ 1379, .occ 1382, .occ 1416, .occ 1418, .occ 1423, .occ 1424, .occ 1429, .occ 1430, .occ 1442, .occ 1451, .occ 1472, .occ 1602, .occ 1607, .occ 1651, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchGe 20 (1), .branchLe 41 (0), .branchLe 37 (0), .branchLe 12 (0)]

def plane484GenLeaf0077Mult : Fin 44 → Nat := ![12724, 16925, 2718, 27677, 16512, 13763, 17996, 10920, 4294, 8032, 8823, 8791, 6748, 3423, 3325, 8153, 11791, 3621, 12, 3039, 10962, 3192, 5800, 4489, 296, 7933, 6005, 17959, 9637, 5247, 16696, 58461, 12662, 10494, 29225, 58461, 19036, 58081, 52001, 44460, 115105, 48290, 48824, 53676]

theorem plane484GenLeaf0077 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0077Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0077Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0077Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0077Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 409
  · exact hroot.hOcc 608
  · exact hroot.hOcc 713
  · exact hroot.hOcc 715
  · exact hroot.hOcc 823
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
