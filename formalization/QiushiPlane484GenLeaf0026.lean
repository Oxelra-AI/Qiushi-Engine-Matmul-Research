import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0026Refs : Fin 43 → RowRef 1665 43 := ![.occ 128, .occ 129, .occ 139, .occ 140, .occ 276, .occ 290, .occ 371, .occ 386, .occ 418, .occ 705, .occ 1220, .occ 1257, .occ 1261, .occ 1263, .occ 1266, .occ 1267, .occ 1277, .occ 1279, .occ 1303, .occ 1347, .occ 1357, .occ 1513, .occ 1520, .occ 1534, .occ 1546, .occ 1556, .occ 1597, .occ 1617, .occ 1621, .occ 1624, .occ 1626, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchLe 42 (0), .branchGe 5 (1)]

def plane484GenLeaf0026Mult : Fin 43 → Nat := ![4334, 3353, 2275, 1337, 3620, 3143, 642, 344, 1674, 1276, 608, 3279, 1156, 1310, 2693, 1262, 266, 990, 2148, 300, 2022, 2064, 1577, 3531, 74, 774, 6492, 690, 1335, 112, 3175, 14438, 830, 14094, 14438, 13674, 2828, 9396, 9636, 13748, 7566, 14438, 29826]

theorem plane484GenLeaf0026 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0026Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0026Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 276
  · exact hroot.hOcc 290
  · exact hroot.hOcc 371
  · exact hroot.hOcc 386
  · exact hroot.hOcc 418
  · exact hroot.hOcc 705
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1626
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
