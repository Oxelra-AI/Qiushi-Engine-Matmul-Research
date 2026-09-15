import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0435Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 128, .occ 130, .occ 133, .occ 136, .occ 138, .occ 353, .occ 1147, .occ 1150, .occ 1158, .occ 1205, .occ 1250, .occ 1263, .occ 1336, .occ 1338, .occ 1385, .occ 1388, .occ 1390, .occ 1433, .occ 1441, .occ 1521, .occ 1522, .occ 1540, .occ 1556, .occ 1559, .occ 1597, .occ 1629, .occ 1630, .occ 1631, .occ 1638, .occ 1642, .sumGe, .nonneg 23, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchLe 20 (0), .branchLe 38 (0), .branchLe 11 (0)]

def plane484GenLeaf0435Mult : Fin 44 → Nat := ![89457, 14008, 112929, 106016, 278462, 50051, 427305, 28150, 104666, 30885, 97693, 65934, 93271, 48244, 87343, 12793, 80860, 89314, 180080, 78202, 158864, 112727, 15005, 134933, 8217, 108083, 104247, 8327, 2133, 119360, 5137, 31653, 722277, 373016, 490938, 60475, 571264, 518568, 713950, 1145875, 515390, 711927, 722277, 703132]

theorem plane484GenLeaf0435 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0435Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0435Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0435Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0435Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 353
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
