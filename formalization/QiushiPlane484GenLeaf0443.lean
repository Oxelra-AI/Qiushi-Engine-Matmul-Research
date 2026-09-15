import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0443Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 131, .occ 133, .occ 138, .occ 172, .occ 313, .occ 322, .occ 1022, .occ 1150, .occ 1187, .occ 1188, .occ 1190, .occ 1200, .occ 1329, .occ 1358, .occ 1371, .occ 1395, .occ 1416, .occ 1432, .occ 1441, .occ 1504, .occ 1522, .occ 1615, .occ 1619, .occ 1621, .occ 1629, .occ 1630, .occ 1631, .occ 1642, .occ 1646, .occ 1651, .occ 1659, .sumGe, .nonneg 23, .nonneg 25, .nonneg 27, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchGe 31 (1), .branchGe 30 (1)]

def plane484GenLeaf0443Mult : Fin 44 → Nat := ![92, 578, 2082, 246, 216, 2422, 412, 194, 276, 522, 66, 276, 1286, 1136, 824, 1184, 368, 386, 118, 218, 54, 450, 636, 418, 521, 325, 632, 382, 943, 843, 577, 25, 4274, 2064, 92, 2210, 8548, 4274, 2428, 1272, 2688, 6586, 7756, 8622]

theorem plane484GenLeaf0443 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0443Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0443Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0443Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0443Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 172
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 1022
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
