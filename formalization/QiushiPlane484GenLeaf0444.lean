import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0444Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 131, .occ 133, .occ 138, .occ 163, .occ 237, .occ 400, .occ 610, .occ 1143, .occ 1213, .occ 1267, .occ 1275, .occ 1281, .occ 1297, .occ 1331, .occ 1338, .occ 1350, .occ 1386, .occ 1389, .occ 1396, .occ 1399, .occ 1441, .occ 1456, .occ 1483, .occ 1515, .occ 1521, .occ 1531, .occ 1610, .occ 1615, .sumGe, .nonneg 19, .nonneg 20, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 23 (1), .branchLe 10 (0), .branchLe 3 (0), .branchLe 26 (0), .branchLe 30 (0)]

def plane484GenLeaf0444Mult : Fin 43 → Nat := ![2494, 5384, 7652, 9506, 7466, 2180, 5506, 1368, 688, 2384, 5096, 180, 230, 946, 1972, 3453, 3251, 110, 3650, 3201, 3, 3408, 2054, 2602, 1862, 1284, 2966, 1028, 110, 206, 17096, 10708, 494, 19794, 8854, 16068, 9128, 17096, 39326, 6222, 16890, 7658, 17096]

theorem plane484GenLeaf0444 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0444Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0444Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0444Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0444Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 163
  · exact hroot.hOcc 237
  · exact hroot.hOcc 400
  · exact hroot.hOcc 610
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
