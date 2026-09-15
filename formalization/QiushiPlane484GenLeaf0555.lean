import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0555Refs : Fin 40 → RowRef 1665 43 := ![.occ 121, .occ 140, .occ 142, .occ 175, .occ 217, .occ 270, .occ 325, .occ 387, .occ 603, .occ 855, .occ 959, .occ 991, .occ 1158, .occ 1242, .occ 1263, .occ 1266, .occ 1271, .occ 1297, .occ 1303, .occ 1311, .occ 1319, .occ 1344, .occ 1349, .occ 1513, .occ 1514, .occ 1544, .occ 1560, .occ 1573, .occ 1646, .occ 1650, .sumGe, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 26 (1), .branchLe 17 (0), .branchLe 42 (0), .branchLe 12 (0), .branchLe 10 (0)]

def plane484GenLeaf0555Mult : Fin 40 → Nat := ![24, 226, 238, 10, 32, 20, 146, 52, 34, 26, 10, 57, 12, 58, 12, 53, 97, 16, 38, 42, 50, 40, 47, 87, 12, 11, 24, 72, 42, 10, 260, 938, 986, 298, 10, 1256, 24, 260, 180, 182]

theorem plane484GenLeaf0555 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0555Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0555Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0555Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0555Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 217
  · exact hroot.hOcc 270
  · exact hroot.hOcc 325
  · exact hroot.hOcc 387
  · exact hroot.hOcc 603
  · exact hroot.hOcc 855
  · exact hroot.hOcc 959
  · exact hroot.hOcc 991
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
