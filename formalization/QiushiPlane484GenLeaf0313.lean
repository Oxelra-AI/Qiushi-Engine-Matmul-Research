import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0313Refs : Fin 44 → RowRef 1665 43 := ![.occ 137, .occ 289, .occ 584, .occ 827, .occ 859, .occ 1143, .occ 1145, .occ 1187, .occ 1190, .occ 1196, .occ 1216, .occ 1285, .occ 1351, .occ 1367, .occ 1435, .occ 1452, .occ 1483, .occ 1484, .occ 1489, .occ 1491, .occ 1492, .occ 1500, .occ 1517, .occ 1541, .occ 1551, .occ 1557, .occ 1558, .occ 1573, .occ 1608, .occ 1635, .sumGe, .nonneg 6, .nonneg 20, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchLe 16 (0), .branchLe 0 (0), .branchGe 30 (1)]

def plane484GenLeaf0313Mult : Fin 44 → Nat := ![42666, 1205, 12760, 9244, 43465, 7828, 19558, 2680, 17254, 30527, 12, 15134, 12676, 3185, 223, 11991, 4272, 3568, 7567, 11881, 27065, 17143, 14830, 18477, 2004, 8171, 850, 19726, 9256, 14428, 93436, 21252, 3004, 85596, 160254, 38020, 31044, 88828, 91432, 93436, 76328, 19088, 84168, 126184]

theorem plane484GenLeaf0313 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0313Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0313Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0313Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0313Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 137
  · exact hroot.hOcc 289
  · exact hroot.hOcc 584
  · exact hroot.hOcc 827
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1635
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
