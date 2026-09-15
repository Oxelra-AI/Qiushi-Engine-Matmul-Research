import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0294Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 126, .occ 130, .occ 134, .occ 135, .occ 137, .occ 181, .occ 185, .occ 228, .occ 290, .occ 517, .occ 723, .occ 1102, .occ 1143, .occ 1154, .occ 1200, .occ 1206, .occ 1220, .occ 1243, .occ 1312, .occ 1442, .occ 1478, .occ 1488, .occ 1526, .occ 1567, .occ 1571, .occ 1602, .occ 1639, .occ 1655, .occ 1656, .sumGe, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 32 (0), .branchLe 17 (0), .branchGe 20 (1)]

def plane484GenLeaf0294Mult : Fin 44 → Nat := ![4703, 468, 117, 1976, 2726, 8198, 1433, 1295, 1099, 180, 2621, 1689, 1547, 264, 705, 4252, 388, 486, 4294, 1411, 306, 2212, 4154, 978, 2639, 264, 1947, 2968, 933, 230, 11, 11859, 1450, 2787, 8539, 9531, 2914, 9482, 2743, 8876, 11859, 10387, 8743, 25346]

theorem plane484GenLeaf0294 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0294Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0294Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0294Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0294Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 181
  · exact hroot.hOcc 185
  · exact hroot.hOcc 228
  · exact hroot.hOcc 290
  · exact hroot.hOcc 517
  · exact hroot.hOcc 723
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
