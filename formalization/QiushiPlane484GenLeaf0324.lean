import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0324Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 128, .occ 137, .occ 140, .occ 141, .occ 228, .occ 536, .occ 585, .occ 605, .occ 959, .occ 1001, .occ 1134, .occ 1147, .occ 1168, .occ 1214, .occ 1254, .occ 1307, .occ 1398, .occ 1477, .occ 1478, .occ 1489, .occ 1496, .occ 1560, .occ 1602, .occ 1618, .occ 1620, .occ 1625, .occ 1645, .sumGe, .nonneg 17, .nonneg 23, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 30 (0), .branchLe 38 (0), .branchLe 16 (0), .branchGe 20 (1)]

def plane484GenLeaf0324Mult : Fin 43 → Nat := ![2038, 4527, 3400, 14276, 14763, 12154, 1226, 1480, 3410, 3234, 2895, 885, 382, 2842, 382, 5438, 624, 6253, 521, 3728, 1365, 4845, 8662, 1246, 1117, 96, 351, 6138, 1117, 20238, 38718, 5924, 2326, 2730, 11886, 18104, 57904, 15370, 15021, 20238, 19856, 5962, 60006]

theorem plane484GenLeaf0324 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0324Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0324Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0324Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0324Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 228
  · exact hroot.hOcc 536
  · exact hroot.hOcc 585
  · exact hroot.hOcc 605
  · exact hroot.hOcc 959
  · exact hroot.hOcc 1001
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
