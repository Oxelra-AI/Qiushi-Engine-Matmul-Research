import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0527Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 130, .occ 131, .occ 180, .occ 220, .occ 221, .occ 296, .occ 325, .occ 520, .occ 573, .occ 633, .occ 689, .occ 858, .occ 859, .occ 968, .occ 1191, .occ 1206, .occ 1276, .occ 1278, .occ 1298, .occ 1342, .occ 1350, .occ 1505, .occ 1515, .occ 1516, .occ 1540, .occ 1571, .occ 1590, .occ 1622, .occ 1644, .occ 1645, .sumGe, .nonneg 23, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchGe 9 (1), .branchLe 3 (0), .branchLe 42 (0)]

def plane484GenLeaf0527Mult : Fin 43 → Nat := ![2207, 8898, 8857, 15016, 6341, 6016, 17766, 19622, 5546, 6646, 5926, 1190, 7528, 1570, 1559, 1318, 2624, 9082, 288, 4248, 2940, 1984, 3878, 1766, 7016, 3336, 1668, 3950, 10724, 2624, 2524, 4590, 28704, 2624, 54420, 65638, 6330, 18928, 28704, 52928, 75484, 11174, 28704]

theorem plane484GenLeaf0527 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0527Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0527Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0527Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0527Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 180
  · exact hroot.hOcc 220
  · exact hroot.hOcc 221
  · exact hroot.hOcc 296
  · exact hroot.hOcc 325
  · exact hroot.hOcc 520
  · exact hroot.hOcc 573
  · exact hroot.hOcc 633
  · exact hroot.hOcc 689
  · exact hroot.hOcc 858
  · exact hroot.hOcc 859
  · exact hroot.hOcc 968
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
