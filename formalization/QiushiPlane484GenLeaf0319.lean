import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0319Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 137, .occ 142, .occ 180, .occ 290, .occ 340, .occ 385, .occ 584, .occ 1146, .occ 1168, .occ 1190, .occ 1233, .occ 1267, .occ 1327, .occ 1328, .occ 1400, .occ 1404, .occ 1470, .occ 1471, .occ 1481, .occ 1483, .occ 1491, .occ 1492, .occ 1496, .occ 1573, .occ 1608, .occ 1615, .occ 1628, .occ 1639, .occ 1662, .sumGe, .nonneg 17, .nonneg 21, .nonneg 23, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchGe 16 (1), .branchLe 34 (0)]

def plane484GenLeaf0319Mult : Fin 44 → Nat := ![34514, 17212, 72047, 65705, 17400, 1146, 3539, 63295, 23185, 32363, 11643, 32642, 5992, 6198, 10484, 438, 1150, 3893, 5131, 9828, 31220, 5616, 763, 6379, 14396, 15577, 5174, 6434, 118, 19083, 1028, 91130, 63862, 130146, 62336, 12347, 208082, 68626, 243165, 16407, 12758, 23959, 236414, 79487]

theorem plane484GenLeaf0319 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0319Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0319Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0319Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0319Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 137
  · exact hroot.hOcc 142
  · exact hroot.hOcc 180
  · exact hroot.hOcc 290
  · exact hroot.hOcc 340
  · exact hroot.hOcc 385
  · exact hroot.hOcc 584
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
