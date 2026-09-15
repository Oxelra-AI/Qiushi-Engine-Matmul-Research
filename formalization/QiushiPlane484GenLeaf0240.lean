import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0240Refs : Fin 44 → RowRef 1665 43 := ![.occ 85, .occ 122, .occ 124, .occ 125, .occ 132, .occ 145, .occ 147, .occ 175, .occ 714, .occ 810, .occ 812, .occ 858, .occ 1143, .occ 1145, .occ 1150, .occ 1186, .occ 1187, .occ 1188, .occ 1200, .occ 1213, .occ 1430, .occ 1437, .occ 1472, .occ 1483, .occ 1573, .occ 1603, .occ 1606, .occ 1615, .occ 1638, .sumGe, .nonneg 14, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchGe 30 (1), .branchLe 6 (0), .branchGe 4 (1)]

def plane484GenLeaf0240Mult : Fin 44 → Nat := ![422, 194, 633, 7, 208, 835, 1092, 981, 140, 536, 244, 564, 80, 712, 820, 392, 516, 536, 412, 536, 88, 332, 304, 136, 296, 48, 136, 68, 244, 2276, 440, 560, 2252, 808, 1012, 1980, 2228, 1824, 1964, 2804, 1712, 1780, 1262, 4798]

theorem plane484GenLeaf0240 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0240Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0240Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0240Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0240Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 175
  · exact hroot.hOcc 714
  · exact hroot.hOcc 810
  · exact hroot.hOcc 812
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
