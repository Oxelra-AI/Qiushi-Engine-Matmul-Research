import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0400Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 126, .occ 127, .occ 137, .occ 180, .occ 213, .occ 442, .occ 508, .occ 509, .occ 528, .occ 860, .occ 931, .occ 932, .occ 1119, .occ 1124, .occ 1196, .occ 1205, .occ 1206, .occ 1208, .occ 1213, .occ 1483, .occ 1486, .occ 1488, .occ 1489, .occ 1523, .occ 1524, .occ 1531, .occ 1571, .occ 1607, .occ 1640, .sumGe, .nonneg 5, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchLe 0 (0), .branchLe 4 (0), .branchGe 35 (1)]

def plane484GenLeaf0400Mult : Fin 44 → Nat := ![2785, 1084, 7902, 1514, 7282, 1263, 4846, 6286, 112, 2320, 666, 1100, 1100, 714, 7447, 363, 1820, 1710, 662, 3752, 248, 812, 5114, 916, 636, 464, 196, 6, 5920, 4656, 184, 12134, 574, 18804, 8766, 28246, 44160, 1634, 11886, 11950, 18484, 7478, 1726, 25162]

theorem plane484GenLeaf0400 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0400Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0400Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0400Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0400Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 180
  · exact hroot.hOcc 213
  · exact hroot.hOcc 442
  · exact hroot.hOcc 508
  · exact hroot.hOcc 509
  · exact hroot.hOcc 528
  · exact hroot.hOcc 860
  · exact hroot.hOcc 931
  · exact hroot.hOcc 932
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
