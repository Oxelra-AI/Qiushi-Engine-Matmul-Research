import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0250Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 134, .occ 136, .occ 139, .occ 290, .occ 525, .occ 699, .occ 776, .occ 798, .occ 858, .occ 1143, .occ 1187, .occ 1188, .occ 1190, .occ 1191, .occ 1205, .occ 1206, .occ 1213, .occ 1244, .occ 1267, .occ 1358, .occ 1412, .occ 1470, .occ 1477, .occ 1525, .occ 1526, .occ 1573, .occ 1615, .occ 1634, .occ 1659, .sumGe, .nonneg 15, .nonneg 19, .nonneg 23, .branchGe 2 (1), .branchLe 7 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchGe 41 (1), .branchLe 40 (0), .branchGe 31 (1)]

def plane484GenLeaf0250Mult : Fin 44 → Nat := ![3092, 6820, 3946, 17520, 12770, 6659, 5420, 4560, 810, 9013, 1498, 14843, 1199, 11300, 818, 2659, 2707, 4589, 4041, 5431, 18993, 12696, 3837, 257, 6229, 981, 6135, 4373, 9603, 2253, 38389, 2808, 4332, 1454, 23058, 16090, 2878, 37408, 7356, 87091, 26271, 73803, 22434, 64797]

theorem plane484GenLeaf0250 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0250Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0250Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0250Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0250Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 290
  · exact hroot.hOcc 525
  · exact hroot.hOcc 699
  · exact hroot.hOcc 776
  · exact hroot.hOcc 798
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
