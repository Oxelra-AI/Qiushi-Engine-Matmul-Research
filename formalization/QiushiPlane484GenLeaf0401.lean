import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0401Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 126, .occ 127, .occ 137, .occ 145, .occ 180, .occ 442, .occ 788, .occ 808, .occ 842, .occ 965, .occ 1136, .occ 1140, .occ 1143, .occ 1145, .occ 1160, .occ 1174, .occ 1196, .occ 1237, .occ 1238, .occ 1239, .occ 1445, .occ 1456, .occ 1486, .occ 1488, .occ 1545, .occ 1571, .occ 1573, .occ 1637, .occ 1653, .sumGe, .nonneg 5, .nonneg 9, .nonneg 10, .nonneg 12, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchLe 0 (0), .branchGe 4 (1)]

def plane484GenLeaf0401Mult : Fin 44 → Nat := ![22312, 4187, 14575, 8974, 14882, 864, 4798, 4117, 474, 7429, 5180, 1389, 1244, 3318, 4413, 610, 4433, 5070, 5092, 3141, 8198, 2549, 1753, 12723, 70, 667, 567, 701, 626, 2060, 22312, 11166, 316, 22547, 56344, 21686, 41513, 95551, 1490, 18470, 14581, 34755, 5431, 70492]

theorem plane484GenLeaf0401 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0401Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0401Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0401Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0401Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 145
  · exact hroot.hOcc 180
  · exact hroot.hOcc 442
  · exact hroot.hOcc 788
  · exact hroot.hOcc 808
  · exact hroot.hOcc 842
  · exact hroot.hOcc 965
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
