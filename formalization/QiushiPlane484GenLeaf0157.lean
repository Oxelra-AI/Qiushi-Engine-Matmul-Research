import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0157Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 128, .occ 129, .occ 130, .occ 131, .occ 134, .occ 142, .occ 179, .occ 411, .occ 707, .occ 727, .occ 729, .occ 777, .occ 778, .occ 780, .occ 791, .occ 1164, .occ 1166, .occ 1216, .occ 1404, .occ 1408, .occ 1471, .occ 1478, .occ 1532, .occ 1601, .occ 1607, .occ 1608, .occ 1610, .occ 1612, .occ 1660, .sumGe, .nonneg 8, .nonneg 11, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchLe 21 (0), .branchGe 42 (1), .branchGe 0 (1)]

def plane484GenLeaf0157Mult : Fin 44 → Nat := ![3921, 1737, 468, 1865, 870, 2344, 360, 416, 1449, 498, 828, 3464, 5374, 3994, 1868, 174, 312, 1564, 1438, 1782, 492, 132, 2226, 756, 312, 1550, 560, 2738, 482, 662, 1158, 6996, 8446, 312, 3078, 6996, 16046, 5680, 15418, 2968, 3698, 6580, 18946, 15182]

theorem plane484GenLeaf0157 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0157Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0157Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0157Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0157Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 179
  · exact hroot.hOcc 411
  · exact hroot.hOcc 707
  · exact hroot.hOcc 727
  · exact hroot.hOcc 729
  · exact hroot.hOcc 777
  · exact hroot.hOcc 778
  · exact hroot.hOcc 780
  · exact hroot.hOcc 791
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1612
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
